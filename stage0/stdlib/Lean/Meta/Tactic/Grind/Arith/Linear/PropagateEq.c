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
lean_object* l_Int_repr(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3_value),LEAN_SCALAR_PTR_LITERAL(206, 233, 164, 186, 216, 210, 242, 163)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(lean_object* v_p_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_583_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_583_ == 0)
{
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_583_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_583_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
if (lean_obj_tag(v_a_459_) == 1)
{
lean_object* v_val_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_578_; 
lean_del_object(v___x_461_);
v_val_463_ = lean_ctor_get(v_a_459_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v_a_459_);
if (v_isSharedCheck_578_ == 0)
{
v___x_465_ = v_a_459_;
v_isShared_466_ = v_isSharedCheck_578_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_val_463_);
lean_dec(v_a_459_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_578_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v_snd_467_; lean_object* v_snd_468_; lean_object* v_fst_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_576_; 
v_snd_467_ = lean_ctor_get(v_val_463_, 1);
lean_inc(v_snd_467_);
v_snd_468_ = lean_ctor_get(v_snd_467_, 1);
lean_inc(v_snd_468_);
v_fst_469_ = lean_ctor_get(v_val_463_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v_val_463_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; 
v_unused_577_ = lean_ctor_get(v_val_463_, 1);
lean_dec(v_unused_577_);
v___x_471_ = v_val_463_;
v_isShared_472_ = v_isSharedCheck_576_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_fst_469_);
lean_dec(v_val_463_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_576_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v_fst_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_574_; 
v_fst_473_ = lean_ctor_get(v_snd_467_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v_snd_467_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; 
v_unused_575_ = lean_ctor_get(v_snd_467_, 1);
lean_dec(v_unused_575_);
v___x_475_ = v_snd_467_;
v_isShared_476_ = v_isSharedCheck_574_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_fst_473_);
lean_dec(v_snd_467_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_574_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v_p_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_573_; 
v_p_477_ = lean_ctor_get(v_snd_468_, 0);
v___x_478_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_479_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_478_, v_a_455_);
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_573_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_573_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_573_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_502_; 
v___x_484_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_477_, v_fst_473_);
lean_inc(v_p_445_);
v___x_485_ = l_Lean_Grind_Linarith_Poly_mul(v_p_445_, v___x_484_);
v___x_486_ = lean_int_neg(v_fst_469_);
lean_inc(v_p_477_);
v___x_487_ = l_Lean_Grind_Linarith_Poly_mul(v_p_477_, v___x_486_);
lean_dec(v___x_486_);
v___x_488_ = l_Lean_Grind_Linarith_Poly_combine(v___x_485_, v___x_487_);
v___x_502_ = lean_unbox(v_a_480_);
lean_dec(v_a_480_);
if (v___x_502_ == 0)
{
lean_dec(v___x_484_);
lean_dec(v_fst_469_);
lean_dec(v_p_445_);
goto v___jp_489_;
}
else
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_p_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
lean_dec(v_p_445_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_505_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref(v___x_503_);
v___x_505_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_473_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_507_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref(v___x_505_);
v___x_507_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_snd_468_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_509_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref(v___x_507_);
v___x_509_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v___x_488_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref(v___x_509_);
v___x_511_ = l_Lean_MessageData_ofExpr(v_a_504_);
v___x_512_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6);
v___x_513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_511_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = l_Int_repr(v_fst_469_);
lean_dec(v_fst_469_);
v___x_515_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
v___x_516_ = l_Lean_MessageData_ofFormat(v___x_515_);
v___x_517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_513_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
lean_ctor_set(v___x_518_, 1, v___x_512_);
v___x_519_ = l_Lean_MessageData_ofExpr(v_a_506_);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
lean_ctor_set(v___x_521_, 1, v___x_512_);
v___x_522_ = l_Lean_MessageData_ofExpr(v_a_508_);
v___x_523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
lean_ctor_set(v___x_524_, 1, v___x_512_);
v___x_525_ = l_Int_repr(v___x_484_);
lean_dec(v___x_484_);
v___x_526_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
v___x_527_ = l_Lean_MessageData_ofFormat(v___x_526_);
v___x_528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_524_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v___x_512_);
v___x_530_ = l_Lean_MessageData_ofExpr(v_a_510_);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_478_, v___x_531_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_dec_ref(v___x_532_);
goto v___jp_489_;
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec(v___x_488_);
lean_del_object(v___x_482_);
lean_del_object(v___x_475_);
lean_dec(v_fst_473_);
lean_del_object(v___x_471_);
lean_dec(v_snd_468_);
lean_del_object(v___x_465_);
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_a_508_);
lean_dec(v_a_506_);
lean_dec(v_a_504_);
lean_dec(v___x_488_);
lean_dec(v___x_484_);
lean_del_object(v___x_482_);
lean_del_object(v___x_475_);
lean_dec(v_fst_473_);
lean_del_object(v___x_471_);
lean_dec(v_fst_469_);
lean_dec(v_snd_468_);
lean_del_object(v___x_465_);
v_a_541_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_509_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_509_);
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
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec(v_a_506_);
lean_dec(v_a_504_);
lean_dec(v___x_488_);
lean_dec(v___x_484_);
lean_del_object(v___x_482_);
lean_del_object(v___x_475_);
lean_dec(v_fst_473_);
lean_del_object(v___x_471_);
lean_dec(v_fst_469_);
lean_dec(v_snd_468_);
lean_del_object(v___x_465_);
v_a_549_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_507_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_507_);
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
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec(v_a_504_);
lean_dec(v___x_488_);
lean_dec(v___x_484_);
lean_del_object(v___x_482_);
lean_del_object(v___x_475_);
lean_dec(v_fst_473_);
lean_del_object(v___x_471_);
lean_dec(v_fst_469_);
lean_dec(v_snd_468_);
lean_del_object(v___x_465_);
v_a_557_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_505_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_505_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_dec(v___x_488_);
lean_dec(v___x_484_);
lean_del_object(v___x_482_);
lean_del_object(v___x_475_);
lean_dec(v_fst_473_);
lean_del_object(v___x_471_);
lean_dec(v_fst_469_);
lean_dec(v_snd_468_);
lean_del_object(v___x_465_);
v_a_565_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_503_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_503_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
v___jp_489_:
{
lean_object* v___x_491_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 1, v___x_488_);
lean_ctor_set(v___x_475_, 0, v_snd_468_);
v___x_491_ = v___x_475_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_snd_468_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v___x_488_);
v___x_491_ = v_reuseFailAlloc_501_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_493_; 
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 1, v___x_491_);
lean_ctor_set(v___x_471_, 0, v_fst_473_);
v___x_493_ = v___x_471_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_fst_473_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v___x_491_);
v___x_493_ = v_reuseFailAlloc_500_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_495_; 
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_493_);
v___x_495_ = v___x_465_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_499_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_497_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_495_);
v___x_497_ = v___x_482_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
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
lean_object* v___x_579_; lean_object* v___x_581_; 
lean_dec(v_a_459_);
lean_dec(v_p_445_);
v___x_579_ = lean_box(0);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_579_);
v___x_581_ = v___x_461_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_dec(v_p_445_);
v_a_584_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_458_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_458_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___boxed(lean_object* v_p_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec(v_a_594_);
lean_dec(v_a_593_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3(lean_object* v_cls_606_, lean_object* v_msg_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_606_, v_msg_607_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___boxed(lean_object* v_cls_621_, lean_object* v_msg_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3(v_cls_621_, v_msg_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec(v___y_624_);
lean_dec(v___y_623_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(lean_object* v_c_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_p_649_; lean_object* v___x_650_; 
v_p_649_ = lean_ctor_get(v_c_636_, 0);
v___x_650_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_p_649_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_652_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref(v___x_650_);
v___x_652_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v_ofNatZero_654_; lean_object* v___x_655_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref(v___x_652_);
v_ofNatZero_654_ = lean_ctor_get(v_a_653_, 18);
lean_inc_ref(v_ofNatZero_654_);
lean_dec(v_a_653_);
v___x_655_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__4(v_a_651_, v_ofNatZero_654_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_664_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_664_ == 0)
{
v___x_658_ = v___x_655_;
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_655_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = l_Lean_mkNot(v_a_656_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_660_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
else
{
return v___x_655_;
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec(v_a_651_);
v_a_665_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_652_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_652_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
else
{
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0___boxed(lean_object* v_c_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v_c_673_);
return v_res_686_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = lean_nat_to_int(v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(lean_object* v_a_693_, lean_object* v_x_694_, lean_object* v_c_u2081_695_, lean_object* v_b_696_, lean_object* v_c_u2082_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v_cls_764_; lean_object* v___x_765_; lean_object* v_a_766_; uint8_t v___x_767_; 
v_cls_764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_765_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v_cls_764_, v_a_707_);
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref(v___x_765_);
v___x_767_ = lean_unbox(v_a_766_);
lean_dec(v_a_766_);
if (v___x_767_ == 0)
{
v___y_711_ = v_a_698_;
v___y_712_ = v_a_699_;
v___y_713_ = v_a_700_;
v___y_714_ = v_a_701_;
v___y_715_ = v_a_702_;
v___y_716_ = v_a_703_;
v___y_717_ = v_a_704_;
v___y_718_ = v_a_705_;
v___y_719_ = v_a_706_;
v___y_720_ = v_a_707_;
v___y_721_ = v_a_708_;
goto v___jp_710_;
}
else
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_694_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_770_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref(v___x_768_);
v___x_770_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_c_u2081_695_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_772_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref(v___x_770_);
v___x_772_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_u2082_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref(v___x_772_);
v___x_774_ = l_Lean_MessageData_ofExpr(v_a_769_);
v___x_775_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6);
v___x_776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = l_Lean_MessageData_ofExpr(v_a_771_);
v___x_778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
lean_ctor_set(v___x_779_, 1, v___x_775_);
v___x_780_ = l_Lean_MessageData_ofExpr(v_a_773_);
v___x_781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_764_, v___x_781_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_dec_ref(v___x_782_);
v___y_711_ = v_a_698_;
v___y_712_ = v_a_699_;
v___y_713_ = v_a_700_;
v___y_714_ = v_a_701_;
v___y_715_ = v_a_702_;
v___y_716_ = v_a_703_;
v___y_717_ = v_a_704_;
v___y_718_ = v_a_705_;
v___y_719_ = v_a_706_;
v___y_720_ = v_a_707_;
v___y_721_ = v_a_708_;
goto v___jp_710_;
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec_ref(v_c_u2082_697_);
lean_dec(v_b_696_);
lean_dec_ref(v_c_u2081_695_);
v_a_783_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_782_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec(v_a_771_);
lean_dec(v_a_769_);
lean_dec_ref(v_c_u2082_697_);
lean_dec(v_b_696_);
lean_dec_ref(v_c_u2081_695_);
v_a_791_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_772_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_772_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec(v_a_769_);
lean_dec_ref(v_c_u2082_697_);
lean_dec(v_b_696_);
lean_dec_ref(v_c_u2081_695_);
v_a_799_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_770_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_770_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref(v_c_u2082_697_);
lean_dec(v_b_696_);
lean_dec_ref(v_c_u2081_695_);
v_a_807_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_768_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_768_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
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
v___jp_710_:
{
lean_object* v_p_722_; lean_object* v_p_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v_p_722_ = lean_ctor_get(v_c_u2081_695_, 0);
v_p_723_ = lean_ctor_get(v_c_u2082_697_, 0);
v___x_724_ = lean_int_emod(v_b_696_, v_a_693_);
v___x_725_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_726_ = lean_int_dec_eq(v___x_724_, v___x_725_);
lean_dec(v___x_724_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_747_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_747_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_747_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_747_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
uint8_t v___x_732_; 
v___x_732_ = lean_unbox(v_a_728_);
lean_dec(v_a_728_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_735_; 
lean_dec_ref(v_c_u2082_697_);
lean_dec(v_b_696_);
lean_dec_ref(v_c_u2081_695_);
v___x_733_ = lean_box(0);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_733_);
v___x_735_ = v___x_730_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_745_; 
lean_inc(v_p_722_);
v___x_737_ = l_Lean_Grind_Linarith_Poly_mul(v_p_722_, v_b_696_);
v___x_738_ = lean_int_neg(v_a_693_);
lean_inc(v_p_723_);
v___x_739_ = l_Lean_Grind_Linarith_Poly_mul(v_p_723_, v___x_738_);
v___x_740_ = l_Lean_Grind_Linarith_Poly_combine(v___x_737_, v___x_739_);
v___x_741_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_741_, 0, v___x_738_);
lean_ctor_set(v___x_741_, 1, v_b_696_);
lean_ctor_set(v___x_741_, 2, v_c_u2081_695_);
lean_ctor_set(v___x_741_, 3, v_c_u2082_697_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_743_);
v___x_745_ = v___x_730_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec_ref(v_c_u2082_697_);
lean_dec(v_b_696_);
lean_dec_ref(v_c_u2081_695_);
v_a_748_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_727_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_727_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_756_ = lean_int_neg(v_b_696_);
lean_dec(v_b_696_);
v___x_757_ = lean_int_ediv(v___x_756_, v_a_693_);
lean_dec(v___x_756_);
lean_inc(v_p_722_);
v___x_758_ = l_Lean_Grind_Linarith_Poly_mul(v_p_722_, v___x_757_);
lean_inc(v_p_723_);
v___x_759_ = l_Lean_Grind_Linarith_Poly_combine(v___x_758_, v_p_723_);
v___x_760_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_760_, 0, v___x_757_);
lean_ctor_set(v___x_760_, 1, v_c_u2081_695_);
lean_ctor_set(v___x_760_, 2, v_c_u2082_697_);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_759_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
v___x_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
return v___x_763_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___boxed(lean_object** _args){
lean_object* v_a_815_ = _args[0];
lean_object* v_x_816_ = _args[1];
lean_object* v_c_u2081_817_ = _args[2];
lean_object* v_b_818_ = _args[3];
lean_object* v_c_u2082_819_ = _args[4];
lean_object* v_a_820_ = _args[5];
lean_object* v_a_821_ = _args[6];
lean_object* v_a_822_ = _args[7];
lean_object* v_a_823_ = _args[8];
lean_object* v_a_824_ = _args[9];
lean_object* v_a_825_ = _args[10];
lean_object* v_a_826_ = _args[11];
lean_object* v_a_827_ = _args[12];
lean_object* v_a_828_ = _args[13];
lean_object* v_a_829_ = _args[14];
lean_object* v_a_830_ = _args[15];
lean_object* v_a_831_ = _args[16];
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_815_, v_x_816_, v_c_u2081_817_, v_b_818_, v_c_u2082_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec(v_a_821_);
lean_dec(v_a_820_);
lean_dec(v_x_816_);
lean_dec(v_a_815_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(lean_object* v_a_833_, lean_object* v_b_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_a_833_, v_a_835_, v_a_836_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_867_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_867_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_867_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_867_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
if (lean_obj_tag(v_a_839_) == 1)
{
lean_object* v_val_843_; lean_object* v___x_844_; 
lean_del_object(v___x_841_);
v_val_843_ = lean_ctor_get(v_a_839_, 0);
v___x_844_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_b_834_, v_a_835_, v_a_836_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_862_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_862_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_862_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_862_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
if (lean_obj_tag(v_a_845_) == 1)
{
lean_object* v_val_849_; uint8_t v___x_850_; 
v_val_849_ = lean_ctor_get(v_a_845_, 0);
lean_inc(v_val_849_);
lean_dec_ref(v_a_845_);
v___x_850_ = lean_nat_dec_eq(v_val_843_, v_val_849_);
lean_dec(v_val_849_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; lean_object* v___x_853_; 
lean_dec_ref(v_a_839_);
v___x_851_ = lean_box(0);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_851_);
v___x_853_ = v___x_847_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
else
{
lean_object* v___x_856_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v_a_839_);
v___x_856_ = v___x_847_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_839_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
else
{
lean_object* v___x_858_; lean_object* v___x_860_; 
lean_dec(v_a_845_);
lean_dec_ref(v_a_839_);
v___x_858_ = lean_box(0);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_858_);
v___x_860_ = v___x_847_;
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
lean_dec_ref(v_a_839_);
return v___x_844_;
}
}
else
{
lean_object* v___x_863_; lean_object* v___x_865_; 
lean_dec(v_a_839_);
v___x_863_ = lean_box(0);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_863_);
v___x_865_ = v___x_841_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
else
{
return v___x_838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg___boxed(lean_object* v_a_868_, lean_object* v_b_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_868_, v_b_869_, v_a_870_, v_a_871_);
lean_dec_ref(v_a_871_);
lean_dec(v_a_870_);
lean_dec_ref(v_b_869_);
lean_dec_ref(v_a_868_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(lean_object* v_a_874_, lean_object* v_b_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_874_, v_b_875_, v_a_876_, v_a_884_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___boxed(lean_object* v_a_888_, lean_object* v_b_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(v_a_888_, v_b_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_b_889_);
lean_dec_ref(v_a_888_);
return v_res_901_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0);
v___x_903_ = lean_int_neg(v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(lean_object* v_a_904_, lean_object* v_b_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
uint8_t v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_918_ = 0;
v___x_919_ = lean_unsigned_to_nat(0u);
v___x_920_ = lean_box(v___x_918_);
lean_inc_ref(v_a_904_);
v___x_921_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_921_, 0, v_a_904_);
lean_closure_set(v___x_921_, 1, v___x_920_);
lean_closure_set(v___x_921_, 2, v___x_919_);
v___x_922_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_921_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_1074_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_1074_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_1074_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
if (lean_obj_tag(v_a_923_) == 1)
{
lean_object* v_val_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
lean_del_object(v___x_925_);
v_val_927_ = lean_ctor_get(v_a_923_, 0);
lean_inc(v_val_927_);
lean_dec_ref(v_a_923_);
v___x_928_ = lean_box(v___x_918_);
lean_inc_ref(v_b_905_);
v___x_929_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_929_, 0, v_b_905_);
lean_closure_set(v___x_929_, 1, v___x_928_);
lean_closure_set(v___x_929_, 2, v___x_919_);
v___x_930_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_929_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_1061_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_1061_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_1061_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
if (lean_obj_tag(v_a_931_) == 1)
{
lean_object* v_val_935_; lean_object* v___x_936_; 
lean_del_object(v___x_933_);
v_val_935_ = lean_ctor_get(v_a_931_, 0);
lean_inc(v_val_935_);
lean_dec_ref(v_a_931_);
v___x_936_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_904_, v_a_907_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_938_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
lean_dec_ref(v___x_936_);
v___x_938_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_905_, v_a_907_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___y_941_; uint8_t v___x_1040_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_939_);
lean_dec_ref(v___x_938_);
v___x_1040_ = lean_nat_dec_le(v_a_937_, v_a_939_);
if (v___x_1040_ == 0)
{
lean_dec(v_a_939_);
v___y_941_ = v_a_937_;
goto v___jp_940_;
}
else
{
lean_dec(v_a_937_);
v___y_941_ = v_a_939_;
goto v___jp_940_;
}
v___jp_940_:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
lean_inc(v_val_935_);
lean_inc(v_val_927_);
v___x_942_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_942_, 0, v_val_927_);
lean_ctor_set(v___x_942_, 1, v_val_935_);
v___x_943_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_942_);
v___x_944_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_944_, 0, v_a_904_);
lean_ctor_set(v___x_944_, 1, v_b_905_);
lean_ctor_set(v___x_944_, 2, v_val_927_);
lean_ctor_set(v___x_944_, 3, v_val_935_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_943_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(v___x_945_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v_p_948_; lean_object* v___x_949_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref(v___x_946_);
v_p_948_ = lean_ctor_get(v_a_947_, 0);
lean_inc(v___y_941_);
lean_inc_ref(v_p_948_);
v___x_949_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_948_, v___y_941_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_951_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref(v___x_949_);
lean_inc(v___y_941_);
v___x_951_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_950_, v___x_918_, v___y_941_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_1015_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_954_ = v___x_951_;
v_isShared_955_ = v_isSharedCheck_1015_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_1015_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
if (lean_obj_tag(v_a_952_) == 1)
{
lean_object* v_val_956_; lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v_val_956_ = lean_ctor_get(v_a_952_, 0);
lean_inc(v_val_956_);
lean_dec_ref(v_a_952_);
lean_inc(v_val_956_);
v___x_957_ = l_Lean_Grind_Linarith_Expr_norm(v_val_956_);
v___x_958_ = lean_box(0);
v___x_959_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_957_, v___x_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
lean_del_object(v___x_954_);
lean_inc(v_a_947_);
v___x_960_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_960_, 0, v_a_947_);
lean_ctor_set(v___x_960_, 1, v_val_956_);
lean_inc(v___x_957_);
v___x_961_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_961_, 0, v___x_957_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
lean_ctor_set_uint8(v___x_961_, sizeof(void*)*2, v___x_918_);
v___x_962_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_961_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1005_; 
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_1005_ == 0)
{
lean_object* v_unused_1006_; 
v_unused_1006_ = lean_ctor_get(v___x_962_, 0);
lean_dec(v_unused_1006_);
v___x_964_ = v___x_962_;
v_isShared_965_ = v_isSharedCheck_1005_;
goto v_resetjp_963_;
}
else
{
lean_dec(v___x_962_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1005_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_966_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_948_);
v___x_967_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_966_, v_p_948_);
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 1);
lean_ctor_set(v___x_964_, 0, v_a_947_);
v___x_969_ = v___x_964_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_947_);
v___x_969_ = v_reuseFailAlloc_1004_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
lean_inc_ref(v___x_967_);
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_967_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
lean_inc(v___y_941_);
v___x_971_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v___x_967_, v___y_941_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref(v___x_971_);
v___x_973_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_972_, v___x_918_, v___y_941_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_987_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_987_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_987_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_987_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
if (lean_obj_tag(v_a_974_) == 1)
{
lean_object* v_val_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
lean_del_object(v___x_976_);
v_val_978_ = lean_ctor_get(v_a_974_, 0);
lean_inc(v_val_978_);
lean_dec_ref(v_a_974_);
v___x_979_ = l_Lean_Grind_Linarith_Poly_mul(v___x_957_, v___x_966_);
v___x_980_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_970_);
lean_ctor_set(v___x_980_, 1, v_val_978_);
v___x_981_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_981_, 0, v___x_979_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
lean_ctor_set_uint8(v___x_981_, sizeof(void*)*2, v___x_918_);
v___x_982_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_981_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
return v___x_982_;
}
else
{
lean_object* v___x_983_; lean_object* v___x_985_; 
lean_dec(v_a_974_);
lean_dec_ref(v___x_970_);
lean_dec(v___x_957_);
v___x_983_ = lean_box(0);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_983_);
v___x_985_ = v___x_976_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
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
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v___x_970_);
lean_dec(v___x_957_);
v_a_988_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_973_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_973_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec_ref(v___x_970_);
lean_dec(v___x_957_);
lean_dec(v___y_941_);
v_a_996_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_971_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_971_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
}
else
{
lean_dec(v___x_957_);
lean_dec(v_a_947_);
lean_dec(v___y_941_);
return v___x_962_;
}
}
else
{
lean_object* v___x_1007_; lean_object* v___x_1009_; 
lean_dec(v___x_957_);
lean_dec(v_val_956_);
lean_dec(v_a_947_);
lean_dec(v___y_941_);
v___x_1007_ = lean_box(0);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_1007_);
v___x_1009_ = v___x_954_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
lean_dec(v_a_952_);
lean_dec(v_a_947_);
lean_dec(v___y_941_);
v___x_1011_ = lean_box(0);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_1011_);
v___x_1013_ = v___x_954_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec(v_a_947_);
lean_dec(v___y_941_);
v_a_1016_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_951_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_951_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v_a_947_);
lean_dec(v___y_941_);
v_a_1024_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_949_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_949_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v___y_941_);
v_a_1032_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_946_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_946_);
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
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec(v_a_937_);
lean_dec(v_val_935_);
lean_dec(v_val_927_);
lean_dec_ref(v_b_905_);
lean_dec_ref(v_a_904_);
v_a_1041_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_938_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_938_);
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
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec(v_val_935_);
lean_dec(v_val_927_);
lean_dec_ref(v_b_905_);
lean_dec_ref(v_a_904_);
v_a_1049_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_936_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_936_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
lean_dec(v_a_931_);
lean_dec(v_val_927_);
lean_dec_ref(v_b_905_);
lean_dec_ref(v_a_904_);
v___x_1057_ = lean_box(0);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_1057_);
v___x_1059_ = v___x_933_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec(v_val_927_);
lean_dec_ref(v_b_905_);
lean_dec_ref(v_a_904_);
v_a_1062_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_930_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_930_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
else
{
lean_object* v___x_1070_; lean_object* v___x_1072_; 
lean_dec(v_a_923_);
lean_dec_ref(v_b_905_);
lean_dec_ref(v_a_904_);
v___x_1070_ = lean_box(0);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_1070_);
v___x_1072_ = v___x_925_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
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
lean_dec_ref(v_b_905_);
lean_dec_ref(v_a_904_);
v_a_1075_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_922_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_922_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___boxed(lean_object* v_a_1083_, lean_object* v_b_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_1083_, v_b_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec(v_a_1085_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(lean_object* v_a_1098_, lean_object* v_b_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1098_, v_a_1101_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; uint8_t v___x_1114_; lean_object* v___x_1115_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref(v___x_1112_);
v___x_1114_ = 0;
lean_inc_ref(v_a_1098_);
v___x_1115_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1098_, v___x_1114_, v_a_1113_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1170_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1170_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1170_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
if (lean_obj_tag(v_a_1116_) == 1)
{
lean_object* v_val_1120_; lean_object* v___x_1121_; 
lean_del_object(v___x_1118_);
v_val_1120_ = lean_ctor_get(v_a_1116_, 0);
lean_inc(v_val_1120_);
lean_dec_ref(v_a_1116_);
v___x_1121_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1099_, v_a_1101_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1123_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref(v___x_1121_);
lean_inc_ref(v_b_1099_);
v___x_1123_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_1099_, v___x_1114_, v_a_1122_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1149_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1126_ = v___x_1123_;
v_isShared_1127_ = v_isSharedCheck_1149_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1123_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1149_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
if (lean_obj_tag(v_a_1124_) == 1)
{
lean_object* v_val_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v_val_1128_ = lean_ctor_get(v_a_1124_, 0);
lean_inc(v_val_1128_);
lean_dec_ref(v_a_1124_);
lean_inc(v_val_1128_);
lean_inc(v_val_1120_);
v___x_1129_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1129_, 0, v_val_1120_);
lean_ctor_set(v___x_1129_, 1, v_val_1128_);
v___x_1130_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1129_);
v___x_1131_ = lean_box(0);
v___x_1132_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_1130_, v___x_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_del_object(v___x_1126_);
lean_inc(v_val_1128_);
lean_inc(v_val_1120_);
lean_inc_ref(v_b_1099_);
lean_inc_ref(v_a_1098_);
v___x_1133_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1133_, 0, v_a_1098_);
lean_ctor_set(v___x_1133_, 1, v_b_1099_);
lean_ctor_set(v___x_1133_, 2, v_val_1120_);
lean_ctor_set(v___x_1133_, 3, v_val_1128_);
lean_inc(v___x_1130_);
v___x_1134_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1134_, 0, v___x_1130_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
lean_ctor_set_uint8(v___x_1134_, sizeof(void*)*2, v___x_1114_);
v___x_1135_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1134_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec_ref(v___x_1135_);
v___x_1136_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_1137_ = l_Lean_Grind_Linarith_Poly_mul(v___x_1130_, v___x_1136_);
v___x_1138_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1138_, 0, v_b_1099_);
lean_ctor_set(v___x_1138_, 1, v_a_1098_);
lean_ctor_set(v___x_1138_, 2, v_val_1128_);
lean_ctor_set(v___x_1138_, 3, v_val_1120_);
v___x_1139_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
lean_ctor_set_uint8(v___x_1139_, sizeof(void*)*2, v___x_1114_);
v___x_1140_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1139_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
return v___x_1140_;
}
else
{
lean_dec(v___x_1130_);
lean_dec(v_val_1128_);
lean_dec(v_val_1120_);
lean_dec_ref(v_b_1099_);
lean_dec_ref(v_a_1098_);
return v___x_1135_;
}
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
lean_dec(v___x_1130_);
lean_dec(v_val_1128_);
lean_dec(v_val_1120_);
lean_dec_ref(v_b_1099_);
lean_dec_ref(v_a_1098_);
v___x_1141_ = lean_box(0);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1141_);
v___x_1143_ = v___x_1126_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
lean_dec(v_a_1124_);
lean_dec(v_val_1120_);
lean_dec_ref(v_b_1099_);
lean_dec_ref(v_a_1098_);
v___x_1145_ = lean_box(0);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1145_);
v___x_1147_ = v___x_1126_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec(v_val_1120_);
lean_dec_ref(v_b_1099_);
lean_dec_ref(v_a_1098_);
v_a_1150_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1123_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1123_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec(v_val_1120_);
lean_dec_ref(v_b_1099_);
lean_dec_ref(v_a_1098_);
v_a_1158_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1121_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1121_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
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
else
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
lean_dec(v_a_1116_);
lean_dec_ref(v_b_1099_);
lean_dec_ref(v_a_1098_);
v___x_1166_ = lean_box(0);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v___x_1166_);
v___x_1168_ = v___x_1118_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref(v_b_1099_);
lean_dec_ref(v_a_1098_);
v_a_1171_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1115_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1115_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec_ref(v_b_1099_);
lean_dec_ref(v_a_1098_);
v_a_1179_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1112_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1112_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27___boxed(lean_object* v_a_1187_, lean_object* v_b_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_1187_, v_b_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec(v_a_1190_);
lean_dec(v_a_1189_);
return v_res_1201_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(lean_object* v_msg_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; lean_object* v___f_1217_; lean_object* v___x_3480__overap_1218_; lean_object* v___x_1219_; 
v___x_1216_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0);
v___f_1217_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1217_, 0, v___x_1216_);
v___x_3480__overap_1218_ = lean_panic_fn(v___f_1217_, v_msg_1203_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
lean_inc(v___y_1212_);
lean_inc_ref(v___y_1211_);
lean_inc(v___y_1210_);
lean_inc_ref(v___y_1209_);
lean_inc(v___y_1208_);
lean_inc_ref(v___y_1207_);
lean_inc(v___y_1206_);
lean_inc(v___y_1205_);
lean_inc(v___y_1204_);
v___x_1219_ = lean_apply_12(v___x_3480__overap_1218_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, lean_box(0));
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___boxed(lean_object* v_msg_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v_msg_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec(v___y_1221_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__1(lean_object* v_a_1234_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_nat_to_int(v_a_1234_);
return v___x_1235_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2));
v___x_1240_ = lean_unsigned_to_nat(42u);
v___x_1241_ = lean_unsigned_to_nat(87u);
v___x_1242_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1));
v___x_1243_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0));
v___x_1244_ = l_mkPanicMessageWithDecl(v___x_1243_, v___x_1242_, v___x_1241_, v___x_1240_, v___x_1239_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(lean_object* v_c_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v_c_1261_; lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v_c_1269_; lean_object* v_p_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; uint8_t v___x_1306_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref(v___x_1266_);
v___x_1306_ = lean_unbox(v_a_1267_);
lean_dec(v_a_1267_);
if (v___x_1306_ == 0)
{
lean_object* v_p_1307_; 
v_p_1307_ = lean_ctor_get(v_c_1245_, 0);
lean_inc(v_p_1307_);
v_c_1269_ = v_c_1245_;
v_p_1270_ = v_p_1307_;
v___y_1271_ = v_a_1246_;
v___y_1272_ = v_a_1247_;
v___y_1273_ = v_a_1248_;
v___y_1274_ = v_a_1249_;
v___y_1275_ = v_a_1250_;
v___y_1276_ = v_a_1251_;
v___y_1277_ = v_a_1252_;
v___y_1278_ = v_a_1253_;
v___y_1279_ = v_a_1254_;
v___y_1280_ = v_a_1255_;
v___y_1281_ = v_a_1256_;
goto v___jp_1268_;
}
else
{
lean_object* v_p_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v_p_1308_ = lean_ctor_get(v_c_1245_, 0);
v___x_1309_ = l_Lean_Grind_Linarith_Poly_gcdCoeffs(v_p_1308_);
v___x_1310_ = lean_unsigned_to_nat(1u);
v___x_1311_ = lean_nat_dec_eq(v___x_1309_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_inc(v___x_1309_);
v___x_1312_ = lean_nat_to_int(v___x_1309_);
lean_inc(v_p_1308_);
v___x_1313_ = l_Lean_Grind_Linarith_Poly_div(v_p_1308_, v___x_1312_);
lean_dec(v___x_1312_);
v___x_1314_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1309_);
lean_ctor_set(v___x_1314_, 1, v_c_1245_);
lean_inc(v___x_1313_);
v___x_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v_c_1269_ = v___x_1315_;
v_p_1270_ = v___x_1313_;
v___y_1271_ = v_a_1246_;
v___y_1272_ = v_a_1247_;
v___y_1273_ = v_a_1248_;
v___y_1274_ = v_a_1249_;
v___y_1275_ = v_a_1250_;
v___y_1276_ = v_a_1251_;
v___y_1277_ = v_a_1252_;
v___y_1278_ = v_a_1253_;
v___y_1279_ = v_a_1254_;
v___y_1280_ = v_a_1255_;
v___y_1281_ = v_a_1256_;
goto v___jp_1268_;
}
else
{
lean_inc(v_p_1308_);
lean_dec(v___x_1309_);
v_c_1269_ = v_c_1245_;
v_p_1270_ = v_p_1308_;
v___y_1271_ = v_a_1246_;
v___y_1272_ = v_a_1247_;
v___y_1273_ = v_a_1248_;
v___y_1274_ = v_a_1249_;
v___y_1275_ = v_a_1250_;
v___y_1276_ = v_a_1251_;
v___y_1277_ = v_a_1252_;
v___y_1278_ = v_a_1253_;
v___y_1279_ = v_a_1254_;
v___y_1280_ = v_a_1255_;
v___y_1281_ = v_a_1256_;
goto v___jp_1268_;
}
}
v___jp_1268_:
{
lean_object* v___x_1282_; 
lean_inc(v_p_1270_);
v___x_1282_ = l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(v_p_1270_);
if (lean_obj_tag(v___x_1282_) == 1)
{
lean_object* v_val_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1303_; 
v_val_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1303_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_val_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1303_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_fst_1287_; lean_object* v_snd_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1302_; 
v_fst_1287_ = lean_ctor_get(v_val_1283_, 0);
v_snd_1288_ = lean_ctor_get(v_val_1283_, 1);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_val_1283_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1290_ = v_val_1283_;
v_isShared_1291_ = v_isSharedCheck_1302_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_snd_1288_);
lean_inc(v_fst_1287_);
lean_dec(v_val_1283_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1302_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_1293_ = lean_int_dec_lt(v_fst_1287_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_del_object(v___x_1290_);
lean_del_object(v___x_1285_);
lean_dec(v_p_1270_);
v___y_1259_ = v_snd_1288_;
v___y_1260_ = v_fst_1287_;
v_c_1261_ = v_c_1269_;
goto v___jp_1258_;
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1297_; 
v___x_1294_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_1295_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1270_, v___x_1294_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set_tag(v___x_1285_, 3);
lean_ctor_set(v___x_1285_, 0, v_c_1269_);
v___x_1297_ = v___x_1285_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_c_1269_);
v___x_1297_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
lean_object* v___x_1299_; 
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 1, v___x_1297_);
lean_ctor_set(v___x_1290_, 0, v___x_1295_);
v___x_1299_ = v___x_1290_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
v___y_1259_ = v_snd_1288_;
v___y_1260_ = v_fst_1287_;
v_c_1261_ = v___x_1299_;
goto v___jp_1258_;
}
}
}
}
}
}
else
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
lean_dec(v___x_1282_);
lean_dec(v_p_1270_);
lean_dec_ref(v_c_1269_);
v___x_1304_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3);
v___x_1305_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v___x_1304_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
return v___x_1305_;
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec_ref(v_c_1245_);
v_a_1316_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1266_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1266_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
v___jp_1258_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1262_ = lean_nat_abs(v___y_1260_);
lean_dec(v___y_1260_);
v___x_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___y_1259_);
lean_ctor_set(v___x_1263_, 1, v_c_1261_);
v___x_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
return v___x_1265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___boxed(lean_object* v_c_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_c_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec(v_a_1327_);
lean_dec(v_a_1326_);
lean_dec(v_a_1325_);
return v_res_1337_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = l_Lean_maxRecDepthErrorMessage;
v___x_1344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
return v___x_1344_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_1346_ = l_Lean_MessageData_ofFormat(v___x_1345_);
return v___x_1346_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_1348_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_1349_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
lean_ctor_set(v___x_1349_, 1, v___x_1347_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_1350_){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1352_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v_ref_1350_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1355_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_1358_, lean_object* v_ref_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1359_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_1373_, lean_object* v_ref_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(v_00_u03b1_1373_, v_ref_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec(v___y_1376_);
lean_dec(v___y_1375_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(lean_object* v_c_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v_fileName_1401_; lean_object* v_fileMap_1402_; lean_object* v_options_1403_; lean_object* v_currRecDepth_1404_; lean_object* v_maxRecDepth_1405_; lean_object* v_ref_1406_; lean_object* v_currNamespace_1407_; lean_object* v_openDecls_1408_; lean_object* v_initHeartbeats_1409_; lean_object* v_maxHeartbeats_1410_; lean_object* v_quotContext_1411_; lean_object* v_currMacroScope_1412_; uint8_t v_diag_1413_; lean_object* v_cancelTk_x3f_1414_; uint8_t v_suppressElabErrors_1415_; lean_object* v_inheritedTraceOptions_1416_; uint8_t v___x_1417_; 
v_fileName_1401_ = lean_ctor_get(v_a_1398_, 0);
lean_inc_ref(v_fileName_1401_);
v_fileMap_1402_ = lean_ctor_get(v_a_1398_, 1);
lean_inc_ref(v_fileMap_1402_);
v_options_1403_ = lean_ctor_get(v_a_1398_, 2);
lean_inc_ref(v_options_1403_);
v_currRecDepth_1404_ = lean_ctor_get(v_a_1398_, 3);
lean_inc(v_currRecDepth_1404_);
v_maxRecDepth_1405_ = lean_ctor_get(v_a_1398_, 4);
lean_inc(v_maxRecDepth_1405_);
v_ref_1406_ = lean_ctor_get(v_a_1398_, 5);
lean_inc(v_ref_1406_);
v_currNamespace_1407_ = lean_ctor_get(v_a_1398_, 6);
lean_inc(v_currNamespace_1407_);
v_openDecls_1408_ = lean_ctor_get(v_a_1398_, 7);
lean_inc(v_openDecls_1408_);
v_initHeartbeats_1409_ = lean_ctor_get(v_a_1398_, 8);
lean_inc(v_initHeartbeats_1409_);
v_maxHeartbeats_1410_ = lean_ctor_get(v_a_1398_, 9);
lean_inc(v_maxHeartbeats_1410_);
v_quotContext_1411_ = lean_ctor_get(v_a_1398_, 10);
lean_inc(v_quotContext_1411_);
v_currMacroScope_1412_ = lean_ctor_get(v_a_1398_, 11);
lean_inc(v_currMacroScope_1412_);
v_diag_1413_ = lean_ctor_get_uint8(v_a_1398_, sizeof(void*)*14);
v_cancelTk_x3f_1414_ = lean_ctor_get(v_a_1398_, 12);
lean_inc(v_cancelTk_x3f_1414_);
v_suppressElabErrors_1415_ = lean_ctor_get_uint8(v_a_1398_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1416_ = lean_ctor_get(v_a_1398_, 13);
lean_inc_ref(v_inheritedTraceOptions_1416_);
lean_dec_ref(v_a_1398_);
v___x_1417_ = lean_nat_dec_eq(v_currRecDepth_1404_, v_maxRecDepth_1405_);
if (v___x_1417_ == 0)
{
lean_object* v_p_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v_p_1418_ = lean_ctor_get(v_c_1388_, 0);
v___x_1419_ = lean_unsigned_to_nat(1u);
v___x_1420_ = lean_nat_add(v_currRecDepth_1404_, v___x_1419_);
lean_dec(v_currRecDepth_1404_);
v___x_1421_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1421_, 0, v_fileName_1401_);
lean_ctor_set(v___x_1421_, 1, v_fileMap_1402_);
lean_ctor_set(v___x_1421_, 2, v_options_1403_);
lean_ctor_set(v___x_1421_, 3, v___x_1420_);
lean_ctor_set(v___x_1421_, 4, v_maxRecDepth_1405_);
lean_ctor_set(v___x_1421_, 5, v_ref_1406_);
lean_ctor_set(v___x_1421_, 6, v_currNamespace_1407_);
lean_ctor_set(v___x_1421_, 7, v_openDecls_1408_);
lean_ctor_set(v___x_1421_, 8, v_initHeartbeats_1409_);
lean_ctor_set(v___x_1421_, 9, v_maxHeartbeats_1410_);
lean_ctor_set(v___x_1421_, 10, v_quotContext_1411_);
lean_ctor_set(v___x_1421_, 11, v_currMacroScope_1412_);
lean_ctor_set(v___x_1421_, 12, v_cancelTk_x3f_1414_);
lean_ctor_set(v___x_1421_, 13, v_inheritedTraceOptions_1416_);
lean_ctor_set_uint8(v___x_1421_, sizeof(void*)*14, v_diag_1413_);
lean_ctor_set_uint8(v___x_1421_, sizeof(void*)*14 + 1, v_suppressElabErrors_1415_);
lean_inc(v_p_1418_);
v___x_1422_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_1418_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v___x_1421_, v_a_1399_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1521_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1521_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1521_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
if (lean_obj_tag(v_a_1423_) == 1)
{
lean_object* v_val_1427_; lean_object* v_snd_1428_; lean_object* v_fst_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1517_; 
lean_del_object(v___x_1425_);
v_val_1427_ = lean_ctor_get(v_a_1423_, 0);
lean_inc(v_val_1427_);
lean_dec_ref(v_a_1423_);
v_snd_1428_ = lean_ctor_get(v_val_1427_, 1);
v_fst_1429_ = lean_ctor_get(v_val_1427_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_val_1427_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1431_ = v_val_1427_;
v_isShared_1432_ = v_isSharedCheck_1517_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_snd_1428_);
lean_inc(v_fst_1429_);
lean_dec(v_val_1427_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1517_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_fst_1433_; lean_object* v_snd_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1516_; 
v_fst_1433_ = lean_ctor_get(v_snd_1428_, 0);
v_snd_1434_ = lean_ctor_get(v_snd_1428_, 1);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_snd_1428_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1436_ = v_snd_1428_;
v_isShared_1437_ = v_isSharedCheck_1516_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_snd_1434_);
lean_inc(v_fst_1433_);
lean_dec(v_snd_1428_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1516_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_1456_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_1455_, v___x_1421_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; uint8_t v___x_1458_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref(v___x_1456_);
v___x_1458_ = lean_unbox(v_a_1457_);
lean_dec(v_a_1457_);
if (v___x_1458_ == 0)
{
lean_del_object(v___x_1431_);
v___y_1439_ = v_a_1389_;
v___y_1440_ = v_a_1390_;
v___y_1441_ = v_a_1391_;
v___y_1442_ = v_a_1392_;
v___y_1443_ = v_a_1393_;
v___y_1444_ = v_a_1394_;
v___y_1445_ = v_a_1395_;
v___y_1446_ = v_a_1396_;
v___y_1447_ = v_a_1397_;
v___y_1448_ = v___x_1421_;
v___y_1449_ = v_a_1399_;
goto v___jp_1438_;
}
else
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_1429_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v___x_1421_, v_a_1399_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1461_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref(v___x_1459_);
v___x_1461_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_c_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v___x_1421_, v_a_1399_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1463_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref(v___x_1461_);
v___x_1463_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_fst_1433_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v___x_1421_, v_a_1399_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1468_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref(v___x_1463_);
v___x_1465_ = l_Lean_MessageData_ofExpr(v_a_1460_);
v___x_1466_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6);
if (v_isShared_1432_ == 0)
{
lean_ctor_set_tag(v___x_1431_, 7);
lean_ctor_set(v___x_1431_, 1, v___x_1466_);
lean_ctor_set(v___x_1431_, 0, v___x_1465_);
v___x_1468_ = v___x_1431_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1465_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1469_ = l_Lean_MessageData_ofExpr(v_a_1462_);
v___x_1470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1468_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
lean_ctor_set(v___x_1471_, 1, v___x_1466_);
v___x_1472_ = l_Lean_MessageData_ofExpr(v_a_1464_);
v___x_1473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1471_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___x_1474_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_1455_, v___x_1473_, v_a_1396_, v_a_1397_, v___x_1421_, v_a_1399_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_dec_ref(v___x_1474_);
v___y_1439_ = v_a_1389_;
v___y_1440_ = v_a_1390_;
v___y_1441_ = v_a_1391_;
v___y_1442_ = v_a_1392_;
v___y_1443_ = v_a_1393_;
v___y_1444_ = v_a_1394_;
v___y_1445_ = v_a_1395_;
v___y_1446_ = v_a_1396_;
v___y_1447_ = v_a_1397_;
v___y_1448_ = v___x_1421_;
v___y_1449_ = v_a_1399_;
goto v___jp_1438_;
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_del_object(v___x_1436_);
lean_dec(v_snd_1434_);
lean_dec(v_fst_1433_);
lean_dec(v_fst_1429_);
lean_dec_ref(v___x_1421_);
lean_dec_ref(v_c_1388_);
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec(v_a_1462_);
lean_dec(v_a_1460_);
lean_del_object(v___x_1436_);
lean_dec(v_snd_1434_);
lean_dec(v_fst_1433_);
lean_del_object(v___x_1431_);
lean_dec(v_fst_1429_);
lean_dec_ref(v___x_1421_);
lean_dec_ref(v_c_1388_);
v_a_1484_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1463_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1463_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec(v_a_1460_);
lean_del_object(v___x_1436_);
lean_dec(v_snd_1434_);
lean_dec(v_fst_1433_);
lean_del_object(v___x_1431_);
lean_dec(v_fst_1429_);
lean_dec_ref(v___x_1421_);
lean_dec_ref(v_c_1388_);
v_a_1492_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1461_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1461_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_del_object(v___x_1436_);
lean_dec(v_snd_1434_);
lean_dec(v_fst_1433_);
lean_del_object(v___x_1431_);
lean_dec(v_fst_1429_);
lean_dec_ref(v___x_1421_);
lean_dec_ref(v_c_1388_);
v_a_1500_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1459_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1459_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_del_object(v___x_1436_);
lean_dec(v_snd_1434_);
lean_dec(v_fst_1433_);
lean_del_object(v___x_1431_);
lean_dec(v_fst_1429_);
lean_dec_ref(v___x_1421_);
lean_dec_ref(v_c_1388_);
v_a_1508_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1456_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1456_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
v___jp_1438_:
{
lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1450_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_1450_, 0, v_fst_1429_);
lean_ctor_set(v___x_1450_, 1, v_fst_1433_);
lean_ctor_set(v___x_1450_, 2, v_c_1388_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v___x_1450_);
lean_ctor_set(v___x_1436_, 0, v_snd_1434_);
v___x_1452_ = v___x_1436_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_snd_1434_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
v_c_1388_ = v___x_1452_;
v_a_1389_ = v___y_1439_;
v_a_1390_ = v___y_1440_;
v_a_1391_ = v___y_1441_;
v_a_1392_ = v___y_1442_;
v_a_1393_ = v___y_1443_;
v_a_1394_ = v___y_1444_;
v_a_1395_ = v___y_1445_;
v_a_1396_ = v___y_1446_;
v_a_1397_ = v___y_1447_;
v_a_1398_ = v___y_1448_;
v_a_1399_ = v___y_1449_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_1519_; 
lean_dec(v_a_1423_);
lean_dec_ref(v___x_1421_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v_c_1388_);
v___x_1519_ = v___x_1425_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_c_1388_);
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
lean_dec_ref(v___x_1421_);
lean_dec_ref(v_c_1388_);
v_a_1522_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1422_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1422_);
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
lean_object* v___x_1530_; 
lean_dec_ref(v_inheritedTraceOptions_1416_);
lean_dec(v_cancelTk_x3f_1414_);
lean_dec(v_currMacroScope_1412_);
lean_dec(v_quotContext_1411_);
lean_dec(v_maxHeartbeats_1410_);
lean_dec(v_initHeartbeats_1409_);
lean_dec(v_openDecls_1408_);
lean_dec(v_currNamespace_1407_);
lean_dec(v_maxRecDepth_1405_);
lean_dec(v_currRecDepth_1404_);
lean_dec_ref(v_options_1403_);
lean_dec_ref(v_fileMap_1402_);
lean_dec_ref(v_fileName_1401_);
lean_dec_ref(v_c_1388_);
v___x_1530_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1406_);
return v___x_1530_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object* v_c_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
lean_dec(v_a_1542_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
lean_dec(v_a_1538_);
lean_dec_ref(v_a_1537_);
lean_dec(v_a_1536_);
lean_dec_ref(v_a_1535_);
lean_dec(v_a_1534_);
lean_dec(v_a_1533_);
lean_dec(v_a_1532_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_ref_1551_; lean_object* v___x_1552_; lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1561_; 
v_ref_1551_ = lean_ctor_get(v___y_1548_, 5);
v___x_1552_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3_spec__6(v_msg_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
lean_inc(v_ref_1551_);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v_ref_1551_);
lean_ctor_set(v___x_1557_, 1, v_a_1553_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set_tag(v___x_1555_, 1);
lean_ctor_set(v___x_1555_, 0, v___x_1557_);
v___x_1559_ = v___x_1555_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
return v_res_1568_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0));
v___x_1571_ = l_Lean_stringToMessageData(v___x_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1596_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1596_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1596_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v_leFn_x3f_1589_; 
v_leFn_x3f_1589_ = lean_ctor_get(v_a_1585_, 20);
lean_inc(v_leFn_x3f_1589_);
lean_dec(v_a_1585_);
if (lean_obj_tag(v_leFn_x3f_1589_) == 1)
{
lean_object* v_val_1590_; lean_object* v___x_1592_; 
v_val_1590_ = lean_ctor_get(v_leFn_x3f_1589_, 0);
lean_inc(v_val_1590_);
lean_dec_ref(v_leFn_x3f_1589_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v_val_1590_);
v___x_1592_ = v___x_1587_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_val_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_dec(v_leFn_x3f_1589_);
lean_del_object(v___x_1587_);
v___x_1594_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1);
v___x_1595_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1594_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
return v___x_1595_;
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
v_a_1597_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1584_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1584_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___boxed(lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec(v___y_1605_);
return v_res_1617_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0));
v___x_1620_ = l_Lean_stringToMessageData(v___x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1645_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1645_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1645_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v_ltFn_x3f_1638_; 
v_ltFn_x3f_1638_ = lean_ctor_get(v_a_1634_, 21);
lean_inc(v_ltFn_x3f_1638_);
lean_dec(v_a_1634_);
if (lean_obj_tag(v_ltFn_x3f_1638_) == 1)
{
lean_object* v_val_1639_; lean_object* v___x_1641_; 
v_val_1639_ = lean_ctor_get(v_ltFn_x3f_1638_, 0);
lean_inc(v_val_1639_);
lean_dec_ref(v_ltFn_x3f_1638_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v_val_1639_);
v___x_1641_ = v___x_1636_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_val_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
else
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_dec(v_ltFn_x3f_1638_);
lean_del_object(v___x_1636_);
v___x_1643_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1);
v___x_1644_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1643_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1644_;
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
v_a_1646_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1633_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1633_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___boxed(lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec(v___y_1654_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(lean_object* v_p_1667_, uint8_t v_strict_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
if (v_strict_1668_ == 0)
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v___x_1683_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref(v___x_1681_);
v___x_1683_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_p_1667_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1685_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref(v___x_1683_);
v___x_1685_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1695_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1688_ = v___x_1685_;
v_isShared_1689_ = v_isSharedCheck_1695_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1685_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1695_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v_ofNatZero_1690_; lean_object* v___x_1691_; lean_object* v___x_1693_; 
v_ofNatZero_1690_ = lean_ctor_get(v_a_1686_, 18);
lean_inc_ref(v_ofNatZero_1690_);
lean_dec(v_a_1686_);
v___x_1691_ = l_Lean_mkAppB(v_a_1682_, v_a_1684_, v_ofNatZero_1690_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___x_1691_);
v___x_1693_ = v___x_1688_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec(v_a_1684_);
lean_dec(v_a_1682_);
v_a_1696_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1685_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1685_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
else
{
lean_dec(v_a_1682_);
return v___x_1683_;
}
}
else
{
return v___x_1681_;
}
}
else
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1706_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_a_1705_);
lean_dec_ref(v___x_1704_);
v___x_1706_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_p_1667_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1708_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref(v___x_1706_);
v___x_1708_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1718_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1711_ = v___x_1708_;
v_isShared_1712_ = v_isSharedCheck_1718_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1718_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v_ofNatZero_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
v_ofNatZero_1713_ = lean_ctor_get(v_a_1709_, 18);
lean_inc_ref(v_ofNatZero_1713_);
lean_dec(v_a_1709_);
v___x_1714_ = l_Lean_mkAppB(v_a_1705_, v_a_1707_, v_ofNatZero_1713_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v___x_1714_);
v___x_1716_ = v___x_1711_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec(v_a_1707_);
lean_dec(v_a_1705_);
v_a_1719_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1708_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1708_);
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
else
{
lean_dec(v_a_1705_);
return v___x_1706_;
}
}
else
{
return v___x_1704_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_p_1727_, lean_object* v_strict_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
uint8_t v_strict_boxed_1741_; lean_object* v_res_1742_; 
v_strict_boxed_1741_ = lean_unbox(v_strict_1728_);
v_res_1742_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1727_, v_strict_boxed_1741_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec(v_p_1727_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(lean_object* v_c_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_p_1756_; uint8_t v_strict_1757_; lean_object* v___x_1758_; 
v_p_1756_ = lean_ctor_get(v_c_1743_, 0);
v_strict_1757_ = lean_ctor_get_uint8(v_c_1743_, sizeof(void*)*2);
v___x_1758_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1756_, v_strict_1757_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0___boxed(lean_object* v_c_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v_c_1759_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object* v_a_1773_, lean_object* v_x_1774_, lean_object* v_c_u2081_1775_, lean_object* v_b_1776_, lean_object* v_c_u2082_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_cls_1790_; lean_object* v___x_1791_; lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1858_; 
v_cls_1790_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_1791_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v_cls_1790_, v_a_1787_);
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1794_ = v___x_1791_;
v_isShared_1795_ = v_isSharedCheck_1858_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1791_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1858_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v_p_1796_; lean_object* v_p_1797_; uint8_t v_strict_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v_p_1803_; uint8_t v___x_1810_; 
v_p_1796_ = lean_ctor_get(v_c_u2081_1775_, 0);
v_p_1797_ = lean_ctor_get(v_c_u2082_1777_, 0);
v_strict_1798_ = lean_ctor_get_uint8(v_c_u2082_1777_, sizeof(void*)*2);
v___x_1799_ = lean_nat_to_int(v_a_1773_);
lean_inc(v_p_1797_);
v___x_1800_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1797_, v___x_1799_);
lean_dec(v___x_1799_);
v___x_1801_ = lean_int_neg(v_b_1776_);
lean_inc(v_p_1796_);
v___x_1802_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1796_, v___x_1801_);
lean_dec(v___x_1801_);
v_p_1803_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1800_, v___x_1802_);
v___x_1810_ = lean_unbox(v_a_1792_);
lean_dec(v_a_1792_);
if (v___x_1810_ == 0)
{
goto v___jp_1804_;
}
else
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1774_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1813_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
lean_dec_ref(v___x_1811_);
v___x_1813_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_c_u2081_1775_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1815_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1814_);
lean_dec_ref(v___x_1813_);
v___x_1815_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_u2082_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_a_1816_);
lean_dec_ref(v___x_1815_);
v___x_1817_ = l_Lean_MessageData_ofExpr(v_a_1812_);
v___x_1818_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6);
v___x_1819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1817_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = l_Lean_MessageData_ofExpr(v_a_1814_);
v___x_1821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1819_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
lean_ctor_set(v___x_1822_, 1, v___x_1818_);
v___x_1823_ = l_Lean_MessageData_ofExpr(v_a_1816_);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1822_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_1790_, v___x_1824_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_dec_ref(v___x_1825_);
goto v___jp_1804_;
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec(v_p_1803_);
lean_del_object(v___x_1794_);
lean_dec_ref(v_c_u2082_1777_);
lean_dec_ref(v_c_u2081_1775_);
lean_dec(v_x_1774_);
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1825_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_dec(v_a_1814_);
lean_dec(v_a_1812_);
lean_dec(v_p_1803_);
lean_del_object(v___x_1794_);
lean_dec_ref(v_c_u2082_1777_);
lean_dec_ref(v_c_u2081_1775_);
lean_dec(v_x_1774_);
v_a_1834_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1815_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1815_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_dec(v_a_1812_);
lean_dec(v_p_1803_);
lean_del_object(v___x_1794_);
lean_dec_ref(v_c_u2082_1777_);
lean_dec_ref(v_c_u2081_1775_);
lean_dec(v_x_1774_);
v_a_1842_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1813_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1813_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_dec(v_p_1803_);
lean_del_object(v___x_1794_);
lean_dec_ref(v_c_u2082_1777_);
lean_dec_ref(v_c_u2081_1775_);
lean_dec(v_x_1774_);
v_a_1850_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1811_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1811_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
v___jp_1804_:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1805_ = lean_alloc_ctor(13, 3, 0);
lean_ctor_set(v___x_1805_, 0, v_x_1774_);
lean_ctor_set(v___x_1805_, 1, v_c_u2081_1775_);
lean_ctor_set(v___x_1805_, 2, v_c_u2082_1777_);
v___x_1806_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1806_, 0, v_p_1803_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
lean_ctor_set_uint8(v___x_1806_, sizeof(void*)*2, v_strict_1798_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1806_);
v___x_1808_ = v___x_1794_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object** _args){
lean_object* v_a_1859_ = _args[0];
lean_object* v_x_1860_ = _args[1];
lean_object* v_c_u2081_1861_ = _args[2];
lean_object* v_b_1862_ = _args[3];
lean_object* v_c_u2082_1863_ = _args[4];
lean_object* v_a_1864_ = _args[5];
lean_object* v_a_1865_ = _args[6];
lean_object* v_a_1866_ = _args[7];
lean_object* v_a_1867_ = _args[8];
lean_object* v_a_1868_ = _args[9];
lean_object* v_a_1869_ = _args[10];
lean_object* v_a_1870_ = _args[11];
lean_object* v_a_1871_ = _args[12];
lean_object* v_a_1872_ = _args[13];
lean_object* v_a_1873_ = _args[14];
lean_object* v_a_1874_ = _args[15];
lean_object* v_a_1875_ = _args[16];
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1859_, v_x_1860_, v_c_u2081_1861_, v_b_1862_, v_c_u2082_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
lean_dec(v_a_1874_);
lean_dec_ref(v_a_1873_);
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1871_);
lean_dec(v_a_1870_);
lean_dec_ref(v_a_1869_);
lean_dec(v_a_1868_);
lean_dec_ref(v_a_1867_);
lean_dec(v_a_1866_);
lean_dec(v_a_1865_);
lean_dec(v_a_1864_);
lean_dec(v_b_1862_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1877_, lean_object* v_msg_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1878_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1892_, lean_object* v_msg_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1892_, v_msg_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec(v___y_1894_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(lean_object* v_a_1915_, lean_object* v_x_1916_, lean_object* v_c_u2081_1917_, lean_object* v_as_1918_, size_t v_sz_1919_, size_t v_i_1920_, lean_object* v_b_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
uint8_t v___x_1934_; 
v___x_1934_ = lean_usize_dec_lt(v_i_1920_, v_sz_1919_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; 
lean_dec_ref(v_c_u2081_1917_);
lean_dec(v_x_1916_);
lean_dec(v_a_1915_);
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v_b_1921_);
return v___x_1935_;
}
else
{
lean_object* v_a_1936_; lean_object* v_fst_1937_; lean_object* v_snd_1938_; lean_object* v___x_1939_; 
lean_dec_ref(v_b_1921_);
v_a_1936_ = lean_array_uget_borrowed(v_as_1918_, v_i_1920_);
v_fst_1937_ = lean_ctor_get(v_a_1936_, 0);
v_snd_1938_ = lean_ctor_get(v_a_1936_, 1);
lean_inc(v_snd_1938_);
lean_inc_ref(v_c_u2081_1917_);
lean_inc(v_x_1916_);
lean_inc(v_a_1915_);
v___x_1939_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1915_, v_x_1916_, v_c_u2081_1917_, v_fst_1937_, v_snd_1938_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1941_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref(v___x_1939_);
v___x_1941_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_a_1940_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v___x_1942_; 
lean_dec_ref(v___x_1941_);
v___x_1942_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1956_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1956_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1956_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
uint8_t v___x_1947_; 
v___x_1947_ = lean_unbox(v_a_1943_);
lean_dec(v_a_1943_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; size_t v___x_1949_; size_t v___x_1950_; 
lean_del_object(v___x_1945_);
v___x_1948_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v___x_1949_ = ((size_t)1ULL);
v___x_1950_ = lean_usize_add(v_i_1920_, v___x_1949_);
v_i_1920_ = v___x_1950_;
v_b_1921_ = v___x_1948_;
goto _start;
}
else
{
lean_object* v___x_1952_; lean_object* v___x_1954_; 
lean_dec_ref(v_c_u2081_1917_);
lean_dec(v_x_1916_);
lean_dec(v_a_1915_);
v___x_1952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1952_);
v___x_1954_ = v___x_1945_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec_ref(v_c_u2081_1917_);
lean_dec(v_x_1916_);
lean_dec(v_a_1915_);
v_a_1957_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1942_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1942_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec_ref(v_c_u2081_1917_);
lean_dec(v_x_1916_);
lean_dec(v_a_1915_);
v_a_1965_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1941_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1941_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec_ref(v_c_u2081_1917_);
lean_dec(v_x_1916_);
lean_dec(v_a_1915_);
v_a_1973_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1939_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1939_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___boxed(lean_object** _args){
lean_object* v_a_1981_ = _args[0];
lean_object* v_x_1982_ = _args[1];
lean_object* v_c_u2081_1983_ = _args[2];
lean_object* v_as_1984_ = _args[3];
lean_object* v_sz_1985_ = _args[4];
lean_object* v_i_1986_ = _args[5];
lean_object* v_b_1987_ = _args[6];
lean_object* v___y_1988_ = _args[7];
lean_object* v___y_1989_ = _args[8];
lean_object* v___y_1990_ = _args[9];
lean_object* v___y_1991_ = _args[10];
lean_object* v___y_1992_ = _args[11];
lean_object* v___y_1993_ = _args[12];
lean_object* v___y_1994_ = _args[13];
lean_object* v___y_1995_ = _args[14];
lean_object* v___y_1996_ = _args[15];
lean_object* v___y_1997_ = _args[16];
lean_object* v___y_1998_ = _args[17];
lean_object* v___y_1999_ = _args[18];
_start:
{
size_t v_sz_boxed_2000_; size_t v_i_boxed_2001_; lean_object* v_res_2002_; 
v_sz_boxed_2000_ = lean_unbox_usize(v_sz_1985_);
lean_dec(v_sz_1985_);
v_i_boxed_2001_ = lean_unbox_usize(v_i_1986_);
lean_dec(v_i_1986_);
v_res_2002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1981_, v_x_1982_, v_c_u2081_1983_, v_as_1984_, v_sz_boxed_2000_, v_i_boxed_2001_, v_b_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v_as_1984_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(lean_object* v_a_2003_, lean_object* v_x_2004_, lean_object* v_c_u2081_2005_, lean_object* v_todo_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; size_t v_sz_2021_; size_t v___x_2022_; lean_object* v___x_2023_; 
v___x_2019_ = lean_box(0);
v___x_2020_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_2021_ = lean_array_size(v_todo_2006_);
v___x_2022_ = ((size_t)0ULL);
v___x_2023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_2003_, v_x_2004_, v_c_u2081_2005_, v_todo_2006_, v_sz_2021_, v___x_2022_, v___x_2020_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2036_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2036_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2036_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v_fst_2028_; 
v_fst_2028_ = lean_ctor_get(v_a_2024_, 0);
lean_inc(v_fst_2028_);
lean_dec(v_a_2024_);
if (lean_obj_tag(v_fst_2028_) == 0)
{
lean_object* v___x_2030_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2019_);
v___x_2030_ = v___x_2026_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2019_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
else
{
lean_object* v_val_2032_; lean_object* v___x_2034_; 
v_val_2032_ = lean_ctor_get(v_fst_2028_, 0);
lean_inc(v_val_2032_);
lean_dec_ref(v_fst_2028_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v_val_2032_);
v___x_2034_ = v___x_2026_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_val_2032_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
v_a_2037_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2023_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2023_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object* v_a_2045_, lean_object* v_x_2046_, lean_object* v_c_u2081_2047_, lean_object* v_todo_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2045_, v_x_2046_, v_c_u2081_2047_, v_todo_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
lean_dec(v_a_2059_);
lean_dec_ref(v_a_2058_);
lean_dec(v_a_2057_);
lean_dec_ref(v_a_2056_);
lean_dec(v_a_2055_);
lean_dec_ref(v_a_2054_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
lean_dec(v_a_2051_);
lean_dec(v_a_2050_);
lean_dec(v_a_2049_);
lean_dec_ref(v_todo_2048_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_2062_, lean_object* v_as_2063_, size_t v_sz_2064_, size_t v_i_2065_, lean_object* v_b_2066_){
_start:
{
uint8_t v___x_2067_; 
v___x_2067_ = lean_usize_dec_lt(v_i_2065_, v_sz_2064_);
if (v___x_2067_ == 0)
{
return v_b_2066_;
}
else
{
lean_object* v_snd_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2101_; 
v_snd_2068_ = lean_ctor_get(v_b_2066_, 1);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_b_2066_);
if (v_isSharedCheck_2101_ == 0)
{
lean_object* v_unused_2102_; 
v_unused_2102_ = lean_ctor_get(v_b_2066_, 0);
lean_dec(v_unused_2102_);
v___x_2070_ = v_b_2066_;
v_isShared_2071_ = v_isSharedCheck_2101_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_snd_2068_);
lean_dec(v_b_2066_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2101_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v_fst_2072_; lean_object* v_snd_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2100_; 
v_fst_2072_ = lean_ctor_get(v_snd_2068_, 0);
v_snd_2073_ = lean_ctor_get(v_snd_2068_, 1);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_snd_2068_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2075_ = v_snd_2068_;
v_isShared_2076_ = v_isSharedCheck_2100_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_snd_2073_);
lean_inc(v_fst_2072_);
lean_dec(v_snd_2068_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2100_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v_a_2077_; lean_object* v_p_2078_; lean_object* v___x_2079_; lean_object* v_a_2081_; lean_object* v_b_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v_a_2077_ = lean_array_uget_borrowed(v_as_2063_, v_i_2065_);
v_p_2078_ = lean_ctor_get(v_a_2077_, 0);
v___x_2079_ = lean_box(0);
v_b_2088_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2078_, v_x_2062_);
v___x_2089_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2090_ = lean_int_dec_eq(v_b_2088_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2092_; 
lean_inc(v_a_2077_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 1, v_a_2077_);
lean_ctor_set(v___x_2070_, 0, v_b_2088_);
v___x_2092_ = v___x_2070_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_b_2088_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_a_2077_);
v___x_2092_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v_todo_2093_; lean_object* v___x_2094_; 
v_todo_2093_ = lean_array_push(v_snd_2073_, v___x_2092_);
v___x_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2094_, 0, v_fst_2072_);
lean_ctor_set(v___x_2094_, 1, v_todo_2093_);
v_a_2081_ = v___x_2094_;
goto v___jp_2080_;
}
}
else
{
lean_object* v_cs_x27_2096_; lean_object* v___x_2098_; 
lean_dec(v_b_2088_);
lean_inc(v_a_2077_);
v_cs_x27_2096_ = l_Lean_PersistentArray_push___redArg(v_fst_2072_, v_a_2077_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 1, v_snd_2073_);
lean_ctor_set(v___x_2070_, 0, v_cs_x27_2096_);
v___x_2098_ = v___x_2070_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_cs_x27_2096_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v_snd_2073_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
v_a_2081_ = v___x_2098_;
goto v___jp_2080_;
}
}
v___jp_2080_:
{
lean_object* v___x_2083_; 
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 1, v_a_2081_);
lean_ctor_set(v___x_2075_, 0, v___x_2079_);
v___x_2083_ = v___x_2075_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2079_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_a_2081_);
v___x_2083_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
size_t v___x_2084_; size_t v___x_2085_; 
v___x_2084_ = ((size_t)1ULL);
v___x_2085_ = lean_usize_add(v_i_2065_, v___x_2084_);
v_i_2065_ = v___x_2085_;
v_b_2066_ = v___x_2083_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_2103_, lean_object* v_as_2104_, lean_object* v_sz_2105_, lean_object* v_i_2106_, lean_object* v_b_2107_){
_start:
{
size_t v_sz_boxed_2108_; size_t v_i_boxed_2109_; lean_object* v_res_2110_; 
v_sz_boxed_2108_ = lean_unbox_usize(v_sz_2105_);
lean_dec(v_sz_2105_);
v_i_boxed_2109_ = lean_unbox_usize(v_i_2106_);
lean_dec(v_i_2106_);
v_res_2110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2103_, v_as_2104_, v_sz_boxed_2108_, v_i_boxed_2109_, v_b_2107_);
lean_dec_ref(v_as_2104_);
lean_dec(v_x_2103_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(lean_object* v_x_2111_, lean_object* v_as_2112_, size_t v_sz_2113_, size_t v_i_2114_, lean_object* v_b_2115_){
_start:
{
uint8_t v___x_2116_; 
v___x_2116_ = lean_usize_dec_lt(v_i_2114_, v_sz_2113_);
if (v___x_2116_ == 0)
{
return v_b_2115_;
}
else
{
lean_object* v_snd_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2150_; 
v_snd_2117_ = lean_ctor_get(v_b_2115_, 1);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_b_2115_);
if (v_isSharedCheck_2150_ == 0)
{
lean_object* v_unused_2151_; 
v_unused_2151_ = lean_ctor_get(v_b_2115_, 0);
lean_dec(v_unused_2151_);
v___x_2119_ = v_b_2115_;
v_isShared_2120_ = v_isSharedCheck_2150_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_snd_2117_);
lean_dec(v_b_2115_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2150_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v_fst_2121_; lean_object* v_snd_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2149_; 
v_fst_2121_ = lean_ctor_get(v_snd_2117_, 0);
v_snd_2122_ = lean_ctor_get(v_snd_2117_, 1);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_snd_2117_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2124_ = v_snd_2117_;
v_isShared_2125_ = v_isSharedCheck_2149_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_snd_2122_);
lean_inc(v_fst_2121_);
lean_dec(v_snd_2117_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2149_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v_a_2126_; lean_object* v_p_2127_; lean_object* v___x_2128_; lean_object* v_a_2130_; lean_object* v_b_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v_a_2126_ = lean_array_uget_borrowed(v_as_2112_, v_i_2114_);
v_p_2127_ = lean_ctor_get(v_a_2126_, 0);
v___x_2128_ = lean_box(0);
v_b_2137_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2127_, v_x_2111_);
v___x_2138_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2139_ = lean_int_dec_eq(v_b_2137_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2141_; 
lean_inc(v_a_2126_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 1, v_a_2126_);
lean_ctor_set(v___x_2119_, 0, v_b_2137_);
v___x_2141_ = v___x_2119_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_b_2137_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_a_2126_);
v___x_2141_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v_todo_2142_; lean_object* v___x_2143_; 
v_todo_2142_ = lean_array_push(v_snd_2122_, v___x_2141_);
v___x_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2143_, 0, v_fst_2121_);
lean_ctor_set(v___x_2143_, 1, v_todo_2142_);
v_a_2130_ = v___x_2143_;
goto v___jp_2129_;
}
}
else
{
lean_object* v_cs_x27_2145_; lean_object* v___x_2147_; 
lean_dec(v_b_2137_);
lean_inc(v_a_2126_);
v_cs_x27_2145_ = l_Lean_PersistentArray_push___redArg(v_fst_2121_, v_a_2126_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 1, v_snd_2122_);
lean_ctor_set(v___x_2119_, 0, v_cs_x27_2145_);
v___x_2147_ = v___x_2119_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_cs_x27_2145_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_snd_2122_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
v_a_2130_ = v___x_2147_;
goto v___jp_2129_;
}
}
v___jp_2129_:
{
lean_object* v___x_2132_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 1, v_a_2130_);
lean_ctor_set(v___x_2124_, 0, v___x_2128_);
v___x_2132_ = v___x_2124_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_a_2130_);
v___x_2132_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
size_t v___x_2133_; size_t v___x_2134_; lean_object* v___x_2135_; 
v___x_2133_ = ((size_t)1ULL);
v___x_2134_ = lean_usize_add(v_i_2114_, v___x_2133_);
v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2111_, v_as_2112_, v_sz_2113_, v___x_2134_, v___x_2132_);
return v___x_2135_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2152_, lean_object* v_as_2153_, lean_object* v_sz_2154_, lean_object* v_i_2155_, lean_object* v_b_2156_){
_start:
{
size_t v_sz_boxed_2157_; size_t v_i_boxed_2158_; lean_object* v_res_2159_; 
v_sz_boxed_2157_ = lean_unbox_usize(v_sz_2154_);
lean_dec(v_sz_2154_);
v_i_boxed_2158_ = lean_unbox_usize(v_i_2155_);
lean_dec(v_i_2155_);
v_res_2159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2152_, v_as_2153_, v_sz_boxed_2157_, v_i_boxed_2158_, v_b_2156_);
lean_dec_ref(v_as_2153_);
lean_dec(v_x_2152_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_2160_, lean_object* v_as_2161_, size_t v_sz_2162_, size_t v_i_2163_, lean_object* v_b_2164_){
_start:
{
uint8_t v___x_2165_; 
v___x_2165_ = lean_usize_dec_lt(v_i_2163_, v_sz_2162_);
if (v___x_2165_ == 0)
{
return v_b_2164_;
}
else
{
lean_object* v_snd_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2199_; 
v_snd_2166_ = lean_ctor_get(v_b_2164_, 1);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_b_2164_);
if (v_isSharedCheck_2199_ == 0)
{
lean_object* v_unused_2200_; 
v_unused_2200_ = lean_ctor_get(v_b_2164_, 0);
lean_dec(v_unused_2200_);
v___x_2168_ = v_b_2164_;
v_isShared_2169_ = v_isSharedCheck_2199_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_snd_2166_);
lean_dec(v_b_2164_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2199_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v_fst_2170_; lean_object* v_snd_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2198_; 
v_fst_2170_ = lean_ctor_get(v_snd_2166_, 0);
v_snd_2171_ = lean_ctor_get(v_snd_2166_, 1);
v_isSharedCheck_2198_ = !lean_is_exclusive(v_snd_2166_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2173_ = v_snd_2166_;
v_isShared_2174_ = v_isSharedCheck_2198_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_snd_2171_);
lean_inc(v_fst_2170_);
lean_dec(v_snd_2166_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2198_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v_a_2175_; lean_object* v_p_2176_; lean_object* v___x_2177_; lean_object* v_a_2179_; lean_object* v_b_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; 
v_a_2175_ = lean_array_uget_borrowed(v_as_2161_, v_i_2163_);
v_p_2176_ = lean_ctor_get(v_a_2175_, 0);
v___x_2177_ = lean_box(0);
v_b_2186_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2176_, v_x_2160_);
v___x_2187_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2188_ = lean_int_dec_eq(v_b_2186_, v___x_2187_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2190_; 
lean_inc(v_a_2175_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 1, v_a_2175_);
lean_ctor_set(v___x_2168_, 0, v_b_2186_);
v___x_2190_ = v___x_2168_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_b_2186_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_a_2175_);
v___x_2190_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
lean_object* v_todo_2191_; lean_object* v___x_2192_; 
v_todo_2191_ = lean_array_push(v_snd_2171_, v___x_2190_);
v___x_2192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2192_, 0, v_fst_2170_);
lean_ctor_set(v___x_2192_, 1, v_todo_2191_);
v_a_2179_ = v___x_2192_;
goto v___jp_2178_;
}
}
else
{
lean_object* v_cs_x27_2194_; lean_object* v___x_2196_; 
lean_dec(v_b_2186_);
lean_inc(v_a_2175_);
v_cs_x27_2194_ = l_Lean_PersistentArray_push___redArg(v_fst_2170_, v_a_2175_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 1, v_snd_2171_);
lean_ctor_set(v___x_2168_, 0, v_cs_x27_2194_);
v___x_2196_ = v___x_2168_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_cs_x27_2194_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_snd_2171_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
v_a_2179_ = v___x_2196_;
goto v___jp_2178_;
}
}
v___jp_2178_:
{
lean_object* v___x_2181_; 
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 1, v_a_2179_);
lean_ctor_set(v___x_2173_, 0, v___x_2177_);
v___x_2181_ = v___x_2173_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2177_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_a_2179_);
v___x_2181_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
size_t v___x_2182_; size_t v___x_2183_; 
v___x_2182_ = ((size_t)1ULL);
v___x_2183_ = lean_usize_add(v_i_2163_, v___x_2182_);
v_i_2163_ = v___x_2183_;
v_b_2164_ = v___x_2181_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_2201_, lean_object* v_as_2202_, lean_object* v_sz_2203_, lean_object* v_i_2204_, lean_object* v_b_2205_){
_start:
{
size_t v_sz_boxed_2206_; size_t v_i_boxed_2207_; lean_object* v_res_2208_; 
v_sz_boxed_2206_ = lean_unbox_usize(v_sz_2203_);
lean_dec(v_sz_2203_);
v_i_boxed_2207_ = lean_unbox_usize(v_i_2204_);
lean_dec(v_i_2204_);
v_res_2208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2201_, v_as_2202_, v_sz_boxed_2206_, v_i_boxed_2207_, v_b_2205_);
lean_dec_ref(v_as_2202_);
lean_dec(v_x_2201_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2209_, lean_object* v_as_2210_, size_t v_sz_2211_, size_t v_i_2212_, lean_object* v_b_2213_){
_start:
{
uint8_t v___x_2214_; 
v___x_2214_ = lean_usize_dec_lt(v_i_2212_, v_sz_2211_);
if (v___x_2214_ == 0)
{
return v_b_2213_;
}
else
{
lean_object* v_snd_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2248_; 
v_snd_2215_ = lean_ctor_get(v_b_2213_, 1);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_b_2213_);
if (v_isSharedCheck_2248_ == 0)
{
lean_object* v_unused_2249_; 
v_unused_2249_ = lean_ctor_get(v_b_2213_, 0);
lean_dec(v_unused_2249_);
v___x_2217_ = v_b_2213_;
v_isShared_2218_ = v_isSharedCheck_2248_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_snd_2215_);
lean_dec(v_b_2213_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2248_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v_fst_2219_; lean_object* v_snd_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2247_; 
v_fst_2219_ = lean_ctor_get(v_snd_2215_, 0);
v_snd_2220_ = lean_ctor_get(v_snd_2215_, 1);
v_isSharedCheck_2247_ = !lean_is_exclusive(v_snd_2215_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2222_ = v_snd_2215_;
v_isShared_2223_ = v_isSharedCheck_2247_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_snd_2220_);
lean_inc(v_fst_2219_);
lean_dec(v_snd_2215_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2247_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v_a_2224_; lean_object* v_p_2225_; lean_object* v___x_2226_; lean_object* v_a_2228_; lean_object* v_b_2235_; lean_object* v___x_2236_; uint8_t v___x_2237_; 
v_a_2224_ = lean_array_uget_borrowed(v_as_2210_, v_i_2212_);
v_p_2225_ = lean_ctor_get(v_a_2224_, 0);
v___x_2226_ = lean_box(0);
v_b_2235_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2225_, v_x_2209_);
v___x_2236_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2237_ = lean_int_dec_eq(v_b_2235_, v___x_2236_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2239_; 
lean_inc(v_a_2224_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 1, v_a_2224_);
lean_ctor_set(v___x_2217_, 0, v_b_2235_);
v___x_2239_ = v___x_2217_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_b_2235_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v_a_2224_);
v___x_2239_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v_todo_2240_; lean_object* v___x_2241_; 
v_todo_2240_ = lean_array_push(v_snd_2220_, v___x_2239_);
v___x_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2241_, 0, v_fst_2219_);
lean_ctor_set(v___x_2241_, 1, v_todo_2240_);
v_a_2228_ = v___x_2241_;
goto v___jp_2227_;
}
}
else
{
lean_object* v_cs_x27_2243_; lean_object* v___x_2245_; 
lean_dec(v_b_2235_);
lean_inc(v_a_2224_);
v_cs_x27_2243_ = l_Lean_PersistentArray_push___redArg(v_fst_2219_, v_a_2224_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 1, v_snd_2220_);
lean_ctor_set(v___x_2217_, 0, v_cs_x27_2243_);
v___x_2245_ = v___x_2217_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_cs_x27_2243_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v_snd_2220_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
v_a_2228_ = v___x_2245_;
goto v___jp_2227_;
}
}
v___jp_2227_:
{
lean_object* v___x_2230_; 
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 1, v_a_2228_);
lean_ctor_set(v___x_2222_, 0, v___x_2226_);
v___x_2230_ = v___x_2222_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2226_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_a_2228_);
v___x_2230_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
size_t v___x_2231_; size_t v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = ((size_t)1ULL);
v___x_2232_ = lean_usize_add(v_i_2212_, v___x_2231_);
v___x_2233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2209_, v_as_2210_, v_sz_2211_, v___x_2232_, v___x_2230_);
return v___x_2233_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_2250_, lean_object* v_as_2251_, lean_object* v_sz_2252_, lean_object* v_i_2253_, lean_object* v_b_2254_){
_start:
{
size_t v_sz_boxed_2255_; size_t v_i_boxed_2256_; lean_object* v_res_2257_; 
v_sz_boxed_2255_ = lean_unbox_usize(v_sz_2252_);
lean_dec(v_sz_2252_);
v_i_boxed_2256_ = lean_unbox_usize(v_i_2253_);
lean_dec(v_i_2253_);
v_res_2257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2250_, v_as_2251_, v_sz_boxed_2255_, v_i_boxed_2256_, v_b_2254_);
lean_dec_ref(v_as_2251_);
lean_dec(v_x_2250_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(lean_object* v_x_2258_, lean_object* v_inh_2259_, lean_object* v_n_2260_, lean_object* v_b_2261_){
_start:
{
if (lean_obj_tag(v_n_2260_) == 0)
{
lean_object* v_cs_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2277_; 
v_cs_2262_ = lean_ctor_get(v_n_2260_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v_n_2260_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2264_ = v_n_2260_;
v_isShared_2265_ = v_isSharedCheck_2277_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_cs_2262_);
lean_dec(v_n_2260_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2277_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; size_t v_sz_2268_; size_t v___x_2269_; lean_object* v___x_2270_; lean_object* v_fst_2271_; 
v___x_2266_ = lean_box(0);
v___x_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
lean_ctor_set(v___x_2267_, 1, v_b_2261_);
v_sz_2268_ = lean_array_size(v_cs_2262_);
v___x_2269_ = ((size_t)0ULL);
v___x_2270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_x_2258_, v_inh_2259_, v_cs_2262_, v_sz_2268_, v___x_2269_, v___x_2267_);
lean_dec_ref(v_cs_2262_);
v_fst_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_fst_2271_);
if (lean_obj_tag(v_fst_2271_) == 0)
{
lean_object* v_snd_2272_; lean_object* v___x_2274_; 
v_snd_2272_ = lean_ctor_get(v___x_2270_, 1);
lean_inc(v_snd_2272_);
lean_dec_ref(v___x_2270_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set_tag(v___x_2264_, 1);
lean_ctor_set(v___x_2264_, 0, v_snd_2272_);
v___x_2274_ = v___x_2264_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_snd_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
else
{
lean_object* v_val_2276_; 
lean_dec_ref(v___x_2270_);
lean_del_object(v___x_2264_);
v_val_2276_ = lean_ctor_get(v_fst_2271_, 0);
lean_inc(v_val_2276_);
lean_dec_ref(v_fst_2271_);
return v_val_2276_;
}
}
}
else
{
lean_object* v_vs_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2293_; 
v_vs_2278_ = lean_ctor_get(v_n_2260_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_n_2260_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2280_ = v_n_2260_;
v_isShared_2281_ = v_isSharedCheck_2293_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_vs_2278_);
lean_dec(v_n_2260_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2293_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; size_t v_sz_2284_; size_t v___x_2285_; lean_object* v___x_2286_; lean_object* v_fst_2287_; 
v___x_2282_ = lean_box(0);
v___x_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
lean_ctor_set(v___x_2283_, 1, v_b_2261_);
v_sz_2284_ = lean_array_size(v_vs_2278_);
v___x_2285_ = ((size_t)0ULL);
v___x_2286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2258_, v_vs_2278_, v_sz_2284_, v___x_2285_, v___x_2283_);
lean_dec_ref(v_vs_2278_);
v_fst_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_fst_2287_);
if (lean_obj_tag(v_fst_2287_) == 0)
{
lean_object* v_snd_2288_; lean_object* v___x_2290_; 
v_snd_2288_ = lean_ctor_get(v___x_2286_, 1);
lean_inc(v_snd_2288_);
lean_dec_ref(v___x_2286_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v_snd_2288_);
v___x_2290_ = v___x_2280_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_snd_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
else
{
lean_object* v_val_2292_; 
lean_dec_ref(v___x_2286_);
lean_del_object(v___x_2280_);
v_val_2292_ = lean_ctor_get(v_fst_2287_, 0);
lean_inc(v_val_2292_);
lean_dec_ref(v_fst_2287_);
return v_val_2292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2294_, lean_object* v_inh_2295_, lean_object* v_as_2296_, size_t v_sz_2297_, size_t v_i_2298_, lean_object* v_b_2299_){
_start:
{
uint8_t v___x_2300_; 
v___x_2300_ = lean_usize_dec_lt(v_i_2298_, v_sz_2297_);
if (v___x_2300_ == 0)
{
return v_b_2299_;
}
else
{
lean_object* v_snd_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2319_; 
v_snd_2301_ = lean_ctor_get(v_b_2299_, 1);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_b_2299_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; 
v_unused_2320_ = lean_ctor_get(v_b_2299_, 0);
lean_dec(v_unused_2320_);
v___x_2303_ = v_b_2299_;
v_isShared_2304_ = v_isSharedCheck_2319_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_snd_2301_);
lean_dec(v_b_2299_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2319_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v_a_2305_; lean_object* v___x_2306_; 
v_a_2305_ = lean_array_uget_borrowed(v_as_2296_, v_i_2298_);
lean_inc(v_snd_2301_);
lean_inc(v_a_2305_);
v___x_2306_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_x_2294_, v_inh_2295_, v_a_2305_, v_snd_2301_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v___x_2307_; lean_object* v___x_2309_; 
v___x_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2307_);
v___x_2309_ = v___x_2303_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v_snd_2301_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2312_; lean_object* v___x_2314_; 
lean_dec(v_snd_2301_);
v_a_2311_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2311_);
lean_dec_ref(v___x_2306_);
v___x_2312_ = lean_box(0);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 1, v_a_2311_);
lean_ctor_set(v___x_2303_, 0, v___x_2312_);
v___x_2314_ = v___x_2303_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2312_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_a_2311_);
v___x_2314_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
size_t v___x_2315_; size_t v___x_2316_; 
v___x_2315_ = ((size_t)1ULL);
v___x_2316_ = lean_usize_add(v_i_2298_, v___x_2315_);
v_i_2298_ = v___x_2316_;
v_b_2299_ = v___x_2314_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_x_2321_, lean_object* v_inh_2322_, lean_object* v_as_2323_, lean_object* v_sz_2324_, lean_object* v_i_2325_, lean_object* v_b_2326_){
_start:
{
size_t v_sz_boxed_2327_; size_t v_i_boxed_2328_; lean_object* v_res_2329_; 
v_sz_boxed_2327_ = lean_unbox_usize(v_sz_2324_);
lean_dec(v_sz_2324_);
v_i_boxed_2328_ = lean_unbox_usize(v_i_2325_);
lean_dec(v_i_2325_);
v_res_2329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_x_2321_, v_inh_2322_, v_as_2323_, v_sz_boxed_2327_, v_i_boxed_2328_, v_b_2326_);
lean_dec_ref(v_as_2323_);
lean_dec_ref(v_inh_2322_);
lean_dec(v_x_2321_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object* v_x_2330_, lean_object* v_inh_2331_, lean_object* v_n_2332_, lean_object* v_b_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_x_2330_, v_inh_2331_, v_n_2332_, v_b_2333_);
lean_dec_ref(v_inh_2331_);
lean_dec(v_x_2330_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(lean_object* v_x_2335_, lean_object* v_t_2336_, lean_object* v_init_2337_){
_start:
{
lean_object* v_root_2338_; lean_object* v_tail_2339_; lean_object* v___x_2340_; 
v_root_2338_ = lean_ctor_get(v_t_2336_, 0);
lean_inc_ref(v_root_2338_);
v_tail_2339_ = lean_ctor_get(v_t_2336_, 1);
lean_inc_ref(v_tail_2339_);
lean_dec_ref(v_t_2336_);
lean_inc_ref(v_init_2337_);
v___x_2340_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_x_2335_, v_init_2337_, v_root_2338_, v_init_2337_);
lean_dec_ref(v_init_2337_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; 
lean_dec_ref(v_tail_2339_);
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref(v___x_2340_);
return v_a_2341_;
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; size_t v_sz_2345_; size_t v___x_2346_; lean_object* v___x_2347_; lean_object* v_fst_2348_; 
v_a_2342_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2342_);
lean_dec_ref(v___x_2340_);
v___x_2343_ = lean_box(0);
v___x_2344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
lean_ctor_set(v___x_2344_, 1, v_a_2342_);
v_sz_2345_ = lean_array_size(v_tail_2339_);
v___x_2346_ = ((size_t)0ULL);
v___x_2347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2335_, v_tail_2339_, v_sz_2345_, v___x_2346_, v___x_2344_);
lean_dec_ref(v_tail_2339_);
v_fst_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_fst_2348_);
if (lean_obj_tag(v_fst_2348_) == 0)
{
lean_object* v_snd_2349_; 
v_snd_2349_ = lean_ctor_get(v___x_2347_, 1);
lean_inc(v_snd_2349_);
lean_dec_ref(v___x_2347_);
return v_snd_2349_;
}
else
{
lean_object* v_val_2350_; 
lean_dec_ref(v___x_2347_);
v_val_2350_ = lean_ctor_get(v_fst_2348_, 0);
lean_inc(v_val_2350_);
lean_dec_ref(v_fst_2348_);
return v_val_2350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0___boxed(lean_object* v_x_2351_, lean_object* v_t_2352_, lean_object* v_init_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2351_, v_t_2352_, v_init_2353_);
lean_dec(v_x_2351_);
return v_res_2354_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2355_ = lean_unsigned_to_nat(32u);
v___x_2356_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___x_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
return v___x_2357_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1(void){
_start:
{
size_t v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v_cs_x27_2363_; 
v___x_2358_ = ((size_t)5ULL);
v___x_2359_ = lean_unsigned_to_nat(0u);
v___x_2360_ = lean_unsigned_to_nat(32u);
v___x_2361_ = lean_mk_empty_array_with_capacity(v___x_2360_);
v___x_2362_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0);
v_cs_x27_2363_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_2363_, 0, v___x_2362_);
lean_ctor_set(v_cs_x27_2363_, 1, v___x_2361_);
lean_ctor_set(v_cs_x27_2363_, 2, v___x_2359_);
lean_ctor_set(v_cs_x27_2363_, 3, v___x_2359_);
lean_ctor_set_usize(v_cs_x27_2363_, 4, v___x_2358_);
return v_cs_x27_2363_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_2366_; lean_object* v_cs_x27_2367_; lean_object* v___x_2368_; 
v_todo_2366_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2));
v_cs_x27_2367_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1);
v___x_2368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2368_, 0, v_cs_x27_2367_);
lean_ctor_set(v___x_2368_, 1, v_todo_2366_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(lean_object* v_x_2369_, lean_object* v_cs_2370_){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v_fst_2373_; lean_object* v_snd_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
v___x_2371_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3);
v___x_2372_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2369_, v_cs_2370_, v___x_2371_);
v_fst_2373_ = lean_ctor_get(v___x_2372_, 0);
v_snd_2374_ = lean_ctor_get(v___x_2372_, 1);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2372_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_snd_2374_);
lean_inc(v_fst_2373_);
lean_dec(v___x_2372_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_fst_2373_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v_snd_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___boxed(lean_object* v_x_2382_, lean_object* v_cs_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2382_, v_cs_2383_);
lean_dec(v_x_2382_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object* v_x_2385_, lean_object* v_cs_2386_){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2385_, v_cs_2386_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___boxed(lean_object* v_x_2388_, lean_object* v_cs_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(v_x_2388_, v_cs_2389_);
lean_dec(v_x_2388_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(lean_object* v_a_2391_, lean_object* v_y_2392_, lean_object* v_fst_2393_, lean_object* v_s_2394_){
_start:
{
lean_object* v_structs_2395_; lean_object* v_typeIdOf_2396_; lean_object* v_exprToStructId_2397_; lean_object* v_exprToStructIdEntries_2398_; lean_object* v_forbiddenNatModules_2399_; lean_object* v_natStructs_2400_; lean_object* v_natTypeIdOf_2401_; lean_object* v_exprToNatStructId_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; 
v_structs_2395_ = lean_ctor_get(v_s_2394_, 0);
v_typeIdOf_2396_ = lean_ctor_get(v_s_2394_, 1);
v_exprToStructId_2397_ = lean_ctor_get(v_s_2394_, 2);
v_exprToStructIdEntries_2398_ = lean_ctor_get(v_s_2394_, 3);
v_forbiddenNatModules_2399_ = lean_ctor_get(v_s_2394_, 4);
v_natStructs_2400_ = lean_ctor_get(v_s_2394_, 5);
v_natTypeIdOf_2401_ = lean_ctor_get(v_s_2394_, 6);
v_exprToNatStructId_2402_ = lean_ctor_get(v_s_2394_, 7);
v___x_2403_ = lean_array_get_size(v_structs_2395_);
v___x_2404_ = lean_nat_dec_lt(v_a_2391_, v___x_2403_);
if (v___x_2404_ == 0)
{
lean_dec_ref(v_fst_2393_);
return v_s_2394_;
}
else
{
lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2466_; 
lean_inc_ref(v_exprToNatStructId_2402_);
lean_inc_ref(v_natTypeIdOf_2401_);
lean_inc_ref(v_natStructs_2400_);
lean_inc_ref(v_forbiddenNatModules_2399_);
lean_inc_ref(v_exprToStructIdEntries_2398_);
lean_inc_ref(v_exprToStructId_2397_);
lean_inc_ref(v_typeIdOf_2396_);
lean_inc_ref(v_structs_2395_);
v_isSharedCheck_2466_ = !lean_is_exclusive(v_s_2394_);
if (v_isSharedCheck_2466_ == 0)
{
lean_object* v_unused_2467_; lean_object* v_unused_2468_; lean_object* v_unused_2469_; lean_object* v_unused_2470_; lean_object* v_unused_2471_; lean_object* v_unused_2472_; lean_object* v_unused_2473_; lean_object* v_unused_2474_; 
v_unused_2467_ = lean_ctor_get(v_s_2394_, 7);
lean_dec(v_unused_2467_);
v_unused_2468_ = lean_ctor_get(v_s_2394_, 6);
lean_dec(v_unused_2468_);
v_unused_2469_ = lean_ctor_get(v_s_2394_, 5);
lean_dec(v_unused_2469_);
v_unused_2470_ = lean_ctor_get(v_s_2394_, 4);
lean_dec(v_unused_2470_);
v_unused_2471_ = lean_ctor_get(v_s_2394_, 3);
lean_dec(v_unused_2471_);
v_unused_2472_ = lean_ctor_get(v_s_2394_, 2);
lean_dec(v_unused_2472_);
v_unused_2473_ = lean_ctor_get(v_s_2394_, 1);
lean_dec(v_unused_2473_);
v_unused_2474_ = lean_ctor_get(v_s_2394_, 0);
lean_dec(v_unused_2474_);
v___x_2406_ = v_s_2394_;
v_isShared_2407_ = v_isSharedCheck_2466_;
goto v_resetjp_2405_;
}
else
{
lean_dec(v_s_2394_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2466_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v_v_2408_; lean_object* v_id_2409_; lean_object* v_ringId_x3f_2410_; lean_object* v_type_2411_; lean_object* v_u_2412_; lean_object* v_intModuleInst_2413_; lean_object* v_leInst_x3f_2414_; lean_object* v_ltInst_x3f_2415_; lean_object* v_lawfulOrderLTInst_x3f_2416_; lean_object* v_isPreorderInst_x3f_2417_; lean_object* v_orderedAddInst_x3f_2418_; lean_object* v_isLinearInst_x3f_2419_; lean_object* v_noNatDivInst_x3f_2420_; lean_object* v_ringInst_x3f_2421_; lean_object* v_commRingInst_x3f_2422_; lean_object* v_orderedRingInst_x3f_2423_; lean_object* v_fieldInst_x3f_2424_; lean_object* v_charInst_x3f_2425_; lean_object* v_zero_2426_; lean_object* v_ofNatZero_2427_; lean_object* v_one_x3f_2428_; lean_object* v_leFn_x3f_2429_; lean_object* v_ltFn_x3f_2430_; lean_object* v_addFn_2431_; lean_object* v_zsmulFn_2432_; lean_object* v_nsmulFn_2433_; lean_object* v_zsmulFn_x3f_2434_; lean_object* v_nsmulFn_x3f_2435_; lean_object* v_homomulFn_x3f_2436_; lean_object* v_subFn_2437_; lean_object* v_negFn_2438_; lean_object* v_vars_2439_; lean_object* v_varMap_2440_; lean_object* v_lowers_2441_; lean_object* v_uppers_2442_; lean_object* v_diseqs_2443_; lean_object* v_assignment_2444_; uint8_t v_caseSplits_2445_; lean_object* v_conflict_x3f_2446_; lean_object* v_diseqSplits_2447_; lean_object* v_elimEqs_2448_; lean_object* v_elimStack_2449_; lean_object* v_occurs_2450_; lean_object* v_ignored_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2465_; 
v_v_2408_ = lean_array_fget(v_structs_2395_, v_a_2391_);
v_id_2409_ = lean_ctor_get(v_v_2408_, 0);
v_ringId_x3f_2410_ = lean_ctor_get(v_v_2408_, 1);
v_type_2411_ = lean_ctor_get(v_v_2408_, 2);
v_u_2412_ = lean_ctor_get(v_v_2408_, 3);
v_intModuleInst_2413_ = lean_ctor_get(v_v_2408_, 4);
v_leInst_x3f_2414_ = lean_ctor_get(v_v_2408_, 5);
v_ltInst_x3f_2415_ = lean_ctor_get(v_v_2408_, 6);
v_lawfulOrderLTInst_x3f_2416_ = lean_ctor_get(v_v_2408_, 7);
v_isPreorderInst_x3f_2417_ = lean_ctor_get(v_v_2408_, 8);
v_orderedAddInst_x3f_2418_ = lean_ctor_get(v_v_2408_, 9);
v_isLinearInst_x3f_2419_ = lean_ctor_get(v_v_2408_, 10);
v_noNatDivInst_x3f_2420_ = lean_ctor_get(v_v_2408_, 11);
v_ringInst_x3f_2421_ = lean_ctor_get(v_v_2408_, 12);
v_commRingInst_x3f_2422_ = lean_ctor_get(v_v_2408_, 13);
v_orderedRingInst_x3f_2423_ = lean_ctor_get(v_v_2408_, 14);
v_fieldInst_x3f_2424_ = lean_ctor_get(v_v_2408_, 15);
v_charInst_x3f_2425_ = lean_ctor_get(v_v_2408_, 16);
v_zero_2426_ = lean_ctor_get(v_v_2408_, 17);
v_ofNatZero_2427_ = lean_ctor_get(v_v_2408_, 18);
v_one_x3f_2428_ = lean_ctor_get(v_v_2408_, 19);
v_leFn_x3f_2429_ = lean_ctor_get(v_v_2408_, 20);
v_ltFn_x3f_2430_ = lean_ctor_get(v_v_2408_, 21);
v_addFn_2431_ = lean_ctor_get(v_v_2408_, 22);
v_zsmulFn_2432_ = lean_ctor_get(v_v_2408_, 23);
v_nsmulFn_2433_ = lean_ctor_get(v_v_2408_, 24);
v_zsmulFn_x3f_2434_ = lean_ctor_get(v_v_2408_, 25);
v_nsmulFn_x3f_2435_ = lean_ctor_get(v_v_2408_, 26);
v_homomulFn_x3f_2436_ = lean_ctor_get(v_v_2408_, 27);
v_subFn_2437_ = lean_ctor_get(v_v_2408_, 28);
v_negFn_2438_ = lean_ctor_get(v_v_2408_, 29);
v_vars_2439_ = lean_ctor_get(v_v_2408_, 30);
v_varMap_2440_ = lean_ctor_get(v_v_2408_, 31);
v_lowers_2441_ = lean_ctor_get(v_v_2408_, 32);
v_uppers_2442_ = lean_ctor_get(v_v_2408_, 33);
v_diseqs_2443_ = lean_ctor_get(v_v_2408_, 34);
v_assignment_2444_ = lean_ctor_get(v_v_2408_, 35);
v_caseSplits_2445_ = lean_ctor_get_uint8(v_v_2408_, sizeof(void*)*42);
v_conflict_x3f_2446_ = lean_ctor_get(v_v_2408_, 36);
v_diseqSplits_2447_ = lean_ctor_get(v_v_2408_, 37);
v_elimEqs_2448_ = lean_ctor_get(v_v_2408_, 38);
v_elimStack_2449_ = lean_ctor_get(v_v_2408_, 39);
v_occurs_2450_ = lean_ctor_get(v_v_2408_, 40);
v_ignored_2451_ = lean_ctor_get(v_v_2408_, 41);
v_isSharedCheck_2465_ = !lean_is_exclusive(v_v_2408_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2453_ = v_v_2408_;
v_isShared_2454_ = v_isSharedCheck_2465_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_ignored_2451_);
lean_inc(v_occurs_2450_);
lean_inc(v_elimStack_2449_);
lean_inc(v_elimEqs_2448_);
lean_inc(v_diseqSplits_2447_);
lean_inc(v_conflict_x3f_2446_);
lean_inc(v_assignment_2444_);
lean_inc(v_diseqs_2443_);
lean_inc(v_uppers_2442_);
lean_inc(v_lowers_2441_);
lean_inc(v_varMap_2440_);
lean_inc(v_vars_2439_);
lean_inc(v_negFn_2438_);
lean_inc(v_subFn_2437_);
lean_inc(v_homomulFn_x3f_2436_);
lean_inc(v_nsmulFn_x3f_2435_);
lean_inc(v_zsmulFn_x3f_2434_);
lean_inc(v_nsmulFn_2433_);
lean_inc(v_zsmulFn_2432_);
lean_inc(v_addFn_2431_);
lean_inc(v_ltFn_x3f_2430_);
lean_inc(v_leFn_x3f_2429_);
lean_inc(v_one_x3f_2428_);
lean_inc(v_ofNatZero_2427_);
lean_inc(v_zero_2426_);
lean_inc(v_charInst_x3f_2425_);
lean_inc(v_fieldInst_x3f_2424_);
lean_inc(v_orderedRingInst_x3f_2423_);
lean_inc(v_commRingInst_x3f_2422_);
lean_inc(v_ringInst_x3f_2421_);
lean_inc(v_noNatDivInst_x3f_2420_);
lean_inc(v_isLinearInst_x3f_2419_);
lean_inc(v_orderedAddInst_x3f_2418_);
lean_inc(v_isPreorderInst_x3f_2417_);
lean_inc(v_lawfulOrderLTInst_x3f_2416_);
lean_inc(v_ltInst_x3f_2415_);
lean_inc(v_leInst_x3f_2414_);
lean_inc(v_intModuleInst_2413_);
lean_inc(v_u_2412_);
lean_inc(v_type_2411_);
lean_inc(v_ringId_x3f_2410_);
lean_inc(v_id_2409_);
lean_dec(v_v_2408_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2465_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2455_; lean_object* v_xs_x27_2456_; lean_object* v___x_2457_; lean_object* v___x_2459_; 
v___x_2455_ = lean_box(0);
v_xs_x27_2456_ = lean_array_fset(v_structs_2395_, v_a_2391_, v___x_2455_);
v___x_2457_ = l_Lean_PersistentArray_set___redArg(v_lowers_2441_, v_y_2392_, v_fst_2393_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 32, v___x_2457_);
v___x_2459_ = v___x_2453_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_id_2409_);
lean_ctor_set(v_reuseFailAlloc_2464_, 1, v_ringId_x3f_2410_);
lean_ctor_set(v_reuseFailAlloc_2464_, 2, v_type_2411_);
lean_ctor_set(v_reuseFailAlloc_2464_, 3, v_u_2412_);
lean_ctor_set(v_reuseFailAlloc_2464_, 4, v_intModuleInst_2413_);
lean_ctor_set(v_reuseFailAlloc_2464_, 5, v_leInst_x3f_2414_);
lean_ctor_set(v_reuseFailAlloc_2464_, 6, v_ltInst_x3f_2415_);
lean_ctor_set(v_reuseFailAlloc_2464_, 7, v_lawfulOrderLTInst_x3f_2416_);
lean_ctor_set(v_reuseFailAlloc_2464_, 8, v_isPreorderInst_x3f_2417_);
lean_ctor_set(v_reuseFailAlloc_2464_, 9, v_orderedAddInst_x3f_2418_);
lean_ctor_set(v_reuseFailAlloc_2464_, 10, v_isLinearInst_x3f_2419_);
lean_ctor_set(v_reuseFailAlloc_2464_, 11, v_noNatDivInst_x3f_2420_);
lean_ctor_set(v_reuseFailAlloc_2464_, 12, v_ringInst_x3f_2421_);
lean_ctor_set(v_reuseFailAlloc_2464_, 13, v_commRingInst_x3f_2422_);
lean_ctor_set(v_reuseFailAlloc_2464_, 14, v_orderedRingInst_x3f_2423_);
lean_ctor_set(v_reuseFailAlloc_2464_, 15, v_fieldInst_x3f_2424_);
lean_ctor_set(v_reuseFailAlloc_2464_, 16, v_charInst_x3f_2425_);
lean_ctor_set(v_reuseFailAlloc_2464_, 17, v_zero_2426_);
lean_ctor_set(v_reuseFailAlloc_2464_, 18, v_ofNatZero_2427_);
lean_ctor_set(v_reuseFailAlloc_2464_, 19, v_one_x3f_2428_);
lean_ctor_set(v_reuseFailAlloc_2464_, 20, v_leFn_x3f_2429_);
lean_ctor_set(v_reuseFailAlloc_2464_, 21, v_ltFn_x3f_2430_);
lean_ctor_set(v_reuseFailAlloc_2464_, 22, v_addFn_2431_);
lean_ctor_set(v_reuseFailAlloc_2464_, 23, v_zsmulFn_2432_);
lean_ctor_set(v_reuseFailAlloc_2464_, 24, v_nsmulFn_2433_);
lean_ctor_set(v_reuseFailAlloc_2464_, 25, v_zsmulFn_x3f_2434_);
lean_ctor_set(v_reuseFailAlloc_2464_, 26, v_nsmulFn_x3f_2435_);
lean_ctor_set(v_reuseFailAlloc_2464_, 27, v_homomulFn_x3f_2436_);
lean_ctor_set(v_reuseFailAlloc_2464_, 28, v_subFn_2437_);
lean_ctor_set(v_reuseFailAlloc_2464_, 29, v_negFn_2438_);
lean_ctor_set(v_reuseFailAlloc_2464_, 30, v_vars_2439_);
lean_ctor_set(v_reuseFailAlloc_2464_, 31, v_varMap_2440_);
lean_ctor_set(v_reuseFailAlloc_2464_, 32, v___x_2457_);
lean_ctor_set(v_reuseFailAlloc_2464_, 33, v_uppers_2442_);
lean_ctor_set(v_reuseFailAlloc_2464_, 34, v_diseqs_2443_);
lean_ctor_set(v_reuseFailAlloc_2464_, 35, v_assignment_2444_);
lean_ctor_set(v_reuseFailAlloc_2464_, 36, v_conflict_x3f_2446_);
lean_ctor_set(v_reuseFailAlloc_2464_, 37, v_diseqSplits_2447_);
lean_ctor_set(v_reuseFailAlloc_2464_, 38, v_elimEqs_2448_);
lean_ctor_set(v_reuseFailAlloc_2464_, 39, v_elimStack_2449_);
lean_ctor_set(v_reuseFailAlloc_2464_, 40, v_occurs_2450_);
lean_ctor_set(v_reuseFailAlloc_2464_, 41, v_ignored_2451_);
lean_ctor_set_uint8(v_reuseFailAlloc_2464_, sizeof(void*)*42, v_caseSplits_2445_);
v___x_2459_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
lean_object* v___x_2460_; lean_object* v___x_2462_; 
v___x_2460_ = lean_array_fset(v_xs_x27_2456_, v_a_2391_, v___x_2459_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 0, v___x_2460_);
v___x_2462_ = v___x_2406_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2460_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v_typeIdOf_2396_);
lean_ctor_set(v_reuseFailAlloc_2463_, 2, v_exprToStructId_2397_);
lean_ctor_set(v_reuseFailAlloc_2463_, 3, v_exprToStructIdEntries_2398_);
lean_ctor_set(v_reuseFailAlloc_2463_, 4, v_forbiddenNatModules_2399_);
lean_ctor_set(v_reuseFailAlloc_2463_, 5, v_natStructs_2400_);
lean_ctor_set(v_reuseFailAlloc_2463_, 6, v_natTypeIdOf_2401_);
lean_ctor_set(v_reuseFailAlloc_2463_, 7, v_exprToNatStructId_2402_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed(lean_object* v_a_2475_, lean_object* v_y_2476_, lean_object* v_fst_2477_, lean_object* v_s_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(v_a_2475_, v_y_2476_, v_fst_2477_, v_s_2478_);
lean_dec(v_y_2476_);
lean_dec(v_a_2475_);
return v_res_2479_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0(void){
_start:
{
lean_object* v___x_2480_; 
v___x_2480_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object* v_a_2481_, lean_object* v_x_2482_, lean_object* v_c_2483_, lean_object* v_y_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2532_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2500_ = v___x_2497_;
v_isShared_2501_ = v_isSharedCheck_2532_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2497_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2532_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
uint8_t v___x_2502_; 
v___x_2502_ = lean_unbox(v_a_2498_);
lean_dec(v_a_2498_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2503_; 
lean_del_object(v___x_2500_);
v___x_2503_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___y_2506_; lean_object* v_lowers_2514_; lean_object* v_size_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref(v___x_2503_);
v_lowers_2514_ = lean_ctor_get(v_a_2504_, 32);
lean_inc_ref(v_lowers_2514_);
lean_dec(v_a_2504_);
v_size_2515_ = lean_ctor_get(v_lowers_2514_, 2);
v___x_2516_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2517_ = lean_nat_dec_lt(v_y_2484_, v_size_2515_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; 
lean_dec_ref(v_lowers_2514_);
v___x_2518_ = l_outOfBounds___redArg(v___x_2516_);
v___y_2506_ = v___x_2518_;
goto v___jp_2505_;
}
else
{
lean_object* v___x_2519_; 
v___x_2519_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2516_, v_lowers_2514_, v_y_2484_);
v___y_2506_ = v___x_2519_;
goto v___jp_2505_;
}
v___jp_2505_:
{
lean_object* v___x_2507_; lean_object* v_fst_2508_; lean_object* v_snd_2509_; lean_object* v___f_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2507_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2482_, v___y_2506_);
v_fst_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_fst_2508_);
v_snd_2509_ = lean_ctor_get(v___x_2507_, 1);
lean_inc(v_snd_2509_);
lean_dec_ref(v___x_2507_);
lean_inc(v_a_2485_);
v___f_2510_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2510_, 0, v_a_2485_);
lean_closure_set(v___f_2510_, 1, v_y_2484_);
lean_closure_set(v___f_2510_, 2, v_fst_2508_);
v___x_2511_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2512_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2511_, v___f_2510_, v_a_2486_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v___x_2513_; 
lean_dec_ref(v___x_2512_);
v___x_2513_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2481_, v_x_2482_, v_c_2483_, v_snd_2509_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
lean_dec(v_snd_2509_);
return v___x_2513_;
}
else
{
lean_dec(v_snd_2509_);
lean_dec_ref(v_c_2483_);
lean_dec(v_x_2482_);
lean_dec(v_a_2481_);
return v___x_2512_;
}
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec(v_y_2484_);
lean_dec_ref(v_c_2483_);
lean_dec(v_x_2482_);
lean_dec(v_a_2481_);
v_a_2520_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2503_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2503_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
else
{
lean_object* v___x_2528_; lean_object* v___x_2530_; 
lean_dec(v_y_2484_);
lean_dec_ref(v_c_2483_);
lean_dec(v_x_2482_);
lean_dec(v_a_2481_);
v___x_2528_ = lean_box(0);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2528_);
v___x_2530_ = v___x_2500_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec(v_y_2484_);
lean_dec_ref(v_c_2483_);
lean_dec(v_x_2482_);
lean_dec(v_a_2481_);
v_a_2533_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2497_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2497_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object* v_a_2541_, lean_object* v_x_2542_, lean_object* v_c_2543_, lean_object* v_y_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_2541_, v_x_2542_, v_c_2543_, v_y_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec(v_a_2546_);
lean_dec(v_a_2545_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(lean_object* v_a_2558_, lean_object* v_y_2559_, lean_object* v_fst_2560_, lean_object* v_s_2561_){
_start:
{
lean_object* v_structs_2562_; lean_object* v_typeIdOf_2563_; lean_object* v_exprToStructId_2564_; lean_object* v_exprToStructIdEntries_2565_; lean_object* v_forbiddenNatModules_2566_; lean_object* v_natStructs_2567_; lean_object* v_natTypeIdOf_2568_; lean_object* v_exprToNatStructId_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v_structs_2562_ = lean_ctor_get(v_s_2561_, 0);
v_typeIdOf_2563_ = lean_ctor_get(v_s_2561_, 1);
v_exprToStructId_2564_ = lean_ctor_get(v_s_2561_, 2);
v_exprToStructIdEntries_2565_ = lean_ctor_get(v_s_2561_, 3);
v_forbiddenNatModules_2566_ = lean_ctor_get(v_s_2561_, 4);
v_natStructs_2567_ = lean_ctor_get(v_s_2561_, 5);
v_natTypeIdOf_2568_ = lean_ctor_get(v_s_2561_, 6);
v_exprToNatStructId_2569_ = lean_ctor_get(v_s_2561_, 7);
v___x_2570_ = lean_array_get_size(v_structs_2562_);
v___x_2571_ = lean_nat_dec_lt(v_a_2558_, v___x_2570_);
if (v___x_2571_ == 0)
{
lean_dec_ref(v_fst_2560_);
return v_s_2561_;
}
else
{
lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2633_; 
lean_inc_ref(v_exprToNatStructId_2569_);
lean_inc_ref(v_natTypeIdOf_2568_);
lean_inc_ref(v_natStructs_2567_);
lean_inc_ref(v_forbiddenNatModules_2566_);
lean_inc_ref(v_exprToStructIdEntries_2565_);
lean_inc_ref(v_exprToStructId_2564_);
lean_inc_ref(v_typeIdOf_2563_);
lean_inc_ref(v_structs_2562_);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_s_2561_);
if (v_isSharedCheck_2633_ == 0)
{
lean_object* v_unused_2634_; lean_object* v_unused_2635_; lean_object* v_unused_2636_; lean_object* v_unused_2637_; lean_object* v_unused_2638_; lean_object* v_unused_2639_; lean_object* v_unused_2640_; lean_object* v_unused_2641_; 
v_unused_2634_ = lean_ctor_get(v_s_2561_, 7);
lean_dec(v_unused_2634_);
v_unused_2635_ = lean_ctor_get(v_s_2561_, 6);
lean_dec(v_unused_2635_);
v_unused_2636_ = lean_ctor_get(v_s_2561_, 5);
lean_dec(v_unused_2636_);
v_unused_2637_ = lean_ctor_get(v_s_2561_, 4);
lean_dec(v_unused_2637_);
v_unused_2638_ = lean_ctor_get(v_s_2561_, 3);
lean_dec(v_unused_2638_);
v_unused_2639_ = lean_ctor_get(v_s_2561_, 2);
lean_dec(v_unused_2639_);
v_unused_2640_ = lean_ctor_get(v_s_2561_, 1);
lean_dec(v_unused_2640_);
v_unused_2641_ = lean_ctor_get(v_s_2561_, 0);
lean_dec(v_unused_2641_);
v___x_2573_ = v_s_2561_;
v_isShared_2574_ = v_isSharedCheck_2633_;
goto v_resetjp_2572_;
}
else
{
lean_dec(v_s_2561_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2633_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v_v_2575_; lean_object* v_id_2576_; lean_object* v_ringId_x3f_2577_; lean_object* v_type_2578_; lean_object* v_u_2579_; lean_object* v_intModuleInst_2580_; lean_object* v_leInst_x3f_2581_; lean_object* v_ltInst_x3f_2582_; lean_object* v_lawfulOrderLTInst_x3f_2583_; lean_object* v_isPreorderInst_x3f_2584_; lean_object* v_orderedAddInst_x3f_2585_; lean_object* v_isLinearInst_x3f_2586_; lean_object* v_noNatDivInst_x3f_2587_; lean_object* v_ringInst_x3f_2588_; lean_object* v_commRingInst_x3f_2589_; lean_object* v_orderedRingInst_x3f_2590_; lean_object* v_fieldInst_x3f_2591_; lean_object* v_charInst_x3f_2592_; lean_object* v_zero_2593_; lean_object* v_ofNatZero_2594_; lean_object* v_one_x3f_2595_; lean_object* v_leFn_x3f_2596_; lean_object* v_ltFn_x3f_2597_; lean_object* v_addFn_2598_; lean_object* v_zsmulFn_2599_; lean_object* v_nsmulFn_2600_; lean_object* v_zsmulFn_x3f_2601_; lean_object* v_nsmulFn_x3f_2602_; lean_object* v_homomulFn_x3f_2603_; lean_object* v_subFn_2604_; lean_object* v_negFn_2605_; lean_object* v_vars_2606_; lean_object* v_varMap_2607_; lean_object* v_lowers_2608_; lean_object* v_uppers_2609_; lean_object* v_diseqs_2610_; lean_object* v_assignment_2611_; uint8_t v_caseSplits_2612_; lean_object* v_conflict_x3f_2613_; lean_object* v_diseqSplits_2614_; lean_object* v_elimEqs_2615_; lean_object* v_elimStack_2616_; lean_object* v_occurs_2617_; lean_object* v_ignored_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2632_; 
v_v_2575_ = lean_array_fget(v_structs_2562_, v_a_2558_);
v_id_2576_ = lean_ctor_get(v_v_2575_, 0);
v_ringId_x3f_2577_ = lean_ctor_get(v_v_2575_, 1);
v_type_2578_ = lean_ctor_get(v_v_2575_, 2);
v_u_2579_ = lean_ctor_get(v_v_2575_, 3);
v_intModuleInst_2580_ = lean_ctor_get(v_v_2575_, 4);
v_leInst_x3f_2581_ = lean_ctor_get(v_v_2575_, 5);
v_ltInst_x3f_2582_ = lean_ctor_get(v_v_2575_, 6);
v_lawfulOrderLTInst_x3f_2583_ = lean_ctor_get(v_v_2575_, 7);
v_isPreorderInst_x3f_2584_ = lean_ctor_get(v_v_2575_, 8);
v_orderedAddInst_x3f_2585_ = lean_ctor_get(v_v_2575_, 9);
v_isLinearInst_x3f_2586_ = lean_ctor_get(v_v_2575_, 10);
v_noNatDivInst_x3f_2587_ = lean_ctor_get(v_v_2575_, 11);
v_ringInst_x3f_2588_ = lean_ctor_get(v_v_2575_, 12);
v_commRingInst_x3f_2589_ = lean_ctor_get(v_v_2575_, 13);
v_orderedRingInst_x3f_2590_ = lean_ctor_get(v_v_2575_, 14);
v_fieldInst_x3f_2591_ = lean_ctor_get(v_v_2575_, 15);
v_charInst_x3f_2592_ = lean_ctor_get(v_v_2575_, 16);
v_zero_2593_ = lean_ctor_get(v_v_2575_, 17);
v_ofNatZero_2594_ = lean_ctor_get(v_v_2575_, 18);
v_one_x3f_2595_ = lean_ctor_get(v_v_2575_, 19);
v_leFn_x3f_2596_ = lean_ctor_get(v_v_2575_, 20);
v_ltFn_x3f_2597_ = lean_ctor_get(v_v_2575_, 21);
v_addFn_2598_ = lean_ctor_get(v_v_2575_, 22);
v_zsmulFn_2599_ = lean_ctor_get(v_v_2575_, 23);
v_nsmulFn_2600_ = lean_ctor_get(v_v_2575_, 24);
v_zsmulFn_x3f_2601_ = lean_ctor_get(v_v_2575_, 25);
v_nsmulFn_x3f_2602_ = lean_ctor_get(v_v_2575_, 26);
v_homomulFn_x3f_2603_ = lean_ctor_get(v_v_2575_, 27);
v_subFn_2604_ = lean_ctor_get(v_v_2575_, 28);
v_negFn_2605_ = lean_ctor_get(v_v_2575_, 29);
v_vars_2606_ = lean_ctor_get(v_v_2575_, 30);
v_varMap_2607_ = lean_ctor_get(v_v_2575_, 31);
v_lowers_2608_ = lean_ctor_get(v_v_2575_, 32);
v_uppers_2609_ = lean_ctor_get(v_v_2575_, 33);
v_diseqs_2610_ = lean_ctor_get(v_v_2575_, 34);
v_assignment_2611_ = lean_ctor_get(v_v_2575_, 35);
v_caseSplits_2612_ = lean_ctor_get_uint8(v_v_2575_, sizeof(void*)*42);
v_conflict_x3f_2613_ = lean_ctor_get(v_v_2575_, 36);
v_diseqSplits_2614_ = lean_ctor_get(v_v_2575_, 37);
v_elimEqs_2615_ = lean_ctor_get(v_v_2575_, 38);
v_elimStack_2616_ = lean_ctor_get(v_v_2575_, 39);
v_occurs_2617_ = lean_ctor_get(v_v_2575_, 40);
v_ignored_2618_ = lean_ctor_get(v_v_2575_, 41);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_v_2575_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2620_ = v_v_2575_;
v_isShared_2621_ = v_isSharedCheck_2632_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_ignored_2618_);
lean_inc(v_occurs_2617_);
lean_inc(v_elimStack_2616_);
lean_inc(v_elimEqs_2615_);
lean_inc(v_diseqSplits_2614_);
lean_inc(v_conflict_x3f_2613_);
lean_inc(v_assignment_2611_);
lean_inc(v_diseqs_2610_);
lean_inc(v_uppers_2609_);
lean_inc(v_lowers_2608_);
lean_inc(v_varMap_2607_);
lean_inc(v_vars_2606_);
lean_inc(v_negFn_2605_);
lean_inc(v_subFn_2604_);
lean_inc(v_homomulFn_x3f_2603_);
lean_inc(v_nsmulFn_x3f_2602_);
lean_inc(v_zsmulFn_x3f_2601_);
lean_inc(v_nsmulFn_2600_);
lean_inc(v_zsmulFn_2599_);
lean_inc(v_addFn_2598_);
lean_inc(v_ltFn_x3f_2597_);
lean_inc(v_leFn_x3f_2596_);
lean_inc(v_one_x3f_2595_);
lean_inc(v_ofNatZero_2594_);
lean_inc(v_zero_2593_);
lean_inc(v_charInst_x3f_2592_);
lean_inc(v_fieldInst_x3f_2591_);
lean_inc(v_orderedRingInst_x3f_2590_);
lean_inc(v_commRingInst_x3f_2589_);
lean_inc(v_ringInst_x3f_2588_);
lean_inc(v_noNatDivInst_x3f_2587_);
lean_inc(v_isLinearInst_x3f_2586_);
lean_inc(v_orderedAddInst_x3f_2585_);
lean_inc(v_isPreorderInst_x3f_2584_);
lean_inc(v_lawfulOrderLTInst_x3f_2583_);
lean_inc(v_ltInst_x3f_2582_);
lean_inc(v_leInst_x3f_2581_);
lean_inc(v_intModuleInst_2580_);
lean_inc(v_u_2579_);
lean_inc(v_type_2578_);
lean_inc(v_ringId_x3f_2577_);
lean_inc(v_id_2576_);
lean_dec(v_v_2575_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2632_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; lean_object* v_xs_x27_2623_; lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2622_ = lean_box(0);
v_xs_x27_2623_ = lean_array_fset(v_structs_2562_, v_a_2558_, v___x_2622_);
v___x_2624_ = l_Lean_PersistentArray_set___redArg(v_uppers_2609_, v_y_2559_, v_fst_2560_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 33, v___x_2624_);
v___x_2626_ = v___x_2620_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_id_2576_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v_ringId_x3f_2577_);
lean_ctor_set(v_reuseFailAlloc_2631_, 2, v_type_2578_);
lean_ctor_set(v_reuseFailAlloc_2631_, 3, v_u_2579_);
lean_ctor_set(v_reuseFailAlloc_2631_, 4, v_intModuleInst_2580_);
lean_ctor_set(v_reuseFailAlloc_2631_, 5, v_leInst_x3f_2581_);
lean_ctor_set(v_reuseFailAlloc_2631_, 6, v_ltInst_x3f_2582_);
lean_ctor_set(v_reuseFailAlloc_2631_, 7, v_lawfulOrderLTInst_x3f_2583_);
lean_ctor_set(v_reuseFailAlloc_2631_, 8, v_isPreorderInst_x3f_2584_);
lean_ctor_set(v_reuseFailAlloc_2631_, 9, v_orderedAddInst_x3f_2585_);
lean_ctor_set(v_reuseFailAlloc_2631_, 10, v_isLinearInst_x3f_2586_);
lean_ctor_set(v_reuseFailAlloc_2631_, 11, v_noNatDivInst_x3f_2587_);
lean_ctor_set(v_reuseFailAlloc_2631_, 12, v_ringInst_x3f_2588_);
lean_ctor_set(v_reuseFailAlloc_2631_, 13, v_commRingInst_x3f_2589_);
lean_ctor_set(v_reuseFailAlloc_2631_, 14, v_orderedRingInst_x3f_2590_);
lean_ctor_set(v_reuseFailAlloc_2631_, 15, v_fieldInst_x3f_2591_);
lean_ctor_set(v_reuseFailAlloc_2631_, 16, v_charInst_x3f_2592_);
lean_ctor_set(v_reuseFailAlloc_2631_, 17, v_zero_2593_);
lean_ctor_set(v_reuseFailAlloc_2631_, 18, v_ofNatZero_2594_);
lean_ctor_set(v_reuseFailAlloc_2631_, 19, v_one_x3f_2595_);
lean_ctor_set(v_reuseFailAlloc_2631_, 20, v_leFn_x3f_2596_);
lean_ctor_set(v_reuseFailAlloc_2631_, 21, v_ltFn_x3f_2597_);
lean_ctor_set(v_reuseFailAlloc_2631_, 22, v_addFn_2598_);
lean_ctor_set(v_reuseFailAlloc_2631_, 23, v_zsmulFn_2599_);
lean_ctor_set(v_reuseFailAlloc_2631_, 24, v_nsmulFn_2600_);
lean_ctor_set(v_reuseFailAlloc_2631_, 25, v_zsmulFn_x3f_2601_);
lean_ctor_set(v_reuseFailAlloc_2631_, 26, v_nsmulFn_x3f_2602_);
lean_ctor_set(v_reuseFailAlloc_2631_, 27, v_homomulFn_x3f_2603_);
lean_ctor_set(v_reuseFailAlloc_2631_, 28, v_subFn_2604_);
lean_ctor_set(v_reuseFailAlloc_2631_, 29, v_negFn_2605_);
lean_ctor_set(v_reuseFailAlloc_2631_, 30, v_vars_2606_);
lean_ctor_set(v_reuseFailAlloc_2631_, 31, v_varMap_2607_);
lean_ctor_set(v_reuseFailAlloc_2631_, 32, v_lowers_2608_);
lean_ctor_set(v_reuseFailAlloc_2631_, 33, v___x_2624_);
lean_ctor_set(v_reuseFailAlloc_2631_, 34, v_diseqs_2610_);
lean_ctor_set(v_reuseFailAlloc_2631_, 35, v_assignment_2611_);
lean_ctor_set(v_reuseFailAlloc_2631_, 36, v_conflict_x3f_2613_);
lean_ctor_set(v_reuseFailAlloc_2631_, 37, v_diseqSplits_2614_);
lean_ctor_set(v_reuseFailAlloc_2631_, 38, v_elimEqs_2615_);
lean_ctor_set(v_reuseFailAlloc_2631_, 39, v_elimStack_2616_);
lean_ctor_set(v_reuseFailAlloc_2631_, 40, v_occurs_2617_);
lean_ctor_set(v_reuseFailAlloc_2631_, 41, v_ignored_2618_);
lean_ctor_set_uint8(v_reuseFailAlloc_2631_, sizeof(void*)*42, v_caseSplits_2612_);
v___x_2626_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
lean_object* v___x_2627_; lean_object* v___x_2629_; 
v___x_2627_ = lean_array_fset(v_xs_x27_2623_, v_a_2558_, v___x_2626_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2627_);
v___x_2629_ = v___x_2573_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2627_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_typeIdOf_2563_);
lean_ctor_set(v_reuseFailAlloc_2630_, 2, v_exprToStructId_2564_);
lean_ctor_set(v_reuseFailAlloc_2630_, 3, v_exprToStructIdEntries_2565_);
lean_ctor_set(v_reuseFailAlloc_2630_, 4, v_forbiddenNatModules_2566_);
lean_ctor_set(v_reuseFailAlloc_2630_, 5, v_natStructs_2567_);
lean_ctor_set(v_reuseFailAlloc_2630_, 6, v_natTypeIdOf_2568_);
lean_ctor_set(v_reuseFailAlloc_2630_, 7, v_exprToNatStructId_2569_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed(lean_object* v_a_2642_, lean_object* v_y_2643_, lean_object* v_fst_2644_, lean_object* v_s_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(v_a_2642_, v_y_2643_, v_fst_2644_, v_s_2645_);
lean_dec(v_y_2643_);
lean_dec(v_a_2642_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object* v_a_2647_, lean_object* v_x_2648_, lean_object* v_c_2649_, lean_object* v_y_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2698_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2666_ = v___x_2663_;
v_isShared_2667_ = v_isSharedCheck_2698_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2663_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2698_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
uint8_t v___x_2668_; 
v___x_2668_ = lean_unbox(v_a_2664_);
lean_dec(v_a_2664_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; 
lean_del_object(v___x_2666_);
v___x_2669_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v___y_2672_; lean_object* v_uppers_2680_; lean_object* v_size_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref(v___x_2669_);
v_uppers_2680_ = lean_ctor_get(v_a_2670_, 33);
lean_inc_ref(v_uppers_2680_);
lean_dec(v_a_2670_);
v_size_2681_ = lean_ctor_get(v_uppers_2680_, 2);
v___x_2682_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2683_ = lean_nat_dec_lt(v_y_2650_, v_size_2681_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; 
lean_dec_ref(v_uppers_2680_);
v___x_2684_ = l_outOfBounds___redArg(v___x_2682_);
v___y_2672_ = v___x_2684_;
goto v___jp_2671_;
}
else
{
lean_object* v___x_2685_; 
v___x_2685_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2682_, v_uppers_2680_, v_y_2650_);
v___y_2672_ = v___x_2685_;
goto v___jp_2671_;
}
v___jp_2671_:
{
lean_object* v___x_2673_; lean_object* v_fst_2674_; lean_object* v_snd_2675_; lean_object* v___f_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2673_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2648_, v___y_2672_);
v_fst_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_fst_2674_);
v_snd_2675_ = lean_ctor_get(v___x_2673_, 1);
lean_inc(v_snd_2675_);
lean_dec_ref(v___x_2673_);
lean_inc(v_a_2651_);
v___f_2676_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2676_, 0, v_a_2651_);
lean_closure_set(v___f_2676_, 1, v_y_2650_);
lean_closure_set(v___f_2676_, 2, v_fst_2674_);
v___x_2677_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2678_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2677_, v___f_2676_, v_a_2652_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v___x_2679_; 
lean_dec_ref(v___x_2678_);
v___x_2679_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2647_, v_x_2648_, v_c_2649_, v_snd_2675_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
lean_dec(v_snd_2675_);
return v___x_2679_;
}
else
{
lean_dec(v_snd_2675_);
lean_dec_ref(v_c_2649_);
lean_dec(v_x_2648_);
lean_dec(v_a_2647_);
return v___x_2678_;
}
}
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_dec(v_y_2650_);
lean_dec_ref(v_c_2649_);
lean_dec(v_x_2648_);
lean_dec(v_a_2647_);
v_a_2686_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2669_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2669_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
else
{
lean_object* v___x_2694_; lean_object* v___x_2696_; 
lean_dec(v_y_2650_);
lean_dec_ref(v_c_2649_);
lean_dec(v_x_2648_);
lean_dec(v_a_2647_);
v___x_2694_ = lean_box(0);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v___x_2694_);
v___x_2696_ = v___x_2666_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2694_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_dec(v_y_2650_);
lean_dec_ref(v_c_2649_);
lean_dec(v_x_2648_);
lean_dec(v_a_2647_);
v_a_2699_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2663_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2663_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object* v_a_2707_, lean_object* v_x_2708_, lean_object* v_c_2709_, lean_object* v_y_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_2707_, v_x_2708_, v_c_2709_, v_y_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec(v_a_2711_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(lean_object* v___y_2724_, lean_object* v_a_2725_, lean_object* v_s_2726_){
_start:
{
lean_object* v_structs_2727_; lean_object* v_typeIdOf_2728_; lean_object* v_exprToStructId_2729_; lean_object* v_exprToStructIdEntries_2730_; lean_object* v_forbiddenNatModules_2731_; lean_object* v_natStructs_2732_; lean_object* v_natTypeIdOf_2733_; lean_object* v_exprToNatStructId_2734_; lean_object* v___x_2735_; uint8_t v___x_2736_; 
v_structs_2727_ = lean_ctor_get(v_s_2726_, 0);
v_typeIdOf_2728_ = lean_ctor_get(v_s_2726_, 1);
v_exprToStructId_2729_ = lean_ctor_get(v_s_2726_, 2);
v_exprToStructIdEntries_2730_ = lean_ctor_get(v_s_2726_, 3);
v_forbiddenNatModules_2731_ = lean_ctor_get(v_s_2726_, 4);
v_natStructs_2732_ = lean_ctor_get(v_s_2726_, 5);
v_natTypeIdOf_2733_ = lean_ctor_get(v_s_2726_, 6);
v_exprToNatStructId_2734_ = lean_ctor_get(v_s_2726_, 7);
v___x_2735_ = lean_array_get_size(v_structs_2727_);
v___x_2736_ = lean_nat_dec_lt(v___y_2724_, v___x_2735_);
if (v___x_2736_ == 0)
{
lean_dec_ref(v_a_2725_);
return v_s_2726_;
}
else
{
lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2798_; 
lean_inc_ref(v_exprToNatStructId_2734_);
lean_inc_ref(v_natTypeIdOf_2733_);
lean_inc_ref(v_natStructs_2732_);
lean_inc_ref(v_forbiddenNatModules_2731_);
lean_inc_ref(v_exprToStructIdEntries_2730_);
lean_inc_ref(v_exprToStructId_2729_);
lean_inc_ref(v_typeIdOf_2728_);
lean_inc_ref(v_structs_2727_);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_s_2726_);
if (v_isSharedCheck_2798_ == 0)
{
lean_object* v_unused_2799_; lean_object* v_unused_2800_; lean_object* v_unused_2801_; lean_object* v_unused_2802_; lean_object* v_unused_2803_; lean_object* v_unused_2804_; lean_object* v_unused_2805_; lean_object* v_unused_2806_; 
v_unused_2799_ = lean_ctor_get(v_s_2726_, 7);
lean_dec(v_unused_2799_);
v_unused_2800_ = lean_ctor_get(v_s_2726_, 6);
lean_dec(v_unused_2800_);
v_unused_2801_ = lean_ctor_get(v_s_2726_, 5);
lean_dec(v_unused_2801_);
v_unused_2802_ = lean_ctor_get(v_s_2726_, 4);
lean_dec(v_unused_2802_);
v_unused_2803_ = lean_ctor_get(v_s_2726_, 3);
lean_dec(v_unused_2803_);
v_unused_2804_ = lean_ctor_get(v_s_2726_, 2);
lean_dec(v_unused_2804_);
v_unused_2805_ = lean_ctor_get(v_s_2726_, 1);
lean_dec(v_unused_2805_);
v_unused_2806_ = lean_ctor_get(v_s_2726_, 0);
lean_dec(v_unused_2806_);
v___x_2738_ = v_s_2726_;
v_isShared_2739_ = v_isSharedCheck_2798_;
goto v_resetjp_2737_;
}
else
{
lean_dec(v_s_2726_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2798_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v_v_2740_; lean_object* v_id_2741_; lean_object* v_ringId_x3f_2742_; lean_object* v_type_2743_; lean_object* v_u_2744_; lean_object* v_intModuleInst_2745_; lean_object* v_leInst_x3f_2746_; lean_object* v_ltInst_x3f_2747_; lean_object* v_lawfulOrderLTInst_x3f_2748_; lean_object* v_isPreorderInst_x3f_2749_; lean_object* v_orderedAddInst_x3f_2750_; lean_object* v_isLinearInst_x3f_2751_; lean_object* v_noNatDivInst_x3f_2752_; lean_object* v_ringInst_x3f_2753_; lean_object* v_commRingInst_x3f_2754_; lean_object* v_orderedRingInst_x3f_2755_; lean_object* v_fieldInst_x3f_2756_; lean_object* v_charInst_x3f_2757_; lean_object* v_zero_2758_; lean_object* v_ofNatZero_2759_; lean_object* v_one_x3f_2760_; lean_object* v_leFn_x3f_2761_; lean_object* v_ltFn_x3f_2762_; lean_object* v_addFn_2763_; lean_object* v_zsmulFn_2764_; lean_object* v_nsmulFn_2765_; lean_object* v_zsmulFn_x3f_2766_; lean_object* v_nsmulFn_x3f_2767_; lean_object* v_homomulFn_x3f_2768_; lean_object* v_subFn_2769_; lean_object* v_negFn_2770_; lean_object* v_vars_2771_; lean_object* v_varMap_2772_; lean_object* v_lowers_2773_; lean_object* v_uppers_2774_; lean_object* v_diseqs_2775_; lean_object* v_assignment_2776_; uint8_t v_caseSplits_2777_; lean_object* v_conflict_x3f_2778_; lean_object* v_diseqSplits_2779_; lean_object* v_elimEqs_2780_; lean_object* v_elimStack_2781_; lean_object* v_occurs_2782_; lean_object* v_ignored_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2797_; 
v_v_2740_ = lean_array_fget(v_structs_2727_, v___y_2724_);
v_id_2741_ = lean_ctor_get(v_v_2740_, 0);
v_ringId_x3f_2742_ = lean_ctor_get(v_v_2740_, 1);
v_type_2743_ = lean_ctor_get(v_v_2740_, 2);
v_u_2744_ = lean_ctor_get(v_v_2740_, 3);
v_intModuleInst_2745_ = lean_ctor_get(v_v_2740_, 4);
v_leInst_x3f_2746_ = lean_ctor_get(v_v_2740_, 5);
v_ltInst_x3f_2747_ = lean_ctor_get(v_v_2740_, 6);
v_lawfulOrderLTInst_x3f_2748_ = lean_ctor_get(v_v_2740_, 7);
v_isPreorderInst_x3f_2749_ = lean_ctor_get(v_v_2740_, 8);
v_orderedAddInst_x3f_2750_ = lean_ctor_get(v_v_2740_, 9);
v_isLinearInst_x3f_2751_ = lean_ctor_get(v_v_2740_, 10);
v_noNatDivInst_x3f_2752_ = lean_ctor_get(v_v_2740_, 11);
v_ringInst_x3f_2753_ = lean_ctor_get(v_v_2740_, 12);
v_commRingInst_x3f_2754_ = lean_ctor_get(v_v_2740_, 13);
v_orderedRingInst_x3f_2755_ = lean_ctor_get(v_v_2740_, 14);
v_fieldInst_x3f_2756_ = lean_ctor_get(v_v_2740_, 15);
v_charInst_x3f_2757_ = lean_ctor_get(v_v_2740_, 16);
v_zero_2758_ = lean_ctor_get(v_v_2740_, 17);
v_ofNatZero_2759_ = lean_ctor_get(v_v_2740_, 18);
v_one_x3f_2760_ = lean_ctor_get(v_v_2740_, 19);
v_leFn_x3f_2761_ = lean_ctor_get(v_v_2740_, 20);
v_ltFn_x3f_2762_ = lean_ctor_get(v_v_2740_, 21);
v_addFn_2763_ = lean_ctor_get(v_v_2740_, 22);
v_zsmulFn_2764_ = lean_ctor_get(v_v_2740_, 23);
v_nsmulFn_2765_ = lean_ctor_get(v_v_2740_, 24);
v_zsmulFn_x3f_2766_ = lean_ctor_get(v_v_2740_, 25);
v_nsmulFn_x3f_2767_ = lean_ctor_get(v_v_2740_, 26);
v_homomulFn_x3f_2768_ = lean_ctor_get(v_v_2740_, 27);
v_subFn_2769_ = lean_ctor_get(v_v_2740_, 28);
v_negFn_2770_ = lean_ctor_get(v_v_2740_, 29);
v_vars_2771_ = lean_ctor_get(v_v_2740_, 30);
v_varMap_2772_ = lean_ctor_get(v_v_2740_, 31);
v_lowers_2773_ = lean_ctor_get(v_v_2740_, 32);
v_uppers_2774_ = lean_ctor_get(v_v_2740_, 33);
v_diseqs_2775_ = lean_ctor_get(v_v_2740_, 34);
v_assignment_2776_ = lean_ctor_get(v_v_2740_, 35);
v_caseSplits_2777_ = lean_ctor_get_uint8(v_v_2740_, sizeof(void*)*42);
v_conflict_x3f_2778_ = lean_ctor_get(v_v_2740_, 36);
v_diseqSplits_2779_ = lean_ctor_get(v_v_2740_, 37);
v_elimEqs_2780_ = lean_ctor_get(v_v_2740_, 38);
v_elimStack_2781_ = lean_ctor_get(v_v_2740_, 39);
v_occurs_2782_ = lean_ctor_get(v_v_2740_, 40);
v_ignored_2783_ = lean_ctor_get(v_v_2740_, 41);
v_isSharedCheck_2797_ = !lean_is_exclusive(v_v_2740_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2785_ = v_v_2740_;
v_isShared_2786_ = v_isSharedCheck_2797_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_ignored_2783_);
lean_inc(v_occurs_2782_);
lean_inc(v_elimStack_2781_);
lean_inc(v_elimEqs_2780_);
lean_inc(v_diseqSplits_2779_);
lean_inc(v_conflict_x3f_2778_);
lean_inc(v_assignment_2776_);
lean_inc(v_diseqs_2775_);
lean_inc(v_uppers_2774_);
lean_inc(v_lowers_2773_);
lean_inc(v_varMap_2772_);
lean_inc(v_vars_2771_);
lean_inc(v_negFn_2770_);
lean_inc(v_subFn_2769_);
lean_inc(v_homomulFn_x3f_2768_);
lean_inc(v_nsmulFn_x3f_2767_);
lean_inc(v_zsmulFn_x3f_2766_);
lean_inc(v_nsmulFn_2765_);
lean_inc(v_zsmulFn_2764_);
lean_inc(v_addFn_2763_);
lean_inc(v_ltFn_x3f_2762_);
lean_inc(v_leFn_x3f_2761_);
lean_inc(v_one_x3f_2760_);
lean_inc(v_ofNatZero_2759_);
lean_inc(v_zero_2758_);
lean_inc(v_charInst_x3f_2757_);
lean_inc(v_fieldInst_x3f_2756_);
lean_inc(v_orderedRingInst_x3f_2755_);
lean_inc(v_commRingInst_x3f_2754_);
lean_inc(v_ringInst_x3f_2753_);
lean_inc(v_noNatDivInst_x3f_2752_);
lean_inc(v_isLinearInst_x3f_2751_);
lean_inc(v_orderedAddInst_x3f_2750_);
lean_inc(v_isPreorderInst_x3f_2749_);
lean_inc(v_lawfulOrderLTInst_x3f_2748_);
lean_inc(v_ltInst_x3f_2747_);
lean_inc(v_leInst_x3f_2746_);
lean_inc(v_intModuleInst_2745_);
lean_inc(v_u_2744_);
lean_inc(v_type_2743_);
lean_inc(v_ringId_x3f_2742_);
lean_inc(v_id_2741_);
lean_dec(v_v_2740_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2797_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2787_; lean_object* v_xs_x27_2788_; lean_object* v___x_2789_; lean_object* v___x_2791_; 
v___x_2787_ = lean_box(0);
v_xs_x27_2788_ = lean_array_fset(v_structs_2727_, v___y_2724_, v___x_2787_);
v___x_2789_ = l_Lean_PersistentArray_push___redArg(v_ignored_2783_, v_a_2725_);
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 41, v___x_2789_);
v___x_2791_ = v___x_2785_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_id_2741_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v_ringId_x3f_2742_);
lean_ctor_set(v_reuseFailAlloc_2796_, 2, v_type_2743_);
lean_ctor_set(v_reuseFailAlloc_2796_, 3, v_u_2744_);
lean_ctor_set(v_reuseFailAlloc_2796_, 4, v_intModuleInst_2745_);
lean_ctor_set(v_reuseFailAlloc_2796_, 5, v_leInst_x3f_2746_);
lean_ctor_set(v_reuseFailAlloc_2796_, 6, v_ltInst_x3f_2747_);
lean_ctor_set(v_reuseFailAlloc_2796_, 7, v_lawfulOrderLTInst_x3f_2748_);
lean_ctor_set(v_reuseFailAlloc_2796_, 8, v_isPreorderInst_x3f_2749_);
lean_ctor_set(v_reuseFailAlloc_2796_, 9, v_orderedAddInst_x3f_2750_);
lean_ctor_set(v_reuseFailAlloc_2796_, 10, v_isLinearInst_x3f_2751_);
lean_ctor_set(v_reuseFailAlloc_2796_, 11, v_noNatDivInst_x3f_2752_);
lean_ctor_set(v_reuseFailAlloc_2796_, 12, v_ringInst_x3f_2753_);
lean_ctor_set(v_reuseFailAlloc_2796_, 13, v_commRingInst_x3f_2754_);
lean_ctor_set(v_reuseFailAlloc_2796_, 14, v_orderedRingInst_x3f_2755_);
lean_ctor_set(v_reuseFailAlloc_2796_, 15, v_fieldInst_x3f_2756_);
lean_ctor_set(v_reuseFailAlloc_2796_, 16, v_charInst_x3f_2757_);
lean_ctor_set(v_reuseFailAlloc_2796_, 17, v_zero_2758_);
lean_ctor_set(v_reuseFailAlloc_2796_, 18, v_ofNatZero_2759_);
lean_ctor_set(v_reuseFailAlloc_2796_, 19, v_one_x3f_2760_);
lean_ctor_set(v_reuseFailAlloc_2796_, 20, v_leFn_x3f_2761_);
lean_ctor_set(v_reuseFailAlloc_2796_, 21, v_ltFn_x3f_2762_);
lean_ctor_set(v_reuseFailAlloc_2796_, 22, v_addFn_2763_);
lean_ctor_set(v_reuseFailAlloc_2796_, 23, v_zsmulFn_2764_);
lean_ctor_set(v_reuseFailAlloc_2796_, 24, v_nsmulFn_2765_);
lean_ctor_set(v_reuseFailAlloc_2796_, 25, v_zsmulFn_x3f_2766_);
lean_ctor_set(v_reuseFailAlloc_2796_, 26, v_nsmulFn_x3f_2767_);
lean_ctor_set(v_reuseFailAlloc_2796_, 27, v_homomulFn_x3f_2768_);
lean_ctor_set(v_reuseFailAlloc_2796_, 28, v_subFn_2769_);
lean_ctor_set(v_reuseFailAlloc_2796_, 29, v_negFn_2770_);
lean_ctor_set(v_reuseFailAlloc_2796_, 30, v_vars_2771_);
lean_ctor_set(v_reuseFailAlloc_2796_, 31, v_varMap_2772_);
lean_ctor_set(v_reuseFailAlloc_2796_, 32, v_lowers_2773_);
lean_ctor_set(v_reuseFailAlloc_2796_, 33, v_uppers_2774_);
lean_ctor_set(v_reuseFailAlloc_2796_, 34, v_diseqs_2775_);
lean_ctor_set(v_reuseFailAlloc_2796_, 35, v_assignment_2776_);
lean_ctor_set(v_reuseFailAlloc_2796_, 36, v_conflict_x3f_2778_);
lean_ctor_set(v_reuseFailAlloc_2796_, 37, v_diseqSplits_2779_);
lean_ctor_set(v_reuseFailAlloc_2796_, 38, v_elimEqs_2780_);
lean_ctor_set(v_reuseFailAlloc_2796_, 39, v_elimStack_2781_);
lean_ctor_set(v_reuseFailAlloc_2796_, 40, v_occurs_2782_);
lean_ctor_set(v_reuseFailAlloc_2796_, 41, v___x_2789_);
lean_ctor_set_uint8(v_reuseFailAlloc_2796_, sizeof(void*)*42, v_caseSplits_2777_);
v___x_2791_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_object* v___x_2792_; lean_object* v___x_2794_; 
v___x_2792_ = lean_array_fset(v_xs_x27_2788_, v___y_2724_, v___x_2791_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 0, v___x_2792_);
v___x_2794_ = v___x_2738_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2792_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v_typeIdOf_2728_);
lean_ctor_set(v_reuseFailAlloc_2795_, 2, v_exprToStructId_2729_);
lean_ctor_set(v_reuseFailAlloc_2795_, 3, v_exprToStructIdEntries_2730_);
lean_ctor_set(v_reuseFailAlloc_2795_, 4, v_forbiddenNatModules_2731_);
lean_ctor_set(v_reuseFailAlloc_2795_, 5, v_natStructs_2732_);
lean_ctor_set(v_reuseFailAlloc_2795_, 6, v_natTypeIdOf_2733_);
lean_ctor_set(v_reuseFailAlloc_2795_, 7, v_exprToNatStructId_2734_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed(lean_object* v___y_2807_, lean_object* v_a_2808_, lean_object* v_s_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(v___y_2807_, v_a_2808_, v_s_2809_);
lean_dec(v___y_2807_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object* v_c_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_){
_start:
{
lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v_cls_2856_; lean_object* v___x_2857_; lean_object* v_a_2858_; uint8_t v___x_2859_; 
v_cls_2856_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2857_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v_cls_2856_, v_a_2828_);
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref(v___x_2857_);
v___x_2859_ = lean_unbox(v_a_2858_);
lean_dec(v_a_2858_);
if (v___x_2859_ == 0)
{
v___y_2832_ = v_a_2819_;
v___y_2833_ = v_a_2820_;
v___y_2834_ = v_a_2821_;
v___y_2835_ = v_a_2822_;
v___y_2836_ = v_a_2823_;
v___y_2837_ = v_a_2824_;
v___y_2838_ = v_a_2825_;
v___y_2839_ = v_a_2826_;
v___y_2840_ = v_a_2827_;
v___y_2841_ = v_a_2828_;
v___y_2842_ = v_a_2829_;
goto v___jp_2831_;
}
else
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref(v___x_2860_);
v___x_2862_ = l_Lean_MessageData_ofExpr(v_a_2861_);
v___x_2863_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_2856_, v___x_2862_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_dec_ref(v___x_2863_);
v___y_2832_ = v_a_2819_;
v___y_2833_ = v_a_2820_;
v___y_2834_ = v_a_2821_;
v___y_2835_ = v_a_2822_;
v___y_2836_ = v_a_2823_;
v___y_2837_ = v_a_2824_;
v___y_2838_ = v_a_2825_;
v___y_2839_ = v_a_2826_;
v___y_2840_ = v_a_2827_;
v___y_2841_ = v_a_2828_;
v___y_2842_ = v_a_2829_;
goto v___jp_2831_;
}
else
{
return v___x_2863_;
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
v_a_2864_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2860_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2860_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
v___jp_2831_:
{
lean_object* v___x_2843_; 
v___x_2843_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2818_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___f_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref(v___x_2843_);
lean_inc(v___y_2832_);
v___f_2845_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2845_, 0, v___y_2832_);
lean_closure_set(v___f_2845_, 1, v_a_2844_);
v___x_2846_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2847_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2846_, v___f_2845_, v___y_2833_);
return v___x_2847_;
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
v_a_2848_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2843_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2843_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object* v_c_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_);
lean_dec(v_a_2883_);
lean_dec_ref(v_a_2882_);
lean_dec(v_a_2881_);
lean_dec_ref(v_a_2880_);
lean_dec(v_a_2879_);
lean_dec_ref(v_a_2878_);
lean_dec(v_a_2877_);
lean_dec_ref(v_a_2876_);
lean_dec(v_a_2875_);
lean_dec(v_a_2874_);
lean_dec(v_a_2873_);
lean_dec_ref(v_c_2872_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object* v_c_u2082_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v_fileName_2899_; lean_object* v_fileMap_2900_; lean_object* v_options_2901_; lean_object* v_currRecDepth_2902_; lean_object* v_maxRecDepth_2903_; lean_object* v_ref_2904_; lean_object* v_currNamespace_2905_; lean_object* v_openDecls_2906_; lean_object* v_initHeartbeats_2907_; lean_object* v_maxHeartbeats_2908_; lean_object* v_quotContext_2909_; lean_object* v_currMacroScope_2910_; uint8_t v_diag_2911_; lean_object* v_cancelTk_x3f_2912_; uint8_t v_suppressElabErrors_2913_; lean_object* v_inheritedTraceOptions_2914_; uint8_t v___x_2915_; 
v_fileName_2899_ = lean_ctor_get(v_a_2896_, 0);
lean_inc_ref(v_fileName_2899_);
v_fileMap_2900_ = lean_ctor_get(v_a_2896_, 1);
lean_inc_ref(v_fileMap_2900_);
v_options_2901_ = lean_ctor_get(v_a_2896_, 2);
lean_inc_ref(v_options_2901_);
v_currRecDepth_2902_ = lean_ctor_get(v_a_2896_, 3);
lean_inc(v_currRecDepth_2902_);
v_maxRecDepth_2903_ = lean_ctor_get(v_a_2896_, 4);
lean_inc(v_maxRecDepth_2903_);
v_ref_2904_ = lean_ctor_get(v_a_2896_, 5);
lean_inc(v_ref_2904_);
v_currNamespace_2905_ = lean_ctor_get(v_a_2896_, 6);
lean_inc(v_currNamespace_2905_);
v_openDecls_2906_ = lean_ctor_get(v_a_2896_, 7);
lean_inc(v_openDecls_2906_);
v_initHeartbeats_2907_ = lean_ctor_get(v_a_2896_, 8);
lean_inc(v_initHeartbeats_2907_);
v_maxHeartbeats_2908_ = lean_ctor_get(v_a_2896_, 9);
lean_inc(v_maxHeartbeats_2908_);
v_quotContext_2909_ = lean_ctor_get(v_a_2896_, 10);
lean_inc(v_quotContext_2909_);
v_currMacroScope_2910_ = lean_ctor_get(v_a_2896_, 11);
lean_inc(v_currMacroScope_2910_);
v_diag_2911_ = lean_ctor_get_uint8(v_a_2896_, sizeof(void*)*14);
v_cancelTk_x3f_2912_ = lean_ctor_get(v_a_2896_, 12);
lean_inc(v_cancelTk_x3f_2912_);
v_suppressElabErrors_2913_ = lean_ctor_get_uint8(v_a_2896_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2914_ = lean_ctor_get(v_a_2896_, 13);
lean_inc_ref(v_inheritedTraceOptions_2914_);
lean_dec_ref(v_a_2896_);
v___x_2915_ = lean_nat_dec_eq(v_currRecDepth_2902_, v_maxRecDepth_2903_);
if (v___x_2915_ == 0)
{
lean_object* v_p_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v_p_2916_ = lean_ctor_get(v_c_u2082_2886_, 0);
v___x_2917_ = lean_unsigned_to_nat(1u);
v___x_2918_ = lean_nat_add(v_currRecDepth_2902_, v___x_2917_);
lean_dec(v_currRecDepth_2902_);
v___x_2919_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2919_, 0, v_fileName_2899_);
lean_ctor_set(v___x_2919_, 1, v_fileMap_2900_);
lean_ctor_set(v___x_2919_, 2, v_options_2901_);
lean_ctor_set(v___x_2919_, 3, v___x_2918_);
lean_ctor_set(v___x_2919_, 4, v_maxRecDepth_2903_);
lean_ctor_set(v___x_2919_, 5, v_ref_2904_);
lean_ctor_set(v___x_2919_, 6, v_currNamespace_2905_);
lean_ctor_set(v___x_2919_, 7, v_openDecls_2906_);
lean_ctor_set(v___x_2919_, 8, v_initHeartbeats_2907_);
lean_ctor_set(v___x_2919_, 9, v_maxHeartbeats_2908_);
lean_ctor_set(v___x_2919_, 10, v_quotContext_2909_);
lean_ctor_set(v___x_2919_, 11, v_currMacroScope_2910_);
lean_ctor_set(v___x_2919_, 12, v_cancelTk_x3f_2912_);
lean_ctor_set(v___x_2919_, 13, v_inheritedTraceOptions_2914_);
lean_ctor_set_uint8(v___x_2919_, sizeof(void*)*14, v_diag_2911_);
lean_ctor_set_uint8(v___x_2919_, sizeof(void*)*14 + 1, v_suppressElabErrors_2913_);
v___x_2920_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2916_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v___x_2919_, v_a_2897_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2958_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2923_ = v___x_2920_;
v_isShared_2924_ = v_isSharedCheck_2958_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2920_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2958_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
if (lean_obj_tag(v_a_2921_) == 1)
{
lean_object* v_val_2925_; lean_object* v_snd_2926_; lean_object* v_snd_2927_; lean_object* v_fst_2928_; lean_object* v_fst_2929_; lean_object* v_p_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
lean_del_object(v___x_2923_);
v_val_2925_ = lean_ctor_get(v_a_2921_, 0);
lean_inc(v_val_2925_);
lean_dec_ref(v_a_2921_);
v_snd_2926_ = lean_ctor_get(v_val_2925_, 1);
lean_inc(v_snd_2926_);
v_snd_2927_ = lean_ctor_get(v_snd_2926_, 1);
lean_inc(v_snd_2927_);
v_fst_2928_ = lean_ctor_get(v_val_2925_, 0);
lean_inc(v_fst_2928_);
lean_dec(v_val_2925_);
v_fst_2929_ = lean_ctor_get(v_snd_2926_, 0);
lean_inc(v_fst_2929_);
lean_dec(v_snd_2926_);
v_p_2930_ = lean_ctor_get(v_snd_2927_, 0);
v___x_2931_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2930_, v_fst_2929_);
lean_inc_ref(v_c_u2082_2886_);
v___x_2932_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v___x_2931_, v_fst_2929_, v_snd_2927_, v_fst_2928_, v_c_u2082_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v___x_2919_, v_a_2897_);
lean_dec(v_fst_2929_);
lean_dec(v___x_2931_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2933_);
lean_dec_ref(v___x_2932_);
if (lean_obj_tag(v_a_2933_) == 1)
{
lean_object* v_val_2934_; 
lean_dec_ref(v_c_u2082_2886_);
v_val_2934_ = lean_ctor_get(v_a_2933_, 0);
lean_inc(v_val_2934_);
lean_dec_ref(v_a_2933_);
v_c_u2082_2886_ = v_val_2934_;
v_a_2896_ = v___x_2919_;
goto _start;
}
else
{
lean_object* v___x_2936_; 
lean_dec(v_a_2933_);
v___x_2936_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_u2082_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v___x_2919_, v_a_2897_);
lean_dec_ref(v___x_2919_);
lean_dec_ref(v_c_u2082_2886_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2944_; 
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2944_ == 0)
{
lean_object* v_unused_2945_; 
v_unused_2945_ = lean_ctor_get(v___x_2936_, 0);
lean_dec(v_unused_2945_);
v___x_2938_ = v___x_2936_;
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
else
{
lean_dec(v___x_2936_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2940_; lean_object* v___x_2942_; 
v___x_2940_ = lean_box(0);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v___x_2940_);
v___x_2942_ = v___x_2938_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2940_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
v_a_2946_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2936_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2936_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2919_);
lean_dec_ref(v_c_u2082_2886_);
return v___x_2932_;
}
}
else
{
lean_object* v___x_2954_; lean_object* v___x_2956_; 
lean_dec(v_a_2921_);
lean_dec_ref(v___x_2919_);
v___x_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2954_, 0, v_c_u2082_2886_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 0, v___x_2954_);
v___x_2956_ = v___x_2923_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2954_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
else
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
lean_dec_ref(v___x_2919_);
lean_dec_ref(v_c_u2082_2886_);
v_a_2959_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2920_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2920_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2959_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
else
{
lean_object* v___x_2967_; 
lean_dec_ref(v_inheritedTraceOptions_2914_);
lean_dec(v_cancelTk_x3f_2912_);
lean_dec(v_currMacroScope_2910_);
lean_dec(v_quotContext_2909_);
lean_dec(v_maxHeartbeats_2908_);
lean_dec(v_initHeartbeats_2907_);
lean_dec(v_openDecls_2906_);
lean_dec(v_currNamespace_2905_);
lean_dec(v_maxRecDepth_2903_);
lean_dec(v_currRecDepth_2902_);
lean_dec_ref(v_options_2901_);
lean_dec_ref(v_fileMap_2900_);
lean_dec_ref(v_fileName_2899_);
lean_dec_ref(v_c_u2082_2886_);
v___x_2967_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_2904_);
return v___x_2967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object* v_c_u2082_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_u2082_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
lean_dec(v_a_2979_);
lean_dec(v_a_2977_);
lean_dec_ref(v_a_2976_);
lean_dec(v_a_2975_);
lean_dec_ref(v_a_2974_);
lean_dec(v_a_2973_);
lean_dec_ref(v_a_2972_);
lean_dec(v_a_2971_);
lean_dec(v_a_2970_);
lean_dec(v_a_2969_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(lean_object* v_val_2982_, lean_object* v_x_2983_, size_t v_x_2984_, size_t v_x_2985_){
_start:
{
if (lean_obj_tag(v_x_2983_) == 0)
{
lean_object* v_cs_2986_; size_t v_j_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; 
v_cs_2986_ = lean_ctor_get(v_x_2983_, 0);
v_j_2987_ = lean_usize_shift_right(v_x_2984_, v_x_2985_);
v___x_2988_ = lean_usize_to_nat(v_j_2987_);
v___x_2989_ = lean_array_get_size(v_cs_2986_);
v___x_2990_ = lean_nat_dec_lt(v___x_2988_, v___x_2989_);
if (v___x_2990_ == 0)
{
lean_dec(v___x_2988_);
lean_dec_ref(v_val_2982_);
return v_x_2983_;
}
else
{
lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3008_; 
lean_inc_ref(v_cs_2986_);
v_isSharedCheck_3008_ = !lean_is_exclusive(v_x_2983_);
if (v_isSharedCheck_3008_ == 0)
{
lean_object* v_unused_3009_; 
v_unused_3009_ = lean_ctor_get(v_x_2983_, 0);
lean_dec(v_unused_3009_);
v___x_2992_ = v_x_2983_;
v_isShared_2993_ = v_isSharedCheck_3008_;
goto v_resetjp_2991_;
}
else
{
lean_dec(v_x_2983_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3008_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
size_t v___x_2994_; size_t v___x_2995_; size_t v___x_2996_; size_t v_i_2997_; size_t v___x_2998_; size_t v_shift_2999_; lean_object* v_v_3000_; lean_object* v___x_3001_; lean_object* v_xs_x27_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3006_; 
v___x_2994_ = ((size_t)1ULL);
v___x_2995_ = lean_usize_shift_left(v___x_2994_, v_x_2985_);
v___x_2996_ = lean_usize_sub(v___x_2995_, v___x_2994_);
v_i_2997_ = lean_usize_land(v_x_2984_, v___x_2996_);
v___x_2998_ = ((size_t)5ULL);
v_shift_2999_ = lean_usize_sub(v_x_2985_, v___x_2998_);
v_v_3000_ = lean_array_fget(v_cs_2986_, v___x_2988_);
v___x_3001_ = lean_box(0);
v_xs_x27_3002_ = lean_array_fset(v_cs_2986_, v___x_2988_, v___x_3001_);
v___x_3003_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(v_val_2982_, v_v_3000_, v_i_2997_, v_shift_2999_);
v___x_3004_ = lean_array_fset(v_xs_x27_3002_, v___x_2988_, v___x_3003_);
lean_dec(v___x_2988_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v___x_3004_);
v___x_3006_ = v___x_2992_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_3004_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
else
{
lean_object* v_vs_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; 
v_vs_3010_ = lean_ctor_get(v_x_2983_, 0);
v___x_3011_ = lean_usize_to_nat(v_x_2984_);
v___x_3012_ = lean_array_get_size(v_vs_3010_);
v___x_3013_ = lean_nat_dec_lt(v___x_3011_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_dec(v___x_3011_);
lean_dec_ref(v_val_2982_);
return v_x_2983_;
}
else
{
lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3025_; 
lean_inc_ref(v_vs_3010_);
v_isSharedCheck_3025_ = !lean_is_exclusive(v_x_2983_);
if (v_isSharedCheck_3025_ == 0)
{
lean_object* v_unused_3026_; 
v_unused_3026_ = lean_ctor_get(v_x_2983_, 0);
lean_dec(v_unused_3026_);
v___x_3015_ = v_x_2983_;
v_isShared_3016_ = v_isSharedCheck_3025_;
goto v_resetjp_3014_;
}
else
{
lean_dec(v_x_2983_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3025_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v_v_3017_; lean_object* v___x_3018_; lean_object* v_xs_x27_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3023_; 
v_v_3017_ = lean_array_fget(v_vs_3010_, v___x_3011_);
v___x_3018_ = lean_box(0);
v_xs_x27_3019_ = lean_array_fset(v_vs_3010_, v___x_3011_, v___x_3018_);
v___x_3020_ = l_Lean_PersistentArray_push___redArg(v_v_3017_, v_val_2982_);
v___x_3021_ = lean_array_fset(v_xs_x27_3019_, v___x_3011_, v___x_3020_);
lean_dec(v___x_3011_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v___x_3021_);
v___x_3023_ = v___x_3015_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg___boxed(lean_object* v_val_3027_, lean_object* v_x_3028_, lean_object* v_x_3029_, lean_object* v_x_3030_){
_start:
{
size_t v_x_39031__boxed_3031_; size_t v_x_39032__boxed_3032_; lean_object* v_res_3033_; 
v_x_39031__boxed_3031_ = lean_unbox_usize(v_x_3029_);
lean_dec(v_x_3029_);
v_x_39032__boxed_3032_ = lean_unbox_usize(v_x_3030_);
lean_dec(v_x_3030_);
v_res_3033_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(v_val_3027_, v_x_3028_, v_x_39031__boxed_3031_, v_x_39032__boxed_3032_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object* v_val_3034_, lean_object* v_inst_3035_, lean_object* v_t_3036_, lean_object* v_i_3037_){
_start:
{
lean_object* v_root_3038_; lean_object* v_tail_3039_; lean_object* v_size_3040_; size_t v_shift_3041_; lean_object* v_tailOff_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3066_; 
v_root_3038_ = lean_ctor_get(v_t_3036_, 0);
v_tail_3039_ = lean_ctor_get(v_t_3036_, 1);
v_size_3040_ = lean_ctor_get(v_t_3036_, 2);
v_shift_3041_ = lean_ctor_get_usize(v_t_3036_, 4);
v_tailOff_3042_ = lean_ctor_get(v_t_3036_, 3);
v_isSharedCheck_3066_ = !lean_is_exclusive(v_t_3036_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3044_ = v_t_3036_;
v_isShared_3045_ = v_isSharedCheck_3066_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_tailOff_3042_);
lean_inc(v_size_3040_);
lean_inc(v_tail_3039_);
lean_inc(v_root_3038_);
lean_dec(v_t_3036_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3066_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
uint8_t v___x_3046_; 
v___x_3046_ = lean_nat_dec_le(v_tailOff_3042_, v_i_3037_);
if (v___x_3046_ == 0)
{
size_t v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3050_; 
v___x_3047_ = lean_usize_of_nat(v_i_3037_);
v___x_3048_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(v_val_3034_, v_root_3038_, v___x_3047_, v_shift_3041_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 0, v___x_3048_);
v___x_3050_ = v___x_3044_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3048_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v_tail_3039_);
lean_ctor_set(v_reuseFailAlloc_3051_, 2, v_size_3040_);
lean_ctor_set(v_reuseFailAlloc_3051_, 3, v_tailOff_3042_);
lean_ctor_set_usize(v_reuseFailAlloc_3051_, 4, v_shift_3041_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
else
{
lean_object* v___x_3052_; lean_object* v___x_3053_; uint8_t v___x_3054_; 
v___x_3052_ = lean_nat_sub(v_i_3037_, v_tailOff_3042_);
v___x_3053_ = lean_array_get_size(v_tail_3039_);
v___x_3054_ = lean_nat_dec_lt(v___x_3052_, v___x_3053_);
if (v___x_3054_ == 0)
{
lean_object* v___x_3056_; 
lean_dec(v___x_3052_);
lean_dec_ref(v_val_3034_);
if (v_isShared_3045_ == 0)
{
v___x_3056_ = v___x_3044_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_root_3038_);
lean_ctor_set(v_reuseFailAlloc_3057_, 1, v_tail_3039_);
lean_ctor_set(v_reuseFailAlloc_3057_, 2, v_size_3040_);
lean_ctor_set(v_reuseFailAlloc_3057_, 3, v_tailOff_3042_);
lean_ctor_set_usize(v_reuseFailAlloc_3057_, 4, v_shift_3041_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
else
{
lean_object* v_v_3058_; lean_object* v___x_3059_; lean_object* v_xs_x27_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3064_; 
v_v_3058_ = lean_array_fget(v_tail_3039_, v___x_3052_);
v___x_3059_ = lean_box(0);
v_xs_x27_3060_ = lean_array_fset(v_tail_3039_, v___x_3052_, v___x_3059_);
v___x_3061_ = l_Lean_PersistentArray_push___redArg(v_v_3058_, v_val_3034_);
v___x_3062_ = lean_array_fset(v_xs_x27_3060_, v___x_3052_, v___x_3061_);
lean_dec(v___x_3052_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 1, v___x_3062_);
v___x_3064_ = v___x_3044_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_root_3038_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v___x_3062_);
lean_ctor_set(v_reuseFailAlloc_3065_, 2, v_size_3040_);
lean_ctor_set(v_reuseFailAlloc_3065_, 3, v_tailOff_3042_);
lean_ctor_set_usize(v_reuseFailAlloc_3065_, 4, v_shift_3041_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object* v_val_3067_, lean_object* v_inst_3068_, lean_object* v_t_3069_, lean_object* v_i_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3067_, v_inst_3068_, v_t_3069_, v_i_3070_);
lean_dec(v_i_3070_);
lean_dec_ref(v_inst_3068_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(lean_object* v___y_3072_, lean_object* v_val_3073_, lean_object* v___x_3074_, lean_object* v_v_3075_, lean_object* v_s_3076_){
_start:
{
lean_object* v_structs_3077_; lean_object* v_typeIdOf_3078_; lean_object* v_exprToStructId_3079_; lean_object* v_exprToStructIdEntries_3080_; lean_object* v_forbiddenNatModules_3081_; lean_object* v_natStructs_3082_; lean_object* v_natTypeIdOf_3083_; lean_object* v_exprToNatStructId_3084_; lean_object* v___x_3085_; uint8_t v___x_3086_; 
v_structs_3077_ = lean_ctor_get(v_s_3076_, 0);
v_typeIdOf_3078_ = lean_ctor_get(v_s_3076_, 1);
v_exprToStructId_3079_ = lean_ctor_get(v_s_3076_, 2);
v_exprToStructIdEntries_3080_ = lean_ctor_get(v_s_3076_, 3);
v_forbiddenNatModules_3081_ = lean_ctor_get(v_s_3076_, 4);
v_natStructs_3082_ = lean_ctor_get(v_s_3076_, 5);
v_natTypeIdOf_3083_ = lean_ctor_get(v_s_3076_, 6);
v_exprToNatStructId_3084_ = lean_ctor_get(v_s_3076_, 7);
v___x_3085_ = lean_array_get_size(v_structs_3077_);
v___x_3086_ = lean_nat_dec_lt(v___y_3072_, v___x_3085_);
if (v___x_3086_ == 0)
{
lean_dec_ref(v_val_3073_);
return v_s_3076_;
}
else
{
lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3148_; 
lean_inc_ref(v_exprToNatStructId_3084_);
lean_inc_ref(v_natTypeIdOf_3083_);
lean_inc_ref(v_natStructs_3082_);
lean_inc_ref(v_forbiddenNatModules_3081_);
lean_inc_ref(v_exprToStructIdEntries_3080_);
lean_inc_ref(v_exprToStructId_3079_);
lean_inc_ref(v_typeIdOf_3078_);
lean_inc_ref(v_structs_3077_);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_s_3076_);
if (v_isSharedCheck_3148_ == 0)
{
lean_object* v_unused_3149_; lean_object* v_unused_3150_; lean_object* v_unused_3151_; lean_object* v_unused_3152_; lean_object* v_unused_3153_; lean_object* v_unused_3154_; lean_object* v_unused_3155_; lean_object* v_unused_3156_; 
v_unused_3149_ = lean_ctor_get(v_s_3076_, 7);
lean_dec(v_unused_3149_);
v_unused_3150_ = lean_ctor_get(v_s_3076_, 6);
lean_dec(v_unused_3150_);
v_unused_3151_ = lean_ctor_get(v_s_3076_, 5);
lean_dec(v_unused_3151_);
v_unused_3152_ = lean_ctor_get(v_s_3076_, 4);
lean_dec(v_unused_3152_);
v_unused_3153_ = lean_ctor_get(v_s_3076_, 3);
lean_dec(v_unused_3153_);
v_unused_3154_ = lean_ctor_get(v_s_3076_, 2);
lean_dec(v_unused_3154_);
v_unused_3155_ = lean_ctor_get(v_s_3076_, 1);
lean_dec(v_unused_3155_);
v_unused_3156_ = lean_ctor_get(v_s_3076_, 0);
lean_dec(v_unused_3156_);
v___x_3088_ = v_s_3076_;
v_isShared_3089_ = v_isSharedCheck_3148_;
goto v_resetjp_3087_;
}
else
{
lean_dec(v_s_3076_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3148_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v_v_3090_; lean_object* v_id_3091_; lean_object* v_ringId_x3f_3092_; lean_object* v_type_3093_; lean_object* v_u_3094_; lean_object* v_intModuleInst_3095_; lean_object* v_leInst_x3f_3096_; lean_object* v_ltInst_x3f_3097_; lean_object* v_lawfulOrderLTInst_x3f_3098_; lean_object* v_isPreorderInst_x3f_3099_; lean_object* v_orderedAddInst_x3f_3100_; lean_object* v_isLinearInst_x3f_3101_; lean_object* v_noNatDivInst_x3f_3102_; lean_object* v_ringInst_x3f_3103_; lean_object* v_commRingInst_x3f_3104_; lean_object* v_orderedRingInst_x3f_3105_; lean_object* v_fieldInst_x3f_3106_; lean_object* v_charInst_x3f_3107_; lean_object* v_zero_3108_; lean_object* v_ofNatZero_3109_; lean_object* v_one_x3f_3110_; lean_object* v_leFn_x3f_3111_; lean_object* v_ltFn_x3f_3112_; lean_object* v_addFn_3113_; lean_object* v_zsmulFn_3114_; lean_object* v_nsmulFn_3115_; lean_object* v_zsmulFn_x3f_3116_; lean_object* v_nsmulFn_x3f_3117_; lean_object* v_homomulFn_x3f_3118_; lean_object* v_subFn_3119_; lean_object* v_negFn_3120_; lean_object* v_vars_3121_; lean_object* v_varMap_3122_; lean_object* v_lowers_3123_; lean_object* v_uppers_3124_; lean_object* v_diseqs_3125_; lean_object* v_assignment_3126_; uint8_t v_caseSplits_3127_; lean_object* v_conflict_x3f_3128_; lean_object* v_diseqSplits_3129_; lean_object* v_elimEqs_3130_; lean_object* v_elimStack_3131_; lean_object* v_occurs_3132_; lean_object* v_ignored_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3147_; 
v_v_3090_ = lean_array_fget(v_structs_3077_, v___y_3072_);
v_id_3091_ = lean_ctor_get(v_v_3090_, 0);
v_ringId_x3f_3092_ = lean_ctor_get(v_v_3090_, 1);
v_type_3093_ = lean_ctor_get(v_v_3090_, 2);
v_u_3094_ = lean_ctor_get(v_v_3090_, 3);
v_intModuleInst_3095_ = lean_ctor_get(v_v_3090_, 4);
v_leInst_x3f_3096_ = lean_ctor_get(v_v_3090_, 5);
v_ltInst_x3f_3097_ = lean_ctor_get(v_v_3090_, 6);
v_lawfulOrderLTInst_x3f_3098_ = lean_ctor_get(v_v_3090_, 7);
v_isPreorderInst_x3f_3099_ = lean_ctor_get(v_v_3090_, 8);
v_orderedAddInst_x3f_3100_ = lean_ctor_get(v_v_3090_, 9);
v_isLinearInst_x3f_3101_ = lean_ctor_get(v_v_3090_, 10);
v_noNatDivInst_x3f_3102_ = lean_ctor_get(v_v_3090_, 11);
v_ringInst_x3f_3103_ = lean_ctor_get(v_v_3090_, 12);
v_commRingInst_x3f_3104_ = lean_ctor_get(v_v_3090_, 13);
v_orderedRingInst_x3f_3105_ = lean_ctor_get(v_v_3090_, 14);
v_fieldInst_x3f_3106_ = lean_ctor_get(v_v_3090_, 15);
v_charInst_x3f_3107_ = lean_ctor_get(v_v_3090_, 16);
v_zero_3108_ = lean_ctor_get(v_v_3090_, 17);
v_ofNatZero_3109_ = lean_ctor_get(v_v_3090_, 18);
v_one_x3f_3110_ = lean_ctor_get(v_v_3090_, 19);
v_leFn_x3f_3111_ = lean_ctor_get(v_v_3090_, 20);
v_ltFn_x3f_3112_ = lean_ctor_get(v_v_3090_, 21);
v_addFn_3113_ = lean_ctor_get(v_v_3090_, 22);
v_zsmulFn_3114_ = lean_ctor_get(v_v_3090_, 23);
v_nsmulFn_3115_ = lean_ctor_get(v_v_3090_, 24);
v_zsmulFn_x3f_3116_ = lean_ctor_get(v_v_3090_, 25);
v_nsmulFn_x3f_3117_ = lean_ctor_get(v_v_3090_, 26);
v_homomulFn_x3f_3118_ = lean_ctor_get(v_v_3090_, 27);
v_subFn_3119_ = lean_ctor_get(v_v_3090_, 28);
v_negFn_3120_ = lean_ctor_get(v_v_3090_, 29);
v_vars_3121_ = lean_ctor_get(v_v_3090_, 30);
v_varMap_3122_ = lean_ctor_get(v_v_3090_, 31);
v_lowers_3123_ = lean_ctor_get(v_v_3090_, 32);
v_uppers_3124_ = lean_ctor_get(v_v_3090_, 33);
v_diseqs_3125_ = lean_ctor_get(v_v_3090_, 34);
v_assignment_3126_ = lean_ctor_get(v_v_3090_, 35);
v_caseSplits_3127_ = lean_ctor_get_uint8(v_v_3090_, sizeof(void*)*42);
v_conflict_x3f_3128_ = lean_ctor_get(v_v_3090_, 36);
v_diseqSplits_3129_ = lean_ctor_get(v_v_3090_, 37);
v_elimEqs_3130_ = lean_ctor_get(v_v_3090_, 38);
v_elimStack_3131_ = lean_ctor_get(v_v_3090_, 39);
v_occurs_3132_ = lean_ctor_get(v_v_3090_, 40);
v_ignored_3133_ = lean_ctor_get(v_v_3090_, 41);
v_isSharedCheck_3147_ = !lean_is_exclusive(v_v_3090_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3135_ = v_v_3090_;
v_isShared_3136_ = v_isSharedCheck_3147_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_ignored_3133_);
lean_inc(v_occurs_3132_);
lean_inc(v_elimStack_3131_);
lean_inc(v_elimEqs_3130_);
lean_inc(v_diseqSplits_3129_);
lean_inc(v_conflict_x3f_3128_);
lean_inc(v_assignment_3126_);
lean_inc(v_diseqs_3125_);
lean_inc(v_uppers_3124_);
lean_inc(v_lowers_3123_);
lean_inc(v_varMap_3122_);
lean_inc(v_vars_3121_);
lean_inc(v_negFn_3120_);
lean_inc(v_subFn_3119_);
lean_inc(v_homomulFn_x3f_3118_);
lean_inc(v_nsmulFn_x3f_3117_);
lean_inc(v_zsmulFn_x3f_3116_);
lean_inc(v_nsmulFn_3115_);
lean_inc(v_zsmulFn_3114_);
lean_inc(v_addFn_3113_);
lean_inc(v_ltFn_x3f_3112_);
lean_inc(v_leFn_x3f_3111_);
lean_inc(v_one_x3f_3110_);
lean_inc(v_ofNatZero_3109_);
lean_inc(v_zero_3108_);
lean_inc(v_charInst_x3f_3107_);
lean_inc(v_fieldInst_x3f_3106_);
lean_inc(v_orderedRingInst_x3f_3105_);
lean_inc(v_commRingInst_x3f_3104_);
lean_inc(v_ringInst_x3f_3103_);
lean_inc(v_noNatDivInst_x3f_3102_);
lean_inc(v_isLinearInst_x3f_3101_);
lean_inc(v_orderedAddInst_x3f_3100_);
lean_inc(v_isPreorderInst_x3f_3099_);
lean_inc(v_lawfulOrderLTInst_x3f_3098_);
lean_inc(v_ltInst_x3f_3097_);
lean_inc(v_leInst_x3f_3096_);
lean_inc(v_intModuleInst_3095_);
lean_inc(v_u_3094_);
lean_inc(v_type_3093_);
lean_inc(v_ringId_x3f_3092_);
lean_inc(v_id_3091_);
lean_dec(v_v_3090_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3147_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3137_; lean_object* v_xs_x27_3138_; lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3137_ = lean_box(0);
v_xs_x27_3138_ = lean_array_fset(v_structs_3077_, v___y_3072_, v___x_3137_);
v___x_3139_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3073_, v___x_3074_, v_diseqs_3125_, v_v_3075_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 34, v___x_3139_);
v___x_3141_ = v___x_3135_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_id_3091_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v_ringId_x3f_3092_);
lean_ctor_set(v_reuseFailAlloc_3146_, 2, v_type_3093_);
lean_ctor_set(v_reuseFailAlloc_3146_, 3, v_u_3094_);
lean_ctor_set(v_reuseFailAlloc_3146_, 4, v_intModuleInst_3095_);
lean_ctor_set(v_reuseFailAlloc_3146_, 5, v_leInst_x3f_3096_);
lean_ctor_set(v_reuseFailAlloc_3146_, 6, v_ltInst_x3f_3097_);
lean_ctor_set(v_reuseFailAlloc_3146_, 7, v_lawfulOrderLTInst_x3f_3098_);
lean_ctor_set(v_reuseFailAlloc_3146_, 8, v_isPreorderInst_x3f_3099_);
lean_ctor_set(v_reuseFailAlloc_3146_, 9, v_orderedAddInst_x3f_3100_);
lean_ctor_set(v_reuseFailAlloc_3146_, 10, v_isLinearInst_x3f_3101_);
lean_ctor_set(v_reuseFailAlloc_3146_, 11, v_noNatDivInst_x3f_3102_);
lean_ctor_set(v_reuseFailAlloc_3146_, 12, v_ringInst_x3f_3103_);
lean_ctor_set(v_reuseFailAlloc_3146_, 13, v_commRingInst_x3f_3104_);
lean_ctor_set(v_reuseFailAlloc_3146_, 14, v_orderedRingInst_x3f_3105_);
lean_ctor_set(v_reuseFailAlloc_3146_, 15, v_fieldInst_x3f_3106_);
lean_ctor_set(v_reuseFailAlloc_3146_, 16, v_charInst_x3f_3107_);
lean_ctor_set(v_reuseFailAlloc_3146_, 17, v_zero_3108_);
lean_ctor_set(v_reuseFailAlloc_3146_, 18, v_ofNatZero_3109_);
lean_ctor_set(v_reuseFailAlloc_3146_, 19, v_one_x3f_3110_);
lean_ctor_set(v_reuseFailAlloc_3146_, 20, v_leFn_x3f_3111_);
lean_ctor_set(v_reuseFailAlloc_3146_, 21, v_ltFn_x3f_3112_);
lean_ctor_set(v_reuseFailAlloc_3146_, 22, v_addFn_3113_);
lean_ctor_set(v_reuseFailAlloc_3146_, 23, v_zsmulFn_3114_);
lean_ctor_set(v_reuseFailAlloc_3146_, 24, v_nsmulFn_3115_);
lean_ctor_set(v_reuseFailAlloc_3146_, 25, v_zsmulFn_x3f_3116_);
lean_ctor_set(v_reuseFailAlloc_3146_, 26, v_nsmulFn_x3f_3117_);
lean_ctor_set(v_reuseFailAlloc_3146_, 27, v_homomulFn_x3f_3118_);
lean_ctor_set(v_reuseFailAlloc_3146_, 28, v_subFn_3119_);
lean_ctor_set(v_reuseFailAlloc_3146_, 29, v_negFn_3120_);
lean_ctor_set(v_reuseFailAlloc_3146_, 30, v_vars_3121_);
lean_ctor_set(v_reuseFailAlloc_3146_, 31, v_varMap_3122_);
lean_ctor_set(v_reuseFailAlloc_3146_, 32, v_lowers_3123_);
lean_ctor_set(v_reuseFailAlloc_3146_, 33, v_uppers_3124_);
lean_ctor_set(v_reuseFailAlloc_3146_, 34, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3146_, 35, v_assignment_3126_);
lean_ctor_set(v_reuseFailAlloc_3146_, 36, v_conflict_x3f_3128_);
lean_ctor_set(v_reuseFailAlloc_3146_, 37, v_diseqSplits_3129_);
lean_ctor_set(v_reuseFailAlloc_3146_, 38, v_elimEqs_3130_);
lean_ctor_set(v_reuseFailAlloc_3146_, 39, v_elimStack_3131_);
lean_ctor_set(v_reuseFailAlloc_3146_, 40, v_occurs_3132_);
lean_ctor_set(v_reuseFailAlloc_3146_, 41, v_ignored_3133_);
lean_ctor_set_uint8(v_reuseFailAlloc_3146_, sizeof(void*)*42, v_caseSplits_3127_);
v___x_3141_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3142_; lean_object* v___x_3144_; 
v___x_3142_ = lean_array_fset(v_xs_x27_3138_, v___y_3072_, v___x_3141_);
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 0, v___x_3142_);
v___x_3144_ = v___x_3088_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3142_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_typeIdOf_3078_);
lean_ctor_set(v_reuseFailAlloc_3145_, 2, v_exprToStructId_3079_);
lean_ctor_set(v_reuseFailAlloc_3145_, 3, v_exprToStructIdEntries_3080_);
lean_ctor_set(v_reuseFailAlloc_3145_, 4, v_forbiddenNatModules_3081_);
lean_ctor_set(v_reuseFailAlloc_3145_, 5, v_natStructs_3082_);
lean_ctor_set(v_reuseFailAlloc_3145_, 6, v_natTypeIdOf_3083_);
lean_ctor_set(v_reuseFailAlloc_3145_, 7, v_exprToNatStructId_3084_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed(lean_object* v___y_3157_, lean_object* v_val_3158_, lean_object* v___x_3159_, lean_object* v_v_3160_, lean_object* v_s_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(v___y_3157_, v_val_3158_, v___x_3159_, v_v_3160_, v_s_3161_);
lean_dec(v_v_3160_);
lean_dec_ref(v___x_3159_);
lean_dec(v___y_3157_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object* v_c_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v_cls_3206_; lean_object* v___x_3207_; lean_object* v_a_3208_; lean_object* v___x_3209_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; uint8_t v___x_3318_; 
v_cls_3206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0));
v___x_3207_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v_cls_3206_, v_a_3188_);
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_a_3208_);
lean_dec_ref(v___x_3207_);
v___x_3209_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_3318_ = lean_unbox(v_a_3208_);
lean_dec(v_a_3208_);
if (v___x_3318_ == 0)
{
v___y_3254_ = v_a_3179_;
v___y_3255_ = v_a_3180_;
v___y_3256_ = v_a_3181_;
v___y_3257_ = v_a_3182_;
v___y_3258_ = v_a_3183_;
v___y_3259_ = v_a_3184_;
v___y_3260_ = v_a_3185_;
v___y_3261_ = v_a_3186_;
v___y_3262_ = v_a_3187_;
v___y_3263_ = v_a_3188_;
v___y_3264_ = v_a_3189_;
goto v___jp_3253_;
}
else
{
lean_object* v___x_3319_; 
v___x_3319_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_a_3320_);
lean_dec_ref(v___x_3319_);
v___x_3321_ = l_Lean_MessageData_ofExpr(v_a_3320_);
v___x_3322_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_3206_, v___x_3321_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_dec_ref(v___x_3322_);
v___y_3254_ = v_a_3179_;
v___y_3255_ = v_a_3180_;
v___y_3256_ = v_a_3181_;
v___y_3257_ = v_a_3182_;
v___y_3258_ = v_a_3183_;
v___y_3259_ = v_a_3184_;
v___y_3260_ = v_a_3185_;
v___y_3261_ = v_a_3186_;
v___y_3262_ = v_a_3187_;
v___y_3263_ = v_a_3188_;
v___y_3264_ = v_a_3189_;
goto v___jp_3253_;
}
else
{
lean_dec_ref(v_c_3178_);
return v___x_3322_;
}
}
else
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
lean_dec_ref(v_c_3178_);
v_a_3323_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3319_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3319_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
v___jp_3191_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3204_, 0, v___y_3192_);
v___x_3205_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(v___x_3204_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
return v___x_3205_;
}
v___jp_3210_:
{
lean_object* v___x_3227_; 
v___x_3227_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v___f_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
lean_dec_ref(v___x_3227_);
lean_inc(v___y_3216_);
v___f_3228_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3228_, 0, v___y_3216_);
lean_closure_set(v___f_3228_, 1, v___y_3212_);
lean_closure_set(v___f_3228_, 2, v___x_3209_);
lean_closure_set(v___f_3228_, 3, v___y_3211_);
v___x_3229_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3230_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3229_, v___f_3228_, v___y_3217_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v___x_3231_; 
lean_dec_ref(v___x_3230_);
v___x_3231_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v___y_3214_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3244_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3234_ = v___x_3231_;
v_isShared_3235_ = v_isSharedCheck_3244_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3244_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
uint8_t v___x_3236_; uint8_t v___x_3237_; uint8_t v___x_3238_; 
v___x_3236_ = 0;
v___x_3237_ = lean_unbox(v_a_3232_);
lean_dec(v_a_3232_);
v___x_3238_ = l_Lean_instBEqLBool_beq(v___x_3237_, v___x_3236_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; lean_object* v___x_3241_; 
lean_dec(v___y_3213_);
v___x_3239_ = lean_box(0);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v___x_3239_);
v___x_3241_ = v___x_3234_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3239_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
else
{
lean_object* v___x_3243_; 
lean_del_object(v___x_3234_);
v___x_3243_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_3213_, v___y_3216_, v___y_3217_);
return v___x_3243_;
}
}
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec(v___y_3213_);
v_a_3245_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3231_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3231_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
else
{
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
return v___x_3230_;
}
}
else
{
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
return v___x_3227_;
}
}
v___jp_3253_:
{
lean_object* v___x_3265_; 
lean_inc_ref(v___y_3263_);
v___x_3265_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_3178_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3309_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3268_ = v___x_3265_;
v_isShared_3269_ = v_isSharedCheck_3309_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3265_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3309_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
if (lean_obj_tag(v_a_3266_) == 1)
{
lean_object* v_val_3270_; lean_object* v_p_3271_; 
lean_del_object(v___x_3268_);
v_val_3270_ = lean_ctor_get(v_a_3266_, 0);
lean_inc(v_val_3270_);
lean_dec_ref(v_a_3266_);
v_p_3271_ = lean_ctor_get(v_val_3270_, 0);
if (lean_obj_tag(v_p_3271_) == 0)
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v_a_3274_; uint8_t v___x_3275_; 
v___x_3272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2));
v___x_3273_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_3272_, v___y_3263_);
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_a_3274_);
lean_dec_ref(v___x_3273_);
v___x_3275_ = lean_unbox(v_a_3274_);
lean_dec(v_a_3274_);
if (v___x_3275_ == 0)
{
v___y_3192_ = v_val_3270_;
v___y_3193_ = v___y_3254_;
v___y_3194_ = v___y_3255_;
v___y_3195_ = v___y_3256_;
v___y_3196_ = v___y_3257_;
v___y_3197_ = v___y_3258_;
v___y_3198_ = v___y_3259_;
v___y_3199_ = v___y_3260_;
v___y_3200_ = v___y_3261_;
v___y_3201_ = v___y_3262_;
v___y_3202_ = v___y_3263_;
v___y_3203_ = v___y_3264_;
goto v___jp_3191_;
}
else
{
lean_object* v___x_3276_; 
v___x_3276_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3270_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref(v___x_3276_);
v___x_3278_ = l_Lean_MessageData_ofExpr(v_a_3277_);
v___x_3279_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_3272_, v___x_3278_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_dec_ref(v___x_3279_);
v___y_3192_ = v_val_3270_;
v___y_3193_ = v___y_3254_;
v___y_3194_ = v___y_3255_;
v___y_3195_ = v___y_3256_;
v___y_3196_ = v___y_3257_;
v___y_3197_ = v___y_3258_;
v___y_3198_ = v___y_3259_;
v___y_3199_ = v___y_3260_;
v___y_3200_ = v___y_3261_;
v___y_3201_ = v___y_3262_;
v___y_3202_ = v___y_3263_;
v___y_3203_ = v___y_3264_;
goto v___jp_3191_;
}
else
{
lean_dec(v_val_3270_);
return v___x_3279_;
}
}
else
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_dec(v_val_3270_);
v_a_3280_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3276_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3276_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
}
else
{
lean_object* v_v_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v_a_3291_; uint8_t v___x_3292_; 
lean_inc_ref(v_p_3271_);
v_v_3288_ = lean_ctor_get(v_p_3271_, 1);
lean_inc(v_v_3288_);
v___x_3289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3290_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_3289_, v___y_3263_);
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
lean_inc(v_a_3291_);
lean_dec_ref(v___x_3290_);
v___x_3292_ = lean_unbox(v_a_3291_);
lean_dec(v_a_3291_);
if (v___x_3292_ == 0)
{
lean_inc(v_val_3270_);
lean_inc(v_v_3288_);
v___y_3211_ = v_v_3288_;
v___y_3212_ = v_val_3270_;
v___y_3213_ = v_v_3288_;
v___y_3214_ = v_val_3270_;
v___y_3215_ = v_p_3271_;
v___y_3216_ = v___y_3254_;
v___y_3217_ = v___y_3255_;
v___y_3218_ = v___y_3256_;
v___y_3219_ = v___y_3257_;
v___y_3220_ = v___y_3258_;
v___y_3221_ = v___y_3259_;
v___y_3222_ = v___y_3260_;
v___y_3223_ = v___y_3261_;
v___y_3224_ = v___y_3262_;
v___y_3225_ = v___y_3263_;
v___y_3226_ = v___y_3264_;
goto v___jp_3210_;
}
else
{
lean_object* v___x_3293_; 
v___x_3293_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3270_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_a_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc(v_a_3294_);
lean_dec_ref(v___x_3293_);
v___x_3295_ = l_Lean_MessageData_ofExpr(v_a_3294_);
v___x_3296_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_3289_, v___x_3295_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_dec_ref(v___x_3296_);
lean_inc(v_val_3270_);
lean_inc(v_v_3288_);
v___y_3211_ = v_v_3288_;
v___y_3212_ = v_val_3270_;
v___y_3213_ = v_v_3288_;
v___y_3214_ = v_val_3270_;
v___y_3215_ = v_p_3271_;
v___y_3216_ = v___y_3254_;
v___y_3217_ = v___y_3255_;
v___y_3218_ = v___y_3256_;
v___y_3219_ = v___y_3257_;
v___y_3220_ = v___y_3258_;
v___y_3221_ = v___y_3259_;
v___y_3222_ = v___y_3260_;
v___y_3223_ = v___y_3261_;
v___y_3224_ = v___y_3262_;
v___y_3225_ = v___y_3263_;
v___y_3226_ = v___y_3264_;
goto v___jp_3210_;
}
else
{
lean_dec_ref(v_p_3271_);
lean_dec(v_v_3288_);
lean_dec(v_val_3270_);
return v___x_3296_;
}
}
else
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
lean_dec(v_v_3288_);
lean_dec_ref(v_p_3271_);
lean_dec(v_val_3270_);
v_a_3297_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3293_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3293_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
}
}
else
{
lean_object* v___x_3305_; lean_object* v___x_3307_; 
lean_dec(v_a_3266_);
v___x_3305_ = lean_box(0);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 0, v___x_3305_);
v___x_3307_ = v___x_3268_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v___x_3305_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
else
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3317_; 
v_a_3310_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3312_ = v___x_3265_;
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3265_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3315_; 
if (v_isShared_3313_ == 0)
{
v___x_3315_ = v___x_3312_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3310_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___boxed(lean_object* v_c_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_c_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_);
lean_dec(v_a_3342_);
lean_dec_ref(v_a_3341_);
lean_dec(v_a_3340_);
lean_dec_ref(v_a_3339_);
lean_dec(v_a_3338_);
lean_dec_ref(v_a_3337_);
lean_dec(v_a_3336_);
lean_dec_ref(v_a_3335_);
lean_dec(v_a_3334_);
lean_dec(v_a_3333_);
lean_dec(v_a_3332_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object* v_val_3345_, lean_object* v_inst_3346_, lean_object* v_x_3347_, size_t v_x_3348_, size_t v_x_3349_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(v_val_3345_, v_x_3347_, v_x_3348_, v_x_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_val_3351_, lean_object* v_inst_3352_, lean_object* v_x_3353_, lean_object* v_x_3354_, lean_object* v_x_3355_){
_start:
{
size_t v_x_39575__boxed_3356_; size_t v_x_39576__boxed_3357_; lean_object* v_res_3358_; 
v_x_39575__boxed_3356_ = lean_unbox_usize(v_x_3354_);
lean_dec(v_x_3354_);
v_x_39576__boxed_3357_ = lean_unbox_usize(v_x_3355_);
lean_dec(v_x_3355_);
v_res_3358_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_3351_, v_inst_3352_, v_x_3353_, v_x_39575__boxed_3356_, v_x_39576__boxed_3357_);
lean_dec_ref(v_inst_3352_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_3359_, lean_object* v_as_3360_, size_t v_sz_3361_, size_t v_i_3362_, lean_object* v_b_3363_){
_start:
{
uint8_t v___x_3364_; 
v___x_3364_ = lean_usize_dec_lt(v_i_3362_, v_sz_3361_);
if (v___x_3364_ == 0)
{
return v_b_3363_;
}
else
{
lean_object* v_snd_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3406_; 
v_snd_3365_ = lean_ctor_get(v_b_3363_, 1);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_b_3363_);
if (v_isSharedCheck_3406_ == 0)
{
lean_object* v_unused_3407_; 
v_unused_3407_ = lean_ctor_get(v_b_3363_, 0);
lean_dec(v_unused_3407_);
v___x_3367_ = v_b_3363_;
v_isShared_3368_ = v_isSharedCheck_3406_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_snd_3365_);
lean_dec(v_b_3363_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3406_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v_fst_3369_; lean_object* v_snd_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3405_; 
v_fst_3369_ = lean_ctor_get(v_snd_3365_, 0);
v_snd_3370_ = lean_ctor_get(v_snd_3365_, 1);
v_isSharedCheck_3405_ = !lean_is_exclusive(v_snd_3365_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3372_ = v_snd_3365_;
v_isShared_3373_ = v_isSharedCheck_3405_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_snd_3370_);
lean_inc(v_fst_3369_);
lean_dec(v_snd_3365_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3405_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v_a_3374_; lean_object* v_p_3375_; lean_object* v___x_3376_; lean_object* v_a_3378_; lean_object* v_b_3385_; lean_object* v___x_3386_; uint8_t v___x_3387_; 
v_a_3374_ = lean_array_uget(v_as_3360_, v_i_3362_);
v_p_3375_ = lean_ctor_get(v_a_3374_, 0);
v___x_3376_ = lean_box(0);
v_b_3385_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3375_, v_x_3359_);
v___x_3386_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3387_ = lean_int_dec_eq(v_b_3385_, v___x_3386_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3389_; 
lean_inc(v_a_3374_);
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 1, v_a_3374_);
lean_ctor_set(v___x_3367_, 0, v_b_3385_);
v___x_3389_ = v___x_3367_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_b_3385_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v_a_3374_);
v___x_3389_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3397_; 
v_isSharedCheck_3397_ = !lean_is_exclusive(v_a_3374_);
if (v_isSharedCheck_3397_ == 0)
{
lean_object* v_unused_3398_; lean_object* v_unused_3399_; 
v_unused_3398_ = lean_ctor_get(v_a_3374_, 1);
lean_dec(v_unused_3398_);
v_unused_3399_ = lean_ctor_get(v_a_3374_, 0);
lean_dec(v_unused_3399_);
v___x_3391_ = v_a_3374_;
v_isShared_3392_ = v_isSharedCheck_3397_;
goto v_resetjp_3390_;
}
else
{
lean_dec(v_a_3374_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3397_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v_todo_3393_; lean_object* v___x_3395_; 
v_todo_3393_ = lean_array_push(v_snd_3370_, v___x_3389_);
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 1, v_todo_3393_);
lean_ctor_set(v___x_3391_, 0, v_fst_3369_);
v___x_3395_ = v___x_3391_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_fst_3369_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v_todo_3393_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
v_a_3378_ = v___x_3395_;
goto v___jp_3377_;
}
}
}
}
else
{
lean_object* v_cs_x27_3401_; lean_object* v___x_3403_; 
lean_dec(v_b_3385_);
v_cs_x27_3401_ = l_Lean_PersistentArray_push___redArg(v_fst_3369_, v_a_3374_);
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 1, v_snd_3370_);
lean_ctor_set(v___x_3367_, 0, v_cs_x27_3401_);
v___x_3403_ = v___x_3367_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_cs_x27_3401_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v_snd_3370_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
v_a_3378_ = v___x_3403_;
goto v___jp_3377_;
}
}
v___jp_3377_:
{
lean_object* v___x_3380_; 
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 1, v_a_3378_);
lean_ctor_set(v___x_3372_, 0, v___x_3376_);
v___x_3380_ = v___x_3372_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3376_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v_a_3378_);
v___x_3380_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
size_t v___x_3381_; size_t v___x_3382_; 
v___x_3381_ = ((size_t)1ULL);
v___x_3382_ = lean_usize_add(v_i_3362_, v___x_3381_);
v_i_3362_ = v___x_3382_;
v_b_3363_ = v___x_3380_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_3408_, lean_object* v_as_3409_, lean_object* v_sz_3410_, lean_object* v_i_3411_, lean_object* v_b_3412_){
_start:
{
size_t v_sz_boxed_3413_; size_t v_i_boxed_3414_; lean_object* v_res_3415_; 
v_sz_boxed_3413_ = lean_unbox_usize(v_sz_3410_);
lean_dec(v_sz_3410_);
v_i_boxed_3414_ = lean_unbox_usize(v_i_3411_);
lean_dec(v_i_3411_);
v_res_3415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3408_, v_as_3409_, v_sz_boxed_3413_, v_i_boxed_3414_, v_b_3412_);
lean_dec_ref(v_as_3409_);
lean_dec(v_x_3408_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(lean_object* v_x_3416_, lean_object* v_as_3417_, size_t v_sz_3418_, size_t v_i_3419_, lean_object* v_b_3420_){
_start:
{
uint8_t v___x_3421_; 
v___x_3421_ = lean_usize_dec_lt(v_i_3419_, v_sz_3418_);
if (v___x_3421_ == 0)
{
return v_b_3420_;
}
else
{
lean_object* v_snd_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3463_; 
v_snd_3422_ = lean_ctor_get(v_b_3420_, 1);
v_isSharedCheck_3463_ = !lean_is_exclusive(v_b_3420_);
if (v_isSharedCheck_3463_ == 0)
{
lean_object* v_unused_3464_; 
v_unused_3464_ = lean_ctor_get(v_b_3420_, 0);
lean_dec(v_unused_3464_);
v___x_3424_ = v_b_3420_;
v_isShared_3425_ = v_isSharedCheck_3463_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_snd_3422_);
lean_dec(v_b_3420_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3463_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v_fst_3426_; lean_object* v_snd_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3462_; 
v_fst_3426_ = lean_ctor_get(v_snd_3422_, 0);
v_snd_3427_ = lean_ctor_get(v_snd_3422_, 1);
v_isSharedCheck_3462_ = !lean_is_exclusive(v_snd_3422_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3429_ = v_snd_3422_;
v_isShared_3430_ = v_isSharedCheck_3462_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_snd_3427_);
lean_inc(v_fst_3426_);
lean_dec(v_snd_3422_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3462_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v_a_3431_; lean_object* v_p_3432_; lean_object* v___x_3433_; lean_object* v_a_3435_; lean_object* v_b_3442_; lean_object* v___x_3443_; uint8_t v___x_3444_; 
v_a_3431_ = lean_array_uget(v_as_3417_, v_i_3419_);
v_p_3432_ = lean_ctor_get(v_a_3431_, 0);
v___x_3433_ = lean_box(0);
v_b_3442_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3432_, v_x_3416_);
v___x_3443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3444_ = lean_int_dec_eq(v_b_3442_, v___x_3443_);
if (v___x_3444_ == 0)
{
lean_object* v___x_3446_; 
lean_inc(v_a_3431_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 1, v_a_3431_);
lean_ctor_set(v___x_3424_, 0, v_b_3442_);
v___x_3446_ = v___x_3424_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_b_3442_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_a_3431_);
v___x_3446_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3454_; 
v_isSharedCheck_3454_ = !lean_is_exclusive(v_a_3431_);
if (v_isSharedCheck_3454_ == 0)
{
lean_object* v_unused_3455_; lean_object* v_unused_3456_; 
v_unused_3455_ = lean_ctor_get(v_a_3431_, 1);
lean_dec(v_unused_3455_);
v_unused_3456_ = lean_ctor_get(v_a_3431_, 0);
lean_dec(v_unused_3456_);
v___x_3448_ = v_a_3431_;
v_isShared_3449_ = v_isSharedCheck_3454_;
goto v_resetjp_3447_;
}
else
{
lean_dec(v_a_3431_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3454_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v_todo_3450_; lean_object* v___x_3452_; 
v_todo_3450_ = lean_array_push(v_snd_3427_, v___x_3446_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 1, v_todo_3450_);
lean_ctor_set(v___x_3448_, 0, v_fst_3426_);
v___x_3452_ = v___x_3448_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_fst_3426_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_todo_3450_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
v_a_3435_ = v___x_3452_;
goto v___jp_3434_;
}
}
}
}
else
{
lean_object* v_cs_x27_3458_; lean_object* v___x_3460_; 
lean_dec(v_b_3442_);
v_cs_x27_3458_ = l_Lean_PersistentArray_push___redArg(v_fst_3426_, v_a_3431_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 1, v_snd_3427_);
lean_ctor_set(v___x_3424_, 0, v_cs_x27_3458_);
v___x_3460_ = v___x_3424_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_cs_x27_3458_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_snd_3427_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
v_a_3435_ = v___x_3460_;
goto v___jp_3434_;
}
}
v___jp_3434_:
{
lean_object* v___x_3437_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 1, v_a_3435_);
lean_ctor_set(v___x_3429_, 0, v___x_3433_);
v___x_3437_ = v___x_3429_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3433_);
lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_a_3435_);
v___x_3437_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
size_t v___x_3438_; size_t v___x_3439_; lean_object* v___x_3440_; 
v___x_3438_ = ((size_t)1ULL);
v___x_3439_ = lean_usize_add(v_i_3419_, v___x_3438_);
v___x_3440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3416_, v_as_3417_, v_sz_3418_, v___x_3439_, v___x_3437_);
return v___x_3440_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_3465_, lean_object* v_as_3466_, lean_object* v_sz_3467_, lean_object* v_i_3468_, lean_object* v_b_3469_){
_start:
{
size_t v_sz_boxed_3470_; size_t v_i_boxed_3471_; lean_object* v_res_3472_; 
v_sz_boxed_3470_ = lean_unbox_usize(v_sz_3467_);
lean_dec(v_sz_3467_);
v_i_boxed_3471_ = lean_unbox_usize(v_i_3468_);
lean_dec(v_i_3468_);
v_res_3472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3465_, v_as_3466_, v_sz_boxed_3470_, v_i_boxed_3471_, v_b_3469_);
lean_dec_ref(v_as_3466_);
lean_dec(v_x_3465_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_3473_, lean_object* v_as_3474_, size_t v_sz_3475_, size_t v_i_3476_, lean_object* v_b_3477_){
_start:
{
uint8_t v___x_3478_; 
v___x_3478_ = lean_usize_dec_lt(v_i_3476_, v_sz_3475_);
if (v___x_3478_ == 0)
{
return v_b_3477_;
}
else
{
lean_object* v_snd_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3520_; 
v_snd_3479_ = lean_ctor_get(v_b_3477_, 1);
v_isSharedCheck_3520_ = !lean_is_exclusive(v_b_3477_);
if (v_isSharedCheck_3520_ == 0)
{
lean_object* v_unused_3521_; 
v_unused_3521_ = lean_ctor_get(v_b_3477_, 0);
lean_dec(v_unused_3521_);
v___x_3481_ = v_b_3477_;
v_isShared_3482_ = v_isSharedCheck_3520_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_snd_3479_);
lean_dec(v_b_3477_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3520_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v_fst_3483_; lean_object* v_snd_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3519_; 
v_fst_3483_ = lean_ctor_get(v_snd_3479_, 0);
v_snd_3484_ = lean_ctor_get(v_snd_3479_, 1);
v_isSharedCheck_3519_ = !lean_is_exclusive(v_snd_3479_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3486_ = v_snd_3479_;
v_isShared_3487_ = v_isSharedCheck_3519_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_snd_3484_);
lean_inc(v_fst_3483_);
lean_dec(v_snd_3479_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3519_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v_a_3488_; lean_object* v_p_3489_; lean_object* v___x_3490_; lean_object* v_a_3492_; lean_object* v_b_3499_; lean_object* v___x_3500_; uint8_t v___x_3501_; 
v_a_3488_ = lean_array_uget(v_as_3474_, v_i_3476_);
v_p_3489_ = lean_ctor_get(v_a_3488_, 0);
v___x_3490_ = lean_box(0);
v_b_3499_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3489_, v_x_3473_);
v___x_3500_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3501_ = lean_int_dec_eq(v_b_3499_, v___x_3500_);
if (v___x_3501_ == 0)
{
lean_object* v___x_3503_; 
lean_inc(v_a_3488_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 1, v_a_3488_);
lean_ctor_set(v___x_3481_, 0, v_b_3499_);
v___x_3503_ = v___x_3481_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_b_3499_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v_a_3488_);
v___x_3503_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3511_; 
v_isSharedCheck_3511_ = !lean_is_exclusive(v_a_3488_);
if (v_isSharedCheck_3511_ == 0)
{
lean_object* v_unused_3512_; lean_object* v_unused_3513_; 
v_unused_3512_ = lean_ctor_get(v_a_3488_, 1);
lean_dec(v_unused_3512_);
v_unused_3513_ = lean_ctor_get(v_a_3488_, 0);
lean_dec(v_unused_3513_);
v___x_3505_ = v_a_3488_;
v_isShared_3506_ = v_isSharedCheck_3511_;
goto v_resetjp_3504_;
}
else
{
lean_dec(v_a_3488_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3511_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v_todo_3507_; lean_object* v___x_3509_; 
v_todo_3507_ = lean_array_push(v_snd_3484_, v___x_3503_);
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 1, v_todo_3507_);
lean_ctor_set(v___x_3505_, 0, v_fst_3483_);
v___x_3509_ = v___x_3505_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_fst_3483_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v_todo_3507_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
v_a_3492_ = v___x_3509_;
goto v___jp_3491_;
}
}
}
}
else
{
lean_object* v_cs_x27_3515_; lean_object* v___x_3517_; 
lean_dec(v_b_3499_);
v_cs_x27_3515_ = l_Lean_PersistentArray_push___redArg(v_fst_3483_, v_a_3488_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 1, v_snd_3484_);
lean_ctor_set(v___x_3481_, 0, v_cs_x27_3515_);
v___x_3517_ = v___x_3481_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_cs_x27_3515_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v_snd_3484_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
v_a_3492_ = v___x_3517_;
goto v___jp_3491_;
}
}
v___jp_3491_:
{
lean_object* v___x_3494_; 
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 1, v_a_3492_);
lean_ctor_set(v___x_3486_, 0, v___x_3490_);
v___x_3494_ = v___x_3486_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3490_);
lean_ctor_set(v_reuseFailAlloc_3498_, 1, v_a_3492_);
v___x_3494_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
size_t v___x_3495_; size_t v___x_3496_; 
v___x_3495_ = ((size_t)1ULL);
v___x_3496_ = lean_usize_add(v_i_3476_, v___x_3495_);
v_i_3476_ = v___x_3496_;
v_b_3477_ = v___x_3494_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3522_, lean_object* v_as_3523_, lean_object* v_sz_3524_, lean_object* v_i_3525_, lean_object* v_b_3526_){
_start:
{
size_t v_sz_boxed_3527_; size_t v_i_boxed_3528_; lean_object* v_res_3529_; 
v_sz_boxed_3527_ = lean_unbox_usize(v_sz_3524_);
lean_dec(v_sz_3524_);
v_i_boxed_3528_ = lean_unbox_usize(v_i_3525_);
lean_dec(v_i_3525_);
v_res_3529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3522_, v_as_3523_, v_sz_boxed_3527_, v_i_boxed_3528_, v_b_3526_);
lean_dec_ref(v_as_3523_);
lean_dec(v_x_3522_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_3530_, lean_object* v_as_3531_, size_t v_sz_3532_, size_t v_i_3533_, lean_object* v_b_3534_){
_start:
{
uint8_t v___x_3535_; 
v___x_3535_ = lean_usize_dec_lt(v_i_3533_, v_sz_3532_);
if (v___x_3535_ == 0)
{
return v_b_3534_;
}
else
{
lean_object* v_snd_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3577_; 
v_snd_3536_ = lean_ctor_get(v_b_3534_, 1);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_b_3534_);
if (v_isSharedCheck_3577_ == 0)
{
lean_object* v_unused_3578_; 
v_unused_3578_ = lean_ctor_get(v_b_3534_, 0);
lean_dec(v_unused_3578_);
v___x_3538_ = v_b_3534_;
v_isShared_3539_ = v_isSharedCheck_3577_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_snd_3536_);
lean_dec(v_b_3534_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3577_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v_fst_3540_; lean_object* v_snd_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3576_; 
v_fst_3540_ = lean_ctor_get(v_snd_3536_, 0);
v_snd_3541_ = lean_ctor_get(v_snd_3536_, 1);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_snd_3536_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3543_ = v_snd_3536_;
v_isShared_3544_ = v_isSharedCheck_3576_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_snd_3541_);
lean_inc(v_fst_3540_);
lean_dec(v_snd_3536_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3576_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v_a_3545_; lean_object* v_p_3546_; lean_object* v___x_3547_; lean_object* v_a_3549_; lean_object* v_b_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; 
v_a_3545_ = lean_array_uget(v_as_3531_, v_i_3533_);
v_p_3546_ = lean_ctor_get(v_a_3545_, 0);
v___x_3547_ = lean_box(0);
v_b_3556_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3546_, v_x_3530_);
v___x_3557_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3558_ = lean_int_dec_eq(v_b_3556_, v___x_3557_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3560_; 
lean_inc(v_a_3545_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 1, v_a_3545_);
lean_ctor_set(v___x_3538_, 0, v_b_3556_);
v___x_3560_ = v___x_3538_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_b_3556_);
lean_ctor_set(v_reuseFailAlloc_3571_, 1, v_a_3545_);
v___x_3560_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3568_; 
v_isSharedCheck_3568_ = !lean_is_exclusive(v_a_3545_);
if (v_isSharedCheck_3568_ == 0)
{
lean_object* v_unused_3569_; lean_object* v_unused_3570_; 
v_unused_3569_ = lean_ctor_get(v_a_3545_, 1);
lean_dec(v_unused_3569_);
v_unused_3570_ = lean_ctor_get(v_a_3545_, 0);
lean_dec(v_unused_3570_);
v___x_3562_ = v_a_3545_;
v_isShared_3563_ = v_isSharedCheck_3568_;
goto v_resetjp_3561_;
}
else
{
lean_dec(v_a_3545_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3568_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v_todo_3564_; lean_object* v___x_3566_; 
v_todo_3564_ = lean_array_push(v_snd_3541_, v___x_3560_);
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 1, v_todo_3564_);
lean_ctor_set(v___x_3562_, 0, v_fst_3540_);
v___x_3566_ = v___x_3562_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_fst_3540_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v_todo_3564_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
v_a_3549_ = v___x_3566_;
goto v___jp_3548_;
}
}
}
}
else
{
lean_object* v_cs_x27_3572_; lean_object* v___x_3574_; 
lean_dec(v_b_3556_);
v_cs_x27_3572_ = l_Lean_PersistentArray_push___redArg(v_fst_3540_, v_a_3545_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 1, v_snd_3541_);
lean_ctor_set(v___x_3538_, 0, v_cs_x27_3572_);
v___x_3574_ = v___x_3538_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_cs_x27_3572_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v_snd_3541_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
v_a_3549_ = v___x_3574_;
goto v___jp_3548_;
}
}
v___jp_3548_:
{
lean_object* v___x_3551_; 
if (v_isShared_3544_ == 0)
{
lean_ctor_set(v___x_3543_, 1, v_a_3549_);
lean_ctor_set(v___x_3543_, 0, v___x_3547_);
v___x_3551_ = v___x_3543_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3547_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v_a_3549_);
v___x_3551_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
size_t v___x_3552_; size_t v___x_3553_; lean_object* v___x_3554_; 
v___x_3552_ = ((size_t)1ULL);
v___x_3553_ = lean_usize_add(v_i_3533_, v___x_3552_);
v___x_3554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3530_, v_as_3531_, v_sz_3532_, v___x_3553_, v___x_3551_);
return v___x_3554_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_3579_, lean_object* v_as_3580_, lean_object* v_sz_3581_, lean_object* v_i_3582_, lean_object* v_b_3583_){
_start:
{
size_t v_sz_boxed_3584_; size_t v_i_boxed_3585_; lean_object* v_res_3586_; 
v_sz_boxed_3584_ = lean_unbox_usize(v_sz_3581_);
lean_dec(v_sz_3581_);
v_i_boxed_3585_ = lean_unbox_usize(v_i_3582_);
lean_dec(v_i_3582_);
v_res_3586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3579_, v_as_3580_, v_sz_boxed_3584_, v_i_boxed_3585_, v_b_3583_);
lean_dec_ref(v_as_3580_);
lean_dec(v_x_3579_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(lean_object* v_x_3587_, lean_object* v_inh_3588_, lean_object* v_n_3589_, lean_object* v_b_3590_){
_start:
{
if (lean_obj_tag(v_n_3589_) == 0)
{
lean_object* v_cs_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3606_; 
v_cs_3591_ = lean_ctor_get(v_n_3589_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v_n_3589_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3593_ = v_n_3589_;
v_isShared_3594_ = v_isSharedCheck_3606_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_cs_3591_);
lean_dec(v_n_3589_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3606_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; size_t v_sz_3597_; size_t v___x_3598_; lean_object* v___x_3599_; lean_object* v_fst_3600_; 
v___x_3595_ = lean_box(0);
v___x_3596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3595_);
lean_ctor_set(v___x_3596_, 1, v_b_3590_);
v_sz_3597_ = lean_array_size(v_cs_3591_);
v___x_3598_ = ((size_t)0ULL);
v___x_3599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_x_3587_, v_inh_3588_, v_cs_3591_, v_sz_3597_, v___x_3598_, v___x_3596_);
lean_dec_ref(v_cs_3591_);
v_fst_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_fst_3600_);
if (lean_obj_tag(v_fst_3600_) == 0)
{
lean_object* v_snd_3601_; lean_object* v___x_3603_; 
v_snd_3601_ = lean_ctor_get(v___x_3599_, 1);
lean_inc(v_snd_3601_);
lean_dec_ref(v___x_3599_);
if (v_isShared_3594_ == 0)
{
lean_ctor_set_tag(v___x_3593_, 1);
lean_ctor_set(v___x_3593_, 0, v_snd_3601_);
v___x_3603_ = v___x_3593_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_snd_3601_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
else
{
lean_object* v_val_3605_; 
lean_dec_ref(v___x_3599_);
lean_del_object(v___x_3593_);
v_val_3605_ = lean_ctor_get(v_fst_3600_, 0);
lean_inc(v_val_3605_);
lean_dec_ref(v_fst_3600_);
return v_val_3605_;
}
}
}
else
{
lean_object* v_vs_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3622_; 
v_vs_3607_ = lean_ctor_get(v_n_3589_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v_n_3589_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3609_ = v_n_3589_;
v_isShared_3610_ = v_isSharedCheck_3622_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_vs_3607_);
lean_dec(v_n_3589_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3622_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; size_t v_sz_3613_; size_t v___x_3614_; lean_object* v___x_3615_; lean_object* v_fst_3616_; 
v___x_3611_ = lean_box(0);
v___x_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3611_);
lean_ctor_set(v___x_3612_, 1, v_b_3590_);
v_sz_3613_ = lean_array_size(v_vs_3607_);
v___x_3614_ = ((size_t)0ULL);
v___x_3615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3587_, v_vs_3607_, v_sz_3613_, v___x_3614_, v___x_3612_);
lean_dec_ref(v_vs_3607_);
v_fst_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_fst_3616_);
if (lean_obj_tag(v_fst_3616_) == 0)
{
lean_object* v_snd_3617_; lean_object* v___x_3619_; 
v_snd_3617_ = lean_ctor_get(v___x_3615_, 1);
lean_inc(v_snd_3617_);
lean_dec_ref(v___x_3615_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 0, v_snd_3617_);
v___x_3619_ = v___x_3609_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_snd_3617_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
else
{
lean_object* v_val_3621_; 
lean_dec_ref(v___x_3615_);
lean_del_object(v___x_3609_);
v_val_3621_ = lean_ctor_get(v_fst_3616_, 0);
lean_inc(v_val_3621_);
lean_dec_ref(v_fst_3616_);
return v_val_3621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_3623_, lean_object* v_inh_3624_, lean_object* v_as_3625_, size_t v_sz_3626_, size_t v_i_3627_, lean_object* v_b_3628_){
_start:
{
uint8_t v___x_3629_; 
v___x_3629_ = lean_usize_dec_lt(v_i_3627_, v_sz_3626_);
if (v___x_3629_ == 0)
{
return v_b_3628_;
}
else
{
lean_object* v_snd_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3648_; 
v_snd_3630_ = lean_ctor_get(v_b_3628_, 1);
v_isSharedCheck_3648_ = !lean_is_exclusive(v_b_3628_);
if (v_isSharedCheck_3648_ == 0)
{
lean_object* v_unused_3649_; 
v_unused_3649_ = lean_ctor_get(v_b_3628_, 0);
lean_dec(v_unused_3649_);
v___x_3632_ = v_b_3628_;
v_isShared_3633_ = v_isSharedCheck_3648_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_snd_3630_);
lean_dec(v_b_3628_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3648_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v_a_3634_; lean_object* v___x_3635_; 
v_a_3634_ = lean_array_uget_borrowed(v_as_3625_, v_i_3627_);
lean_inc(v_snd_3630_);
lean_inc(v_a_3634_);
v___x_3635_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_x_3623_, v_inh_3624_, v_a_3634_, v_snd_3630_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_object* v___x_3636_; lean_object* v___x_3638_; 
v___x_3636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3635_);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 0, v___x_3636_);
v___x_3638_ = v___x_3632_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3636_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v_snd_3630_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
else
{
lean_object* v_a_3640_; lean_object* v___x_3641_; lean_object* v___x_3643_; 
lean_dec(v_snd_3630_);
v_a_3640_ = lean_ctor_get(v___x_3635_, 0);
lean_inc(v_a_3640_);
lean_dec_ref(v___x_3635_);
v___x_3641_ = lean_box(0);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 1, v_a_3640_);
lean_ctor_set(v___x_3632_, 0, v___x_3641_);
v___x_3643_ = v___x_3632_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3641_);
lean_ctor_set(v_reuseFailAlloc_3647_, 1, v_a_3640_);
v___x_3643_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
size_t v___x_3644_; size_t v___x_3645_; 
v___x_3644_ = ((size_t)1ULL);
v___x_3645_ = lean_usize_add(v_i_3627_, v___x_3644_);
v_i_3627_ = v___x_3645_;
v_b_3628_ = v___x_3643_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_x_3650_, lean_object* v_inh_3651_, lean_object* v_as_3652_, lean_object* v_sz_3653_, lean_object* v_i_3654_, lean_object* v_b_3655_){
_start:
{
size_t v_sz_boxed_3656_; size_t v_i_boxed_3657_; lean_object* v_res_3658_; 
v_sz_boxed_3656_ = lean_unbox_usize(v_sz_3653_);
lean_dec(v_sz_3653_);
v_i_boxed_3657_ = lean_unbox_usize(v_i_3654_);
lean_dec(v_i_3654_);
v_res_3658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_x_3650_, v_inh_3651_, v_as_3652_, v_sz_boxed_3656_, v_i_boxed_3657_, v_b_3655_);
lean_dec_ref(v_as_3652_);
lean_dec_ref(v_inh_3651_);
lean_dec(v_x_3650_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3659_, lean_object* v_inh_3660_, lean_object* v_n_3661_, lean_object* v_b_3662_){
_start:
{
lean_object* v_res_3663_; 
v_res_3663_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_x_3659_, v_inh_3660_, v_n_3661_, v_b_3662_);
lean_dec_ref(v_inh_3660_);
lean_dec(v_x_3659_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object* v_x_3664_, lean_object* v_t_3665_, lean_object* v_init_3666_){
_start:
{
lean_object* v_root_3667_; lean_object* v_tail_3668_; lean_object* v___x_3669_; 
v_root_3667_ = lean_ctor_get(v_t_3665_, 0);
lean_inc_ref(v_root_3667_);
v_tail_3668_ = lean_ctor_get(v_t_3665_, 1);
lean_inc_ref(v_tail_3668_);
lean_dec_ref(v_t_3665_);
lean_inc_ref(v_init_3666_);
v___x_3669_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_x_3664_, v_init_3666_, v_root_3667_, v_init_3666_);
lean_dec_ref(v_init_3666_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; 
lean_dec_ref(v_tail_3668_);
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3670_);
lean_dec_ref(v___x_3669_);
return v_a_3670_;
}
else
{
lean_object* v_a_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; size_t v_sz_3674_; size_t v___x_3675_; lean_object* v___x_3676_; lean_object* v_fst_3677_; 
v_a_3671_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3671_);
lean_dec_ref(v___x_3669_);
v___x_3672_ = lean_box(0);
v___x_3673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3672_);
lean_ctor_set(v___x_3673_, 1, v_a_3671_);
v_sz_3674_ = lean_array_size(v_tail_3668_);
v___x_3675_ = ((size_t)0ULL);
v___x_3676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3664_, v_tail_3668_, v_sz_3674_, v___x_3675_, v___x_3673_);
lean_dec_ref(v_tail_3668_);
v_fst_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_fst_3677_);
if (lean_obj_tag(v_fst_3677_) == 0)
{
lean_object* v_snd_3678_; 
v_snd_3678_ = lean_ctor_get(v___x_3676_, 1);
lean_inc(v_snd_3678_);
lean_dec_ref(v___x_3676_);
return v_snd_3678_;
}
else
{
lean_object* v_val_3679_; 
lean_dec_ref(v___x_3676_);
v_val_3679_ = lean_ctor_get(v_fst_3677_, 0);
lean_inc(v_val_3679_);
lean_dec_ref(v_fst_3677_);
return v_val_3679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object* v_x_3680_, lean_object* v_t_3681_, lean_object* v_init_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3680_, v_t_3681_, v_init_3682_);
lean_dec(v_x_3680_);
return v_res_3683_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3684_ = lean_unsigned_to_nat(32u);
v___x_3685_ = lean_mk_empty_array_with_capacity(v___x_3684_);
v___x_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3685_);
return v___x_3686_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1(void){
_start:
{
size_t v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v_cs_x27_3692_; 
v___x_3687_ = ((size_t)5ULL);
v___x_3688_ = lean_unsigned_to_nat(0u);
v___x_3689_ = lean_unsigned_to_nat(32u);
v___x_3690_ = lean_mk_empty_array_with_capacity(v___x_3689_);
v___x_3691_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0);
v_cs_x27_3692_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_3692_, 0, v___x_3691_);
lean_ctor_set(v_cs_x27_3692_, 1, v___x_3690_);
lean_ctor_set(v_cs_x27_3692_, 2, v___x_3688_);
lean_ctor_set(v_cs_x27_3692_, 3, v___x_3688_);
lean_ctor_set_usize(v_cs_x27_3692_, 4, v___x_3687_);
return v_cs_x27_3692_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_3695_; lean_object* v_cs_x27_3696_; lean_object* v___x_3697_; 
v_todo_3695_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2));
v_cs_x27_3696_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1);
v___x_3697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3697_, 0, v_cs_x27_3696_);
lean_ctor_set(v___x_3697_, 1, v_todo_3695_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object* v_x_3698_, lean_object* v_cs_3699_){
_start:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v_fst_3702_; lean_object* v_snd_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
v___x_3700_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3);
v___x_3701_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3698_, v_cs_3699_, v___x_3700_);
v_fst_3702_ = lean_ctor_get(v___x_3701_, 0);
v_snd_3703_ = lean_ctor_get(v___x_3701_, 1);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3701_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_snd_3703_);
lean_inc(v_fst_3702_);
lean_dec(v___x_3701_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_fst_3702_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v_snd_3703_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object* v_x_3711_, lean_object* v_cs_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3711_, v_cs_3712_);
lean_dec(v_x_3711_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object* v_x_3714_, lean_object* v_cs_3715_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3714_, v_cs_3715_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object* v_x_3717_, lean_object* v_cs_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(v_x_3717_, v_cs_3718_);
lean_dec(v_x_3717_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(lean_object* v_a_3720_, lean_object* v_y_3721_, lean_object* v_fst_3722_, lean_object* v_s_3723_){
_start:
{
lean_object* v_structs_3724_; lean_object* v_typeIdOf_3725_; lean_object* v_exprToStructId_3726_; lean_object* v_exprToStructIdEntries_3727_; lean_object* v_forbiddenNatModules_3728_; lean_object* v_natStructs_3729_; lean_object* v_natTypeIdOf_3730_; lean_object* v_exprToNatStructId_3731_; lean_object* v___x_3732_; uint8_t v___x_3733_; 
v_structs_3724_ = lean_ctor_get(v_s_3723_, 0);
v_typeIdOf_3725_ = lean_ctor_get(v_s_3723_, 1);
v_exprToStructId_3726_ = lean_ctor_get(v_s_3723_, 2);
v_exprToStructIdEntries_3727_ = lean_ctor_get(v_s_3723_, 3);
v_forbiddenNatModules_3728_ = lean_ctor_get(v_s_3723_, 4);
v_natStructs_3729_ = lean_ctor_get(v_s_3723_, 5);
v_natTypeIdOf_3730_ = lean_ctor_get(v_s_3723_, 6);
v_exprToNatStructId_3731_ = lean_ctor_get(v_s_3723_, 7);
v___x_3732_ = lean_array_get_size(v_structs_3724_);
v___x_3733_ = lean_nat_dec_lt(v_a_3720_, v___x_3732_);
if (v___x_3733_ == 0)
{
lean_dec_ref(v_fst_3722_);
return v_s_3723_;
}
else
{
lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3795_; 
lean_inc_ref(v_exprToNatStructId_3731_);
lean_inc_ref(v_natTypeIdOf_3730_);
lean_inc_ref(v_natStructs_3729_);
lean_inc_ref(v_forbiddenNatModules_3728_);
lean_inc_ref(v_exprToStructIdEntries_3727_);
lean_inc_ref(v_exprToStructId_3726_);
lean_inc_ref(v_typeIdOf_3725_);
lean_inc_ref(v_structs_3724_);
v_isSharedCheck_3795_ = !lean_is_exclusive(v_s_3723_);
if (v_isSharedCheck_3795_ == 0)
{
lean_object* v_unused_3796_; lean_object* v_unused_3797_; lean_object* v_unused_3798_; lean_object* v_unused_3799_; lean_object* v_unused_3800_; lean_object* v_unused_3801_; lean_object* v_unused_3802_; lean_object* v_unused_3803_; 
v_unused_3796_ = lean_ctor_get(v_s_3723_, 7);
lean_dec(v_unused_3796_);
v_unused_3797_ = lean_ctor_get(v_s_3723_, 6);
lean_dec(v_unused_3797_);
v_unused_3798_ = lean_ctor_get(v_s_3723_, 5);
lean_dec(v_unused_3798_);
v_unused_3799_ = lean_ctor_get(v_s_3723_, 4);
lean_dec(v_unused_3799_);
v_unused_3800_ = lean_ctor_get(v_s_3723_, 3);
lean_dec(v_unused_3800_);
v_unused_3801_ = lean_ctor_get(v_s_3723_, 2);
lean_dec(v_unused_3801_);
v_unused_3802_ = lean_ctor_get(v_s_3723_, 1);
lean_dec(v_unused_3802_);
v_unused_3803_ = lean_ctor_get(v_s_3723_, 0);
lean_dec(v_unused_3803_);
v___x_3735_ = v_s_3723_;
v_isShared_3736_ = v_isSharedCheck_3795_;
goto v_resetjp_3734_;
}
else
{
lean_dec(v_s_3723_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3795_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v_v_3737_; lean_object* v_id_3738_; lean_object* v_ringId_x3f_3739_; lean_object* v_type_3740_; lean_object* v_u_3741_; lean_object* v_intModuleInst_3742_; lean_object* v_leInst_x3f_3743_; lean_object* v_ltInst_x3f_3744_; lean_object* v_lawfulOrderLTInst_x3f_3745_; lean_object* v_isPreorderInst_x3f_3746_; lean_object* v_orderedAddInst_x3f_3747_; lean_object* v_isLinearInst_x3f_3748_; lean_object* v_noNatDivInst_x3f_3749_; lean_object* v_ringInst_x3f_3750_; lean_object* v_commRingInst_x3f_3751_; lean_object* v_orderedRingInst_x3f_3752_; lean_object* v_fieldInst_x3f_3753_; lean_object* v_charInst_x3f_3754_; lean_object* v_zero_3755_; lean_object* v_ofNatZero_3756_; lean_object* v_one_x3f_3757_; lean_object* v_leFn_x3f_3758_; lean_object* v_ltFn_x3f_3759_; lean_object* v_addFn_3760_; lean_object* v_zsmulFn_3761_; lean_object* v_nsmulFn_3762_; lean_object* v_zsmulFn_x3f_3763_; lean_object* v_nsmulFn_x3f_3764_; lean_object* v_homomulFn_x3f_3765_; lean_object* v_subFn_3766_; lean_object* v_negFn_3767_; lean_object* v_vars_3768_; lean_object* v_varMap_3769_; lean_object* v_lowers_3770_; lean_object* v_uppers_3771_; lean_object* v_diseqs_3772_; lean_object* v_assignment_3773_; uint8_t v_caseSplits_3774_; lean_object* v_conflict_x3f_3775_; lean_object* v_diseqSplits_3776_; lean_object* v_elimEqs_3777_; lean_object* v_elimStack_3778_; lean_object* v_occurs_3779_; lean_object* v_ignored_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3794_; 
v_v_3737_ = lean_array_fget(v_structs_3724_, v_a_3720_);
v_id_3738_ = lean_ctor_get(v_v_3737_, 0);
v_ringId_x3f_3739_ = lean_ctor_get(v_v_3737_, 1);
v_type_3740_ = lean_ctor_get(v_v_3737_, 2);
v_u_3741_ = lean_ctor_get(v_v_3737_, 3);
v_intModuleInst_3742_ = lean_ctor_get(v_v_3737_, 4);
v_leInst_x3f_3743_ = lean_ctor_get(v_v_3737_, 5);
v_ltInst_x3f_3744_ = lean_ctor_get(v_v_3737_, 6);
v_lawfulOrderLTInst_x3f_3745_ = lean_ctor_get(v_v_3737_, 7);
v_isPreorderInst_x3f_3746_ = lean_ctor_get(v_v_3737_, 8);
v_orderedAddInst_x3f_3747_ = lean_ctor_get(v_v_3737_, 9);
v_isLinearInst_x3f_3748_ = lean_ctor_get(v_v_3737_, 10);
v_noNatDivInst_x3f_3749_ = lean_ctor_get(v_v_3737_, 11);
v_ringInst_x3f_3750_ = lean_ctor_get(v_v_3737_, 12);
v_commRingInst_x3f_3751_ = lean_ctor_get(v_v_3737_, 13);
v_orderedRingInst_x3f_3752_ = lean_ctor_get(v_v_3737_, 14);
v_fieldInst_x3f_3753_ = lean_ctor_get(v_v_3737_, 15);
v_charInst_x3f_3754_ = lean_ctor_get(v_v_3737_, 16);
v_zero_3755_ = lean_ctor_get(v_v_3737_, 17);
v_ofNatZero_3756_ = lean_ctor_get(v_v_3737_, 18);
v_one_x3f_3757_ = lean_ctor_get(v_v_3737_, 19);
v_leFn_x3f_3758_ = lean_ctor_get(v_v_3737_, 20);
v_ltFn_x3f_3759_ = lean_ctor_get(v_v_3737_, 21);
v_addFn_3760_ = lean_ctor_get(v_v_3737_, 22);
v_zsmulFn_3761_ = lean_ctor_get(v_v_3737_, 23);
v_nsmulFn_3762_ = lean_ctor_get(v_v_3737_, 24);
v_zsmulFn_x3f_3763_ = lean_ctor_get(v_v_3737_, 25);
v_nsmulFn_x3f_3764_ = lean_ctor_get(v_v_3737_, 26);
v_homomulFn_x3f_3765_ = lean_ctor_get(v_v_3737_, 27);
v_subFn_3766_ = lean_ctor_get(v_v_3737_, 28);
v_negFn_3767_ = lean_ctor_get(v_v_3737_, 29);
v_vars_3768_ = lean_ctor_get(v_v_3737_, 30);
v_varMap_3769_ = lean_ctor_get(v_v_3737_, 31);
v_lowers_3770_ = lean_ctor_get(v_v_3737_, 32);
v_uppers_3771_ = lean_ctor_get(v_v_3737_, 33);
v_diseqs_3772_ = lean_ctor_get(v_v_3737_, 34);
v_assignment_3773_ = lean_ctor_get(v_v_3737_, 35);
v_caseSplits_3774_ = lean_ctor_get_uint8(v_v_3737_, sizeof(void*)*42);
v_conflict_x3f_3775_ = lean_ctor_get(v_v_3737_, 36);
v_diseqSplits_3776_ = lean_ctor_get(v_v_3737_, 37);
v_elimEqs_3777_ = lean_ctor_get(v_v_3737_, 38);
v_elimStack_3778_ = lean_ctor_get(v_v_3737_, 39);
v_occurs_3779_ = lean_ctor_get(v_v_3737_, 40);
v_ignored_3780_ = lean_ctor_get(v_v_3737_, 41);
v_isSharedCheck_3794_ = !lean_is_exclusive(v_v_3737_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3782_ = v_v_3737_;
v_isShared_3783_ = v_isSharedCheck_3794_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_ignored_3780_);
lean_inc(v_occurs_3779_);
lean_inc(v_elimStack_3778_);
lean_inc(v_elimEqs_3777_);
lean_inc(v_diseqSplits_3776_);
lean_inc(v_conflict_x3f_3775_);
lean_inc(v_assignment_3773_);
lean_inc(v_diseqs_3772_);
lean_inc(v_uppers_3771_);
lean_inc(v_lowers_3770_);
lean_inc(v_varMap_3769_);
lean_inc(v_vars_3768_);
lean_inc(v_negFn_3767_);
lean_inc(v_subFn_3766_);
lean_inc(v_homomulFn_x3f_3765_);
lean_inc(v_nsmulFn_x3f_3764_);
lean_inc(v_zsmulFn_x3f_3763_);
lean_inc(v_nsmulFn_3762_);
lean_inc(v_zsmulFn_3761_);
lean_inc(v_addFn_3760_);
lean_inc(v_ltFn_x3f_3759_);
lean_inc(v_leFn_x3f_3758_);
lean_inc(v_one_x3f_3757_);
lean_inc(v_ofNatZero_3756_);
lean_inc(v_zero_3755_);
lean_inc(v_charInst_x3f_3754_);
lean_inc(v_fieldInst_x3f_3753_);
lean_inc(v_orderedRingInst_x3f_3752_);
lean_inc(v_commRingInst_x3f_3751_);
lean_inc(v_ringInst_x3f_3750_);
lean_inc(v_noNatDivInst_x3f_3749_);
lean_inc(v_isLinearInst_x3f_3748_);
lean_inc(v_orderedAddInst_x3f_3747_);
lean_inc(v_isPreorderInst_x3f_3746_);
lean_inc(v_lawfulOrderLTInst_x3f_3745_);
lean_inc(v_ltInst_x3f_3744_);
lean_inc(v_leInst_x3f_3743_);
lean_inc(v_intModuleInst_3742_);
lean_inc(v_u_3741_);
lean_inc(v_type_3740_);
lean_inc(v_ringId_x3f_3739_);
lean_inc(v_id_3738_);
lean_dec(v_v_3737_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3794_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3784_; lean_object* v_xs_x27_3785_; lean_object* v___x_3786_; lean_object* v___x_3788_; 
v___x_3784_ = lean_box(0);
v_xs_x27_3785_ = lean_array_fset(v_structs_3724_, v_a_3720_, v___x_3784_);
v___x_3786_ = l_Lean_PersistentArray_set___redArg(v_diseqs_3772_, v_y_3721_, v_fst_3722_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 34, v___x_3786_);
v___x_3788_ = v___x_3782_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_id_3738_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_ringId_x3f_3739_);
lean_ctor_set(v_reuseFailAlloc_3793_, 2, v_type_3740_);
lean_ctor_set(v_reuseFailAlloc_3793_, 3, v_u_3741_);
lean_ctor_set(v_reuseFailAlloc_3793_, 4, v_intModuleInst_3742_);
lean_ctor_set(v_reuseFailAlloc_3793_, 5, v_leInst_x3f_3743_);
lean_ctor_set(v_reuseFailAlloc_3793_, 6, v_ltInst_x3f_3744_);
lean_ctor_set(v_reuseFailAlloc_3793_, 7, v_lawfulOrderLTInst_x3f_3745_);
lean_ctor_set(v_reuseFailAlloc_3793_, 8, v_isPreorderInst_x3f_3746_);
lean_ctor_set(v_reuseFailAlloc_3793_, 9, v_orderedAddInst_x3f_3747_);
lean_ctor_set(v_reuseFailAlloc_3793_, 10, v_isLinearInst_x3f_3748_);
lean_ctor_set(v_reuseFailAlloc_3793_, 11, v_noNatDivInst_x3f_3749_);
lean_ctor_set(v_reuseFailAlloc_3793_, 12, v_ringInst_x3f_3750_);
lean_ctor_set(v_reuseFailAlloc_3793_, 13, v_commRingInst_x3f_3751_);
lean_ctor_set(v_reuseFailAlloc_3793_, 14, v_orderedRingInst_x3f_3752_);
lean_ctor_set(v_reuseFailAlloc_3793_, 15, v_fieldInst_x3f_3753_);
lean_ctor_set(v_reuseFailAlloc_3793_, 16, v_charInst_x3f_3754_);
lean_ctor_set(v_reuseFailAlloc_3793_, 17, v_zero_3755_);
lean_ctor_set(v_reuseFailAlloc_3793_, 18, v_ofNatZero_3756_);
lean_ctor_set(v_reuseFailAlloc_3793_, 19, v_one_x3f_3757_);
lean_ctor_set(v_reuseFailAlloc_3793_, 20, v_leFn_x3f_3758_);
lean_ctor_set(v_reuseFailAlloc_3793_, 21, v_ltFn_x3f_3759_);
lean_ctor_set(v_reuseFailAlloc_3793_, 22, v_addFn_3760_);
lean_ctor_set(v_reuseFailAlloc_3793_, 23, v_zsmulFn_3761_);
lean_ctor_set(v_reuseFailAlloc_3793_, 24, v_nsmulFn_3762_);
lean_ctor_set(v_reuseFailAlloc_3793_, 25, v_zsmulFn_x3f_3763_);
lean_ctor_set(v_reuseFailAlloc_3793_, 26, v_nsmulFn_x3f_3764_);
lean_ctor_set(v_reuseFailAlloc_3793_, 27, v_homomulFn_x3f_3765_);
lean_ctor_set(v_reuseFailAlloc_3793_, 28, v_subFn_3766_);
lean_ctor_set(v_reuseFailAlloc_3793_, 29, v_negFn_3767_);
lean_ctor_set(v_reuseFailAlloc_3793_, 30, v_vars_3768_);
lean_ctor_set(v_reuseFailAlloc_3793_, 31, v_varMap_3769_);
lean_ctor_set(v_reuseFailAlloc_3793_, 32, v_lowers_3770_);
lean_ctor_set(v_reuseFailAlloc_3793_, 33, v_uppers_3771_);
lean_ctor_set(v_reuseFailAlloc_3793_, 34, v___x_3786_);
lean_ctor_set(v_reuseFailAlloc_3793_, 35, v_assignment_3773_);
lean_ctor_set(v_reuseFailAlloc_3793_, 36, v_conflict_x3f_3775_);
lean_ctor_set(v_reuseFailAlloc_3793_, 37, v_diseqSplits_3776_);
lean_ctor_set(v_reuseFailAlloc_3793_, 38, v_elimEqs_3777_);
lean_ctor_set(v_reuseFailAlloc_3793_, 39, v_elimStack_3778_);
lean_ctor_set(v_reuseFailAlloc_3793_, 40, v_occurs_3779_);
lean_ctor_set(v_reuseFailAlloc_3793_, 41, v_ignored_3780_);
lean_ctor_set_uint8(v_reuseFailAlloc_3793_, sizeof(void*)*42, v_caseSplits_3774_);
v___x_3788_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
lean_object* v___x_3789_; lean_object* v___x_3791_; 
v___x_3789_ = lean_array_fset(v_xs_x27_3785_, v_a_3720_, v___x_3788_);
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 0, v___x_3789_);
v___x_3791_ = v___x_3735_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3789_);
lean_ctor_set(v_reuseFailAlloc_3792_, 1, v_typeIdOf_3725_);
lean_ctor_set(v_reuseFailAlloc_3792_, 2, v_exprToStructId_3726_);
lean_ctor_set(v_reuseFailAlloc_3792_, 3, v_exprToStructIdEntries_3727_);
lean_ctor_set(v_reuseFailAlloc_3792_, 4, v_forbiddenNatModules_3728_);
lean_ctor_set(v_reuseFailAlloc_3792_, 5, v_natStructs_3729_);
lean_ctor_set(v_reuseFailAlloc_3792_, 6, v_natTypeIdOf_3730_);
lean_ctor_set(v_reuseFailAlloc_3792_, 7, v_exprToNatStructId_3731_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed(lean_object* v_a_3804_, lean_object* v_y_3805_, lean_object* v_fst_3806_, lean_object* v_s_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(v_a_3804_, v_y_3805_, v_fst_3806_, v_s_3807_);
lean_dec(v_y_3805_);
lean_dec(v_a_3804_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object* v_a_3809_, lean_object* v_x_3810_, lean_object* v_c_3811_, lean_object* v_as_3812_, size_t v_sz_3813_, size_t v_i_3814_, lean_object* v_b_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
lean_object* v_a_3829_; uint8_t v___x_3833_; 
v___x_3833_ = lean_usize_dec_lt(v_i_3814_, v_sz_3813_);
if (v___x_3833_ == 0)
{
lean_object* v___x_3834_; 
lean_dec_ref(v_c_3811_);
v___x_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3834_, 0, v_b_3815_);
return v___x_3834_;
}
else
{
lean_object* v_a_3835_; lean_object* v_fst_3836_; lean_object* v_snd_3837_; lean_object* v___x_3838_; 
lean_dec_ref(v_b_3815_);
v_a_3835_ = lean_array_uget_borrowed(v_as_3812_, v_i_3814_);
v_fst_3836_ = lean_ctor_get(v_a_3835_, 0);
v_snd_3837_ = lean_ctor_get(v_a_3835_, 1);
lean_inc(v_snd_3837_);
lean_inc(v_fst_3836_);
lean_inc_ref(v_c_3811_);
v___x_3838_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_3809_, v_x_3810_, v_c_3811_, v_fst_3836_, v_snd_3837_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_object* v_a_3839_; lean_object* v___x_3840_; 
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3839_);
lean_dec_ref(v___x_3838_);
v___x_3840_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
if (lean_obj_tag(v_a_3839_) == 1)
{
lean_object* v_val_3841_; lean_object* v___x_3842_; 
v_val_3841_ = lean_ctor_get(v_a_3839_, 0);
lean_inc(v_val_3841_);
lean_dec_ref(v_a_3839_);
v___x_3842_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_val_3841_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v___x_3843_; 
lean_dec_ref(v___x_3842_);
v___x_3843_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3853_; 
v_a_3844_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3846_ = v___x_3843_;
v_isShared_3847_ = v_isSharedCheck_3853_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3843_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3853_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
uint8_t v___x_3848_; 
v___x_3848_ = lean_unbox(v_a_3844_);
lean_dec(v_a_3844_);
if (v___x_3848_ == 0)
{
lean_del_object(v___x_3846_);
v_a_3829_ = v___x_3840_;
goto v___jp_3828_;
}
else
{
lean_object* v___x_3849_; lean_object* v___x_3851_; 
lean_dec_ref(v_c_3811_);
v___x_3849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_3847_ == 0)
{
lean_ctor_set(v___x_3846_, 0, v___x_3849_);
v___x_3851_ = v___x_3846_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v___x_3849_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
else
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3861_; 
lean_dec_ref(v_c_3811_);
v_a_3854_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3856_ = v___x_3843_;
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3843_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3859_; 
if (v_isShared_3857_ == 0)
{
v___x_3859_ = v___x_3856_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
}
else
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
lean_dec_ref(v_c_3811_);
v_a_3862_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3842_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3842_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
else
{
lean_object* v___x_3870_; 
lean_dec(v_a_3839_);
v___x_3870_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_snd_3837_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_dec_ref(v___x_3870_);
v_a_3829_ = v___x_3840_;
goto v___jp_3828_;
}
else
{
lean_object* v_a_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3878_; 
lean_dec_ref(v_c_3811_);
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3873_ = v___x_3870_;
v_isShared_3874_ = v_isSharedCheck_3878_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_a_3871_);
lean_dec(v___x_3870_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3878_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___x_3876_; 
if (v_isShared_3874_ == 0)
{
v___x_3876_ = v___x_3873_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_a_3871_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
return v___x_3876_;
}
}
}
}
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
lean_dec_ref(v_c_3811_);
v_a_3879_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___x_3838_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3838_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
v___jp_3828_:
{
size_t v___x_3830_; size_t v___x_3831_; 
v___x_3830_ = ((size_t)1ULL);
v___x_3831_ = lean_usize_add(v_i_3814_, v___x_3830_);
v_i_3814_ = v___x_3831_;
v_b_3815_ = v_a_3829_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object** _args){
lean_object* v_a_3887_ = _args[0];
lean_object* v_x_3888_ = _args[1];
lean_object* v_c_3889_ = _args[2];
lean_object* v_as_3890_ = _args[3];
lean_object* v_sz_3891_ = _args[4];
lean_object* v_i_3892_ = _args[5];
lean_object* v_b_3893_ = _args[6];
lean_object* v___y_3894_ = _args[7];
lean_object* v___y_3895_ = _args[8];
lean_object* v___y_3896_ = _args[9];
lean_object* v___y_3897_ = _args[10];
lean_object* v___y_3898_ = _args[11];
lean_object* v___y_3899_ = _args[12];
lean_object* v___y_3900_ = _args[13];
lean_object* v___y_3901_ = _args[14];
lean_object* v___y_3902_ = _args[15];
lean_object* v___y_3903_ = _args[16];
lean_object* v___y_3904_ = _args[17];
lean_object* v___y_3905_ = _args[18];
_start:
{
size_t v_sz_boxed_3906_; size_t v_i_boxed_3907_; lean_object* v_res_3908_; 
v_sz_boxed_3906_ = lean_unbox_usize(v_sz_3891_);
lean_dec(v_sz_3891_);
v_i_boxed_3907_ = lean_unbox_usize(v_i_3892_);
lean_dec(v_i_3892_);
v_res_3908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3887_, v_x_3888_, v_c_3889_, v_as_3890_, v_sz_boxed_3906_, v_i_boxed_3907_, v_b_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v_as_3890_);
lean_dec(v_x_3888_);
lean_dec(v_a_3887_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object* v_a_3909_, lean_object* v_x_3910_, lean_object* v_c_3911_, lean_object* v_y_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_){
_start:
{
lean_object* v___x_3925_; 
v___x_3925_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3985_; 
v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3928_ = v___x_3925_;
v_isShared_3929_ = v_isSharedCheck_3985_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3925_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3985_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
uint8_t v___x_3930_; 
v___x_3930_ = lean_unbox(v_a_3926_);
lean_dec(v_a_3926_);
if (v___x_3930_ == 0)
{
lean_object* v___x_3931_; 
lean_del_object(v___x_3928_);
v___x_3931_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v___y_3934_; lean_object* v_diseqs_3967_; lean_object* v_size_3968_; lean_object* v___x_3969_; uint8_t v___x_3970_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref(v___x_3931_);
v_diseqs_3967_ = lean_ctor_get(v_a_3932_, 34);
lean_inc_ref(v_diseqs_3967_);
lean_dec(v_a_3932_);
v_size_3968_ = lean_ctor_get(v_diseqs_3967_, 2);
v___x_3969_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_3970_ = lean_nat_dec_lt(v_y_3912_, v_size_3968_);
if (v___x_3970_ == 0)
{
lean_object* v___x_3971_; 
lean_dec_ref(v_diseqs_3967_);
v___x_3971_ = l_outOfBounds___redArg(v___x_3969_);
v___y_3934_ = v___x_3971_;
goto v___jp_3933_;
}
else
{
lean_object* v___x_3972_; 
v___x_3972_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3969_, v_diseqs_3967_, v_y_3912_);
v___y_3934_ = v___x_3972_;
goto v___jp_3933_;
}
v___jp_3933_:
{
lean_object* v___x_3935_; lean_object* v_fst_3936_; lean_object* v_snd_3937_; lean_object* v___f_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3935_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3910_, v___y_3934_);
v_fst_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_fst_3936_);
v_snd_3937_ = lean_ctor_get(v___x_3935_, 1);
lean_inc(v_snd_3937_);
lean_dec_ref(v___x_3935_);
lean_inc(v_a_3913_);
v___f_3938_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3938_, 0, v_a_3913_);
lean_closure_set(v___f_3938_, 1, v_y_3912_);
lean_closure_set(v___f_3938_, 2, v_fst_3936_);
v___x_3939_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3940_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3939_, v___f_3938_, v_a_3914_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v___x_3941_; lean_object* v___x_3942_; size_t v_sz_3943_; size_t v___x_3944_; lean_object* v___x_3945_; 
lean_dec_ref(v___x_3940_);
v___x_3941_ = lean_box(0);
v___x_3942_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_3943_ = lean_array_size(v_snd_3937_);
v___x_3944_ = ((size_t)0ULL);
v___x_3945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3909_, v_x_3910_, v_c_3911_, v_snd_3937_, v_sz_3943_, v___x_3944_, v___x_3942_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_);
lean_dec(v_snd_3937_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3958_; 
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3948_ = v___x_3945_;
v_isShared_3949_ = v_isSharedCheck_3958_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3945_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3958_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v_fst_3950_; 
v_fst_3950_ = lean_ctor_get(v_a_3946_, 0);
lean_inc(v_fst_3950_);
lean_dec(v_a_3946_);
if (lean_obj_tag(v_fst_3950_) == 0)
{
lean_object* v___x_3952_; 
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 0, v___x_3941_);
v___x_3952_ = v___x_3948_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3941_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
else
{
lean_object* v_val_3954_; lean_object* v___x_3956_; 
v_val_3954_ = lean_ctor_get(v_fst_3950_, 0);
lean_inc(v_val_3954_);
lean_dec_ref(v_fst_3950_);
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 0, v_val_3954_);
v___x_3956_ = v___x_3948_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_val_3954_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
}
else
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3966_; 
v_a_3959_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3961_ = v___x_3945_;
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3945_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_a_3959_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
else
{
lean_dec(v_snd_3937_);
lean_dec_ref(v_c_3911_);
return v___x_3940_;
}
}
}
else
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
lean_dec(v_y_3912_);
lean_dec_ref(v_c_3911_);
v_a_3973_ = lean_ctor_get(v___x_3931_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3931_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3931_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
else
{
lean_object* v___x_3981_; lean_object* v___x_3983_; 
lean_dec(v_y_3912_);
lean_dec_ref(v_c_3911_);
v___x_3981_ = lean_box(0);
if (v_isShared_3929_ == 0)
{
lean_ctor_set(v___x_3928_, 0, v___x_3981_);
v___x_3983_ = v___x_3928_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v___x_3981_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
else
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3993_; 
lean_dec(v_y_3912_);
lean_dec_ref(v_c_3911_);
v_a_3986_ = lean_ctor_get(v___x_3925_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3988_ = v___x_3925_;
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3925_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3986_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object* v_a_3994_, lean_object* v_x_3995_, lean_object* v_c_3996_, lean_object* v_y_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_){
_start:
{
lean_object* v_res_4010_; 
v_res_4010_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v_a_3994_, v_x_3995_, v_c_3996_, v_y_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_);
lean_dec(v_a_4008_);
lean_dec_ref(v_a_4007_);
lean_dec(v_a_4006_);
lean_dec_ref(v_a_4005_);
lean_dec(v_a_4004_);
lean_dec_ref(v_a_4003_);
lean_dec(v_a_4002_);
lean_dec_ref(v_a_4001_);
lean_dec(v_a_4000_);
lean_dec(v_a_3999_);
lean_dec(v_a_3998_);
lean_dec(v_x_3995_);
lean_dec(v_a_3994_);
return v_res_4010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object* v_a_4011_, lean_object* v_x_4012_, lean_object* v_c_4013_, lean_object* v_y_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_){
_start:
{
lean_object* v___x_4027_; 
lean_inc(v_y_4014_);
lean_inc_ref(v_c_4013_);
lean_inc(v_x_4012_);
lean_inc(v_a_4011_);
v___x_4027_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_4011_, v_x_4012_, v_c_4013_, v_y_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v___x_4028_; 
lean_dec_ref(v___x_4027_);
lean_inc(v_y_4014_);
lean_inc_ref(v_c_4013_);
lean_inc(v_x_4012_);
lean_inc(v_a_4011_);
v___x_4028_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_4011_, v_x_4012_, v_c_4013_, v_y_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v___x_4029_; lean_object* v___x_4030_; 
lean_dec_ref(v___x_4028_);
v___x_4029_ = lean_nat_to_int(v_a_4011_);
v___x_4030_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v___x_4029_, v_x_4012_, v_c_4013_, v_y_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
lean_dec(v_x_4012_);
lean_dec(v___x_4029_);
return v___x_4030_;
}
else
{
lean_dec(v_y_4014_);
lean_dec_ref(v_c_4013_);
lean_dec(v_x_4012_);
lean_dec(v_a_4011_);
return v___x_4028_;
}
}
else
{
lean_dec(v_y_4014_);
lean_dec_ref(v_c_4013_);
lean_dec(v_x_4012_);
lean_dec(v_a_4011_);
return v___x_4027_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object* v_a_4031_, lean_object* v_x_4032_, lean_object* v_c_4033_, lean_object* v_y_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_){
_start:
{
lean_object* v_res_4047_; 
v_res_4047_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4031_, v_x_4032_, v_c_4033_, v_y_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_);
lean_dec(v_a_4045_);
lean_dec_ref(v_a_4044_);
lean_dec(v_a_4043_);
lean_dec_ref(v_a_4042_);
lean_dec(v_a_4041_);
lean_dec_ref(v_a_4040_);
lean_dec(v_a_4039_);
lean_dec_ref(v_a_4038_);
lean_dec(v_a_4037_);
lean_dec(v_a_4036_);
lean_dec(v_a_4035_);
return v_res_4047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(lean_object* v_a_4048_, lean_object* v_x_4049_, lean_object* v_s_4050_){
_start:
{
lean_object* v_structs_4051_; lean_object* v_typeIdOf_4052_; lean_object* v_exprToStructId_4053_; lean_object* v_exprToStructIdEntries_4054_; lean_object* v_forbiddenNatModules_4055_; lean_object* v_natStructs_4056_; lean_object* v_natTypeIdOf_4057_; lean_object* v_exprToNatStructId_4058_; lean_object* v___x_4059_; uint8_t v___x_4060_; 
v_structs_4051_ = lean_ctor_get(v_s_4050_, 0);
v_typeIdOf_4052_ = lean_ctor_get(v_s_4050_, 1);
v_exprToStructId_4053_ = lean_ctor_get(v_s_4050_, 2);
v_exprToStructIdEntries_4054_ = lean_ctor_get(v_s_4050_, 3);
v_forbiddenNatModules_4055_ = lean_ctor_get(v_s_4050_, 4);
v_natStructs_4056_ = lean_ctor_get(v_s_4050_, 5);
v_natTypeIdOf_4057_ = lean_ctor_get(v_s_4050_, 6);
v_exprToNatStructId_4058_ = lean_ctor_get(v_s_4050_, 7);
v___x_4059_ = lean_array_get_size(v_structs_4051_);
v___x_4060_ = lean_nat_dec_lt(v_a_4048_, v___x_4059_);
if (v___x_4060_ == 0)
{
return v_s_4050_;
}
else
{
lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4123_; 
lean_inc_ref(v_exprToNatStructId_4058_);
lean_inc_ref(v_natTypeIdOf_4057_);
lean_inc_ref(v_natStructs_4056_);
lean_inc_ref(v_forbiddenNatModules_4055_);
lean_inc_ref(v_exprToStructIdEntries_4054_);
lean_inc_ref(v_exprToStructId_4053_);
lean_inc_ref(v_typeIdOf_4052_);
lean_inc_ref(v_structs_4051_);
v_isSharedCheck_4123_ = !lean_is_exclusive(v_s_4050_);
if (v_isSharedCheck_4123_ == 0)
{
lean_object* v_unused_4124_; lean_object* v_unused_4125_; lean_object* v_unused_4126_; lean_object* v_unused_4127_; lean_object* v_unused_4128_; lean_object* v_unused_4129_; lean_object* v_unused_4130_; lean_object* v_unused_4131_; 
v_unused_4124_ = lean_ctor_get(v_s_4050_, 7);
lean_dec(v_unused_4124_);
v_unused_4125_ = lean_ctor_get(v_s_4050_, 6);
lean_dec(v_unused_4125_);
v_unused_4126_ = lean_ctor_get(v_s_4050_, 5);
lean_dec(v_unused_4126_);
v_unused_4127_ = lean_ctor_get(v_s_4050_, 4);
lean_dec(v_unused_4127_);
v_unused_4128_ = lean_ctor_get(v_s_4050_, 3);
lean_dec(v_unused_4128_);
v_unused_4129_ = lean_ctor_get(v_s_4050_, 2);
lean_dec(v_unused_4129_);
v_unused_4130_ = lean_ctor_get(v_s_4050_, 1);
lean_dec(v_unused_4130_);
v_unused_4131_ = lean_ctor_get(v_s_4050_, 0);
lean_dec(v_unused_4131_);
v___x_4062_ = v_s_4050_;
v_isShared_4063_ = v_isSharedCheck_4123_;
goto v_resetjp_4061_;
}
else
{
lean_dec(v_s_4050_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4123_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v_v_4064_; lean_object* v_id_4065_; lean_object* v_ringId_x3f_4066_; lean_object* v_type_4067_; lean_object* v_u_4068_; lean_object* v_intModuleInst_4069_; lean_object* v_leInst_x3f_4070_; lean_object* v_ltInst_x3f_4071_; lean_object* v_lawfulOrderLTInst_x3f_4072_; lean_object* v_isPreorderInst_x3f_4073_; lean_object* v_orderedAddInst_x3f_4074_; lean_object* v_isLinearInst_x3f_4075_; lean_object* v_noNatDivInst_x3f_4076_; lean_object* v_ringInst_x3f_4077_; lean_object* v_commRingInst_x3f_4078_; lean_object* v_orderedRingInst_x3f_4079_; lean_object* v_fieldInst_x3f_4080_; lean_object* v_charInst_x3f_4081_; lean_object* v_zero_4082_; lean_object* v_ofNatZero_4083_; lean_object* v_one_x3f_4084_; lean_object* v_leFn_x3f_4085_; lean_object* v_ltFn_x3f_4086_; lean_object* v_addFn_4087_; lean_object* v_zsmulFn_4088_; lean_object* v_nsmulFn_4089_; lean_object* v_zsmulFn_x3f_4090_; lean_object* v_nsmulFn_x3f_4091_; lean_object* v_homomulFn_x3f_4092_; lean_object* v_subFn_4093_; lean_object* v_negFn_4094_; lean_object* v_vars_4095_; lean_object* v_varMap_4096_; lean_object* v_lowers_4097_; lean_object* v_uppers_4098_; lean_object* v_diseqs_4099_; lean_object* v_assignment_4100_; uint8_t v_caseSplits_4101_; lean_object* v_conflict_x3f_4102_; lean_object* v_diseqSplits_4103_; lean_object* v_elimEqs_4104_; lean_object* v_elimStack_4105_; lean_object* v_occurs_4106_; lean_object* v_ignored_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4122_; 
v_v_4064_ = lean_array_fget(v_structs_4051_, v_a_4048_);
v_id_4065_ = lean_ctor_get(v_v_4064_, 0);
v_ringId_x3f_4066_ = lean_ctor_get(v_v_4064_, 1);
v_type_4067_ = lean_ctor_get(v_v_4064_, 2);
v_u_4068_ = lean_ctor_get(v_v_4064_, 3);
v_intModuleInst_4069_ = lean_ctor_get(v_v_4064_, 4);
v_leInst_x3f_4070_ = lean_ctor_get(v_v_4064_, 5);
v_ltInst_x3f_4071_ = lean_ctor_get(v_v_4064_, 6);
v_lawfulOrderLTInst_x3f_4072_ = lean_ctor_get(v_v_4064_, 7);
v_isPreorderInst_x3f_4073_ = lean_ctor_get(v_v_4064_, 8);
v_orderedAddInst_x3f_4074_ = lean_ctor_get(v_v_4064_, 9);
v_isLinearInst_x3f_4075_ = lean_ctor_get(v_v_4064_, 10);
v_noNatDivInst_x3f_4076_ = lean_ctor_get(v_v_4064_, 11);
v_ringInst_x3f_4077_ = lean_ctor_get(v_v_4064_, 12);
v_commRingInst_x3f_4078_ = lean_ctor_get(v_v_4064_, 13);
v_orderedRingInst_x3f_4079_ = lean_ctor_get(v_v_4064_, 14);
v_fieldInst_x3f_4080_ = lean_ctor_get(v_v_4064_, 15);
v_charInst_x3f_4081_ = lean_ctor_get(v_v_4064_, 16);
v_zero_4082_ = lean_ctor_get(v_v_4064_, 17);
v_ofNatZero_4083_ = lean_ctor_get(v_v_4064_, 18);
v_one_x3f_4084_ = lean_ctor_get(v_v_4064_, 19);
v_leFn_x3f_4085_ = lean_ctor_get(v_v_4064_, 20);
v_ltFn_x3f_4086_ = lean_ctor_get(v_v_4064_, 21);
v_addFn_4087_ = lean_ctor_get(v_v_4064_, 22);
v_zsmulFn_4088_ = lean_ctor_get(v_v_4064_, 23);
v_nsmulFn_4089_ = lean_ctor_get(v_v_4064_, 24);
v_zsmulFn_x3f_4090_ = lean_ctor_get(v_v_4064_, 25);
v_nsmulFn_x3f_4091_ = lean_ctor_get(v_v_4064_, 26);
v_homomulFn_x3f_4092_ = lean_ctor_get(v_v_4064_, 27);
v_subFn_4093_ = lean_ctor_get(v_v_4064_, 28);
v_negFn_4094_ = lean_ctor_get(v_v_4064_, 29);
v_vars_4095_ = lean_ctor_get(v_v_4064_, 30);
v_varMap_4096_ = lean_ctor_get(v_v_4064_, 31);
v_lowers_4097_ = lean_ctor_get(v_v_4064_, 32);
v_uppers_4098_ = lean_ctor_get(v_v_4064_, 33);
v_diseqs_4099_ = lean_ctor_get(v_v_4064_, 34);
v_assignment_4100_ = lean_ctor_get(v_v_4064_, 35);
v_caseSplits_4101_ = lean_ctor_get_uint8(v_v_4064_, sizeof(void*)*42);
v_conflict_x3f_4102_ = lean_ctor_get(v_v_4064_, 36);
v_diseqSplits_4103_ = lean_ctor_get(v_v_4064_, 37);
v_elimEqs_4104_ = lean_ctor_get(v_v_4064_, 38);
v_elimStack_4105_ = lean_ctor_get(v_v_4064_, 39);
v_occurs_4106_ = lean_ctor_get(v_v_4064_, 40);
v_ignored_4107_ = lean_ctor_get(v_v_4064_, 41);
v_isSharedCheck_4122_ = !lean_is_exclusive(v_v_4064_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4109_ = v_v_4064_;
v_isShared_4110_ = v_isSharedCheck_4122_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_ignored_4107_);
lean_inc(v_occurs_4106_);
lean_inc(v_elimStack_4105_);
lean_inc(v_elimEqs_4104_);
lean_inc(v_diseqSplits_4103_);
lean_inc(v_conflict_x3f_4102_);
lean_inc(v_assignment_4100_);
lean_inc(v_diseqs_4099_);
lean_inc(v_uppers_4098_);
lean_inc(v_lowers_4097_);
lean_inc(v_varMap_4096_);
lean_inc(v_vars_4095_);
lean_inc(v_negFn_4094_);
lean_inc(v_subFn_4093_);
lean_inc(v_homomulFn_x3f_4092_);
lean_inc(v_nsmulFn_x3f_4091_);
lean_inc(v_zsmulFn_x3f_4090_);
lean_inc(v_nsmulFn_4089_);
lean_inc(v_zsmulFn_4088_);
lean_inc(v_addFn_4087_);
lean_inc(v_ltFn_x3f_4086_);
lean_inc(v_leFn_x3f_4085_);
lean_inc(v_one_x3f_4084_);
lean_inc(v_ofNatZero_4083_);
lean_inc(v_zero_4082_);
lean_inc(v_charInst_x3f_4081_);
lean_inc(v_fieldInst_x3f_4080_);
lean_inc(v_orderedRingInst_x3f_4079_);
lean_inc(v_commRingInst_x3f_4078_);
lean_inc(v_ringInst_x3f_4077_);
lean_inc(v_noNatDivInst_x3f_4076_);
lean_inc(v_isLinearInst_x3f_4075_);
lean_inc(v_orderedAddInst_x3f_4074_);
lean_inc(v_isPreorderInst_x3f_4073_);
lean_inc(v_lawfulOrderLTInst_x3f_4072_);
lean_inc(v_ltInst_x3f_4071_);
lean_inc(v_leInst_x3f_4070_);
lean_inc(v_intModuleInst_4069_);
lean_inc(v_u_4068_);
lean_inc(v_type_4067_);
lean_inc(v_ringId_x3f_4066_);
lean_inc(v_id_4065_);
lean_dec(v_v_4064_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4122_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4111_; lean_object* v_xs_x27_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4116_; 
v___x_4111_ = lean_box(0);
v_xs_x27_4112_ = lean_array_fset(v_structs_4051_, v_a_4048_, v___x_4111_);
v___x_4113_ = lean_box(1);
v___x_4114_ = l_Lean_PersistentArray_set___redArg(v_occurs_4106_, v_x_4049_, v___x_4113_);
if (v_isShared_4110_ == 0)
{
lean_ctor_set(v___x_4109_, 40, v___x_4114_);
v___x_4116_ = v___x_4109_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_id_4065_);
lean_ctor_set(v_reuseFailAlloc_4121_, 1, v_ringId_x3f_4066_);
lean_ctor_set(v_reuseFailAlloc_4121_, 2, v_type_4067_);
lean_ctor_set(v_reuseFailAlloc_4121_, 3, v_u_4068_);
lean_ctor_set(v_reuseFailAlloc_4121_, 4, v_intModuleInst_4069_);
lean_ctor_set(v_reuseFailAlloc_4121_, 5, v_leInst_x3f_4070_);
lean_ctor_set(v_reuseFailAlloc_4121_, 6, v_ltInst_x3f_4071_);
lean_ctor_set(v_reuseFailAlloc_4121_, 7, v_lawfulOrderLTInst_x3f_4072_);
lean_ctor_set(v_reuseFailAlloc_4121_, 8, v_isPreorderInst_x3f_4073_);
lean_ctor_set(v_reuseFailAlloc_4121_, 9, v_orderedAddInst_x3f_4074_);
lean_ctor_set(v_reuseFailAlloc_4121_, 10, v_isLinearInst_x3f_4075_);
lean_ctor_set(v_reuseFailAlloc_4121_, 11, v_noNatDivInst_x3f_4076_);
lean_ctor_set(v_reuseFailAlloc_4121_, 12, v_ringInst_x3f_4077_);
lean_ctor_set(v_reuseFailAlloc_4121_, 13, v_commRingInst_x3f_4078_);
lean_ctor_set(v_reuseFailAlloc_4121_, 14, v_orderedRingInst_x3f_4079_);
lean_ctor_set(v_reuseFailAlloc_4121_, 15, v_fieldInst_x3f_4080_);
lean_ctor_set(v_reuseFailAlloc_4121_, 16, v_charInst_x3f_4081_);
lean_ctor_set(v_reuseFailAlloc_4121_, 17, v_zero_4082_);
lean_ctor_set(v_reuseFailAlloc_4121_, 18, v_ofNatZero_4083_);
lean_ctor_set(v_reuseFailAlloc_4121_, 19, v_one_x3f_4084_);
lean_ctor_set(v_reuseFailAlloc_4121_, 20, v_leFn_x3f_4085_);
lean_ctor_set(v_reuseFailAlloc_4121_, 21, v_ltFn_x3f_4086_);
lean_ctor_set(v_reuseFailAlloc_4121_, 22, v_addFn_4087_);
lean_ctor_set(v_reuseFailAlloc_4121_, 23, v_zsmulFn_4088_);
lean_ctor_set(v_reuseFailAlloc_4121_, 24, v_nsmulFn_4089_);
lean_ctor_set(v_reuseFailAlloc_4121_, 25, v_zsmulFn_x3f_4090_);
lean_ctor_set(v_reuseFailAlloc_4121_, 26, v_nsmulFn_x3f_4091_);
lean_ctor_set(v_reuseFailAlloc_4121_, 27, v_homomulFn_x3f_4092_);
lean_ctor_set(v_reuseFailAlloc_4121_, 28, v_subFn_4093_);
lean_ctor_set(v_reuseFailAlloc_4121_, 29, v_negFn_4094_);
lean_ctor_set(v_reuseFailAlloc_4121_, 30, v_vars_4095_);
lean_ctor_set(v_reuseFailAlloc_4121_, 31, v_varMap_4096_);
lean_ctor_set(v_reuseFailAlloc_4121_, 32, v_lowers_4097_);
lean_ctor_set(v_reuseFailAlloc_4121_, 33, v_uppers_4098_);
lean_ctor_set(v_reuseFailAlloc_4121_, 34, v_diseqs_4099_);
lean_ctor_set(v_reuseFailAlloc_4121_, 35, v_assignment_4100_);
lean_ctor_set(v_reuseFailAlloc_4121_, 36, v_conflict_x3f_4102_);
lean_ctor_set(v_reuseFailAlloc_4121_, 37, v_diseqSplits_4103_);
lean_ctor_set(v_reuseFailAlloc_4121_, 38, v_elimEqs_4104_);
lean_ctor_set(v_reuseFailAlloc_4121_, 39, v_elimStack_4105_);
lean_ctor_set(v_reuseFailAlloc_4121_, 40, v___x_4114_);
lean_ctor_set(v_reuseFailAlloc_4121_, 41, v_ignored_4107_);
lean_ctor_set_uint8(v_reuseFailAlloc_4121_, sizeof(void*)*42, v_caseSplits_4101_);
v___x_4116_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
lean_object* v___x_4117_; lean_object* v___x_4119_; 
v___x_4117_ = lean_array_fset(v_xs_x27_4112_, v_a_4048_, v___x_4116_);
if (v_isShared_4063_ == 0)
{
lean_ctor_set(v___x_4062_, 0, v___x_4117_);
v___x_4119_ = v___x_4062_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v___x_4117_);
lean_ctor_set(v_reuseFailAlloc_4120_, 1, v_typeIdOf_4052_);
lean_ctor_set(v_reuseFailAlloc_4120_, 2, v_exprToStructId_4053_);
lean_ctor_set(v_reuseFailAlloc_4120_, 3, v_exprToStructIdEntries_4054_);
lean_ctor_set(v_reuseFailAlloc_4120_, 4, v_forbiddenNatModules_4055_);
lean_ctor_set(v_reuseFailAlloc_4120_, 5, v_natStructs_4056_);
lean_ctor_set(v_reuseFailAlloc_4120_, 6, v_natTypeIdOf_4057_);
lean_ctor_set(v_reuseFailAlloc_4120_, 7, v_exprToNatStructId_4058_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed(lean_object* v_a_4132_, lean_object* v_x_4133_, lean_object* v_s_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(v_a_4132_, v_x_4133_, v_s_4134_);
lean_dec(v_x_4133_);
lean_dec(v_a_4132_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object* v_a_4136_, lean_object* v_x_4137_, lean_object* v_c_4138_, lean_object* v_init_4139_, lean_object* v_x_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
if (lean_obj_tag(v_x_4140_) == 0)
{
lean_object* v_k_4153_; lean_object* v_l_4154_; lean_object* v_r_4155_; lean_object* v___x_4156_; 
v_k_4153_ = lean_ctor_get(v_x_4140_, 1);
lean_inc(v_k_4153_);
v_l_4154_ = lean_ctor_get(v_x_4140_, 3);
lean_inc(v_l_4154_);
v_r_4155_ = lean_ctor_get(v_x_4140_, 4);
lean_inc(v_r_4155_);
lean_dec_ref(v_x_4140_);
lean_inc_ref(v_c_4138_);
lean_inc(v_x_4137_);
lean_inc(v_a_4136_);
v___x_4156_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4136_, v_x_4137_, v_c_4138_, v_init_4139_, v_l_4154_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v___x_4157_; 
lean_dec_ref(v___x_4156_);
lean_inc_ref(v_c_4138_);
lean_inc(v_x_4137_);
lean_inc(v_a_4136_);
v___x_4157_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4136_, v_x_4137_, v_c_4138_, v_k_4153_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v___x_4158_; 
lean_dec_ref(v___x_4157_);
v___x_4158_ = lean_box(0);
v_init_4139_ = v___x_4158_;
v_x_4140_ = v_r_4155_;
goto _start;
}
else
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4167_; 
lean_dec(v_r_4155_);
lean_dec_ref(v_c_4138_);
lean_dec(v_x_4137_);
lean_dec(v_a_4136_);
v_a_4160_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4162_ = v___x_4157_;
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4157_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4165_; 
if (v_isShared_4163_ == 0)
{
v___x_4165_ = v___x_4162_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_a_4160_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
}
else
{
lean_dec(v_r_4155_);
lean_dec(v_k_4153_);
lean_dec_ref(v_c_4138_);
lean_dec(v_x_4137_);
lean_dec(v_a_4136_);
return v___x_4156_;
}
}
else
{
lean_object* v___x_4168_; lean_object* v___x_4169_; 
lean_dec_ref(v_c_4138_);
lean_dec(v_x_4137_);
lean_dec(v_a_4136_);
v___x_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4168_, 0, v_init_4139_);
v___x_4169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
return v___x_4169_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object** _args){
lean_object* v_a_4170_ = _args[0];
lean_object* v_x_4171_ = _args[1];
lean_object* v_c_4172_ = _args[2];
lean_object* v_init_4173_ = _args[3];
lean_object* v_x_4174_ = _args[4];
lean_object* v___y_4175_ = _args[5];
lean_object* v___y_4176_ = _args[6];
lean_object* v___y_4177_ = _args[7];
lean_object* v___y_4178_ = _args[8];
lean_object* v___y_4179_ = _args[9];
lean_object* v___y_4180_ = _args[10];
lean_object* v___y_4181_ = _args[11];
lean_object* v___y_4182_ = _args[12];
lean_object* v___y_4183_ = _args[13];
lean_object* v___y_4184_ = _args[14];
lean_object* v___y_4185_ = _args[15];
lean_object* v___y_4186_ = _args[16];
_start:
{
lean_object* v_res_4187_; 
v_res_4187_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4170_, v_x_4171_, v_c_4172_, v_init_4173_, v_x_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec(v___y_4175_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object* v_a_4188_, lean_object* v_x_4189_, lean_object* v_c_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_){
_start:
{
lean_object* v___x_4203_; 
v___x_4203_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v_occurs_4205_; lean_object* v_size_4206_; lean_object* v___f_4207_; lean_object* v___y_4209_; lean_object* v___x_4231_; uint8_t v___x_4232_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc(v_a_4204_);
lean_dec_ref(v___x_4203_);
v_occurs_4205_ = lean_ctor_get(v_a_4204_, 40);
lean_inc_ref(v_occurs_4205_);
lean_dec(v_a_4204_);
v_size_4206_ = lean_ctor_get(v_occurs_4205_, 2);
lean_inc(v_x_4189_);
lean_inc(v_a_4191_);
v___f_4207_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4207_, 0, v_a_4191_);
lean_closure_set(v___f_4207_, 1, v_x_4189_);
v___x_4231_ = lean_box(1);
v___x_4232_ = lean_nat_dec_lt(v_x_4189_, v_size_4206_);
if (v___x_4232_ == 0)
{
lean_object* v___x_4233_; 
lean_dec_ref(v_occurs_4205_);
v___x_4233_ = l_outOfBounds___redArg(v___x_4231_);
v___y_4209_ = v___x_4233_;
goto v___jp_4208_;
}
else
{
lean_object* v___x_4234_; 
v___x_4234_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4231_, v_occurs_4205_, v_x_4189_);
v___y_4209_ = v___x_4234_;
goto v___jp_4208_;
}
v___jp_4208_:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4210_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4211_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4210_, v___f_4207_, v_a_4192_);
if (lean_obj_tag(v___x_4211_) == 0)
{
lean_object* v___x_4212_; 
lean_dec_ref(v___x_4211_);
lean_inc_ref(v_c_4190_);
lean_inc_n(v_x_4189_, 2);
lean_inc(v_a_4188_);
v___x_4212_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4188_, v_x_4189_, v_c_4190_, v_x_4189_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v___x_4213_; lean_object* v___x_4214_; 
lean_dec_ref(v___x_4212_);
v___x_4213_ = lean_box(0);
v___x_4214_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4188_, v_x_4189_, v_c_4190_, v___x_4213_, v___y_4209_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4221_; 
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4221_ == 0)
{
lean_object* v_unused_4222_; 
v_unused_4222_ = lean_ctor_get(v___x_4214_, 0);
lean_dec(v_unused_4222_);
v___x_4216_ = v___x_4214_;
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
else
{
lean_dec(v___x_4214_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4219_; 
if (v_isShared_4217_ == 0)
{
lean_ctor_set(v___x_4216_, 0, v___x_4213_);
v___x_4219_ = v___x_4216_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4213_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
else
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
v_a_4223_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_4214_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4214_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4223_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
}
else
{
lean_dec(v___y_4209_);
lean_dec_ref(v_c_4190_);
lean_dec(v_x_4189_);
lean_dec(v_a_4188_);
return v___x_4212_;
}
}
else
{
lean_dec(v___y_4209_);
lean_dec_ref(v_c_4190_);
lean_dec(v_x_4189_);
lean_dec(v_a_4188_);
return v___x_4211_;
}
}
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
lean_dec_ref(v_c_4190_);
lean_dec(v_x_4189_);
lean_dec(v_a_4188_);
v_a_4235_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4203_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4203_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___boxed(lean_object* v_a_4243_, lean_object* v_x_4244_, lean_object* v_c_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v_a_4243_, v_x_4244_, v_c_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_);
lean_dec(v_a_4256_);
lean_dec_ref(v_a_4255_);
lean_dec(v_a_4254_);
lean_dec_ref(v_a_4253_);
lean_dec(v_a_4252_);
lean_dec_ref(v_a_4251_);
lean_dec(v_a_4250_);
lean_dec_ref(v_a_4249_);
lean_dec(v_a_4248_);
lean_dec(v_a_4247_);
lean_dec(v_a_4246_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(lean_object* v_c_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_){
_start:
{
lean_object* v_p_4276_; 
v_p_4276_ = lean_ctor_get(v_c_4259_, 0);
if (lean_obj_tag(v_p_4276_) == 1)
{
lean_object* v_k_4277_; lean_object* v_v_4278_; lean_object* v_p_4279_; lean_object* v_y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___x_4330_; lean_object* v___x_4331_; uint8_t v___x_4332_; 
v_k_4277_ = lean_ctor_get(v_p_4276_, 0);
v_v_4278_ = lean_ctor_get(v_p_4276_, 1);
v_p_4279_ = lean_ctor_get(v_p_4276_, 2);
v___x_4330_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0);
v___x_4331_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4332_ = lean_int_dec_eq(v_k_4277_, v___x_4331_);
if (v___x_4332_ == 0)
{
uint8_t v___x_4333_; 
v___x_4333_ = lean_int_dec_eq(v_k_4277_, v___x_4330_);
if (v___x_4333_ == 0)
{
goto v___jp_4272_;
}
else
{
if (lean_obj_tag(v_p_4279_) == 1)
{
lean_object* v_k_4334_; lean_object* v_v_4335_; lean_object* v_p_4336_; uint8_t v___x_4337_; 
v_k_4334_ = lean_ctor_get(v_p_4279_, 0);
v_v_4335_ = lean_ctor_get(v_p_4279_, 1);
v_p_4336_ = lean_ctor_get(v_p_4279_, 2);
v___x_4337_ = lean_int_dec_eq(v_k_4334_, v___x_4331_);
if (v___x_4337_ == 0)
{
goto v___jp_4272_;
}
else
{
if (lean_obj_tag(v_p_4336_) == 0)
{
v_y_4281_ = v_v_4335_;
v___y_4282_ = v_a_4260_;
v___y_4283_ = v_a_4261_;
v___y_4284_ = v_a_4262_;
v___y_4285_ = v_a_4263_;
v___y_4286_ = v_a_4264_;
v___y_4287_ = v_a_4265_;
v___y_4288_ = v_a_4266_;
v___y_4289_ = v_a_4267_;
v___y_4290_ = v_a_4268_;
v___y_4291_ = v_a_4269_;
v___y_4292_ = v_a_4270_;
goto v___jp_4280_;
}
else
{
goto v___jp_4272_;
}
}
}
else
{
goto v___jp_4272_;
}
}
}
else
{
if (lean_obj_tag(v_p_4279_) == 1)
{
lean_object* v_k_4338_; lean_object* v_v_4339_; lean_object* v_p_4340_; uint8_t v___x_4341_; 
v_k_4338_ = lean_ctor_get(v_p_4279_, 0);
v_v_4339_ = lean_ctor_get(v_p_4279_, 1);
v_p_4340_ = lean_ctor_get(v_p_4279_, 2);
v___x_4341_ = lean_int_dec_eq(v_k_4338_, v___x_4330_);
if (v___x_4341_ == 0)
{
goto v___jp_4272_;
}
else
{
if (lean_obj_tag(v_p_4340_) == 0)
{
v_y_4281_ = v_v_4339_;
v___y_4282_ = v_a_4260_;
v___y_4283_ = v_a_4261_;
v___y_4284_ = v_a_4262_;
v___y_4285_ = v_a_4263_;
v___y_4286_ = v_a_4264_;
v___y_4287_ = v_a_4265_;
v___y_4288_ = v_a_4266_;
v___y_4289_ = v_a_4267_;
v___y_4290_ = v_a_4268_;
v___y_4291_ = v_a_4269_;
v___y_4292_ = v_a_4270_;
goto v___jp_4280_;
}
else
{
goto v___jp_4272_;
}
}
}
else
{
goto v___jp_4272_;
}
}
v___jp_4280_:
{
lean_object* v___x_4293_; 
v___x_4293_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_v_4278_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
if (lean_obj_tag(v___x_4293_) == 0)
{
lean_object* v_a_4294_; lean_object* v___x_4295_; 
v_a_4294_ = lean_ctor_get(v___x_4293_, 0);
lean_inc(v_a_4294_);
lean_dec_ref(v___x_4293_);
v___x_4295_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_a_4296_; lean_object* v___x_4297_; 
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
lean_inc(v_a_4296_);
lean_dec_ref(v___x_4295_);
v___x_4297_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_4294_, v_a_4296_, v___y_4283_);
lean_dec(v_a_4296_);
lean_dec(v_a_4294_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v_a_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4313_; 
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4300_ = v___x_4297_;
v_isShared_4301_ = v_isSharedCheck_4313_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_a_4298_);
lean_dec(v___x_4297_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4313_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
uint8_t v___x_4302_; 
v___x_4302_ = lean_unbox(v_a_4298_);
lean_dec(v_a_4298_);
if (v___x_4302_ == 0)
{
uint8_t v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4306_; 
v___x_4303_ = 1;
v___x_4304_ = lean_box(v___x_4303_);
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 0, v___x_4304_);
v___x_4306_ = v___x_4300_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v___x_4304_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
else
{
uint8_t v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4311_; 
v___x_4308_ = 0;
v___x_4309_ = lean_box(v___x_4308_);
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 0, v___x_4309_);
v___x_4311_ = v___x_4300_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v___x_4309_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
}
else
{
return v___x_4297_;
}
}
else
{
lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4321_; 
lean_dec(v_a_4294_);
v_a_4314_ = lean_ctor_get(v___x_4295_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4316_ = v___x_4295_;
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_dec(v___x_4295_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4319_; 
if (v_isShared_4317_ == 0)
{
v___x_4319_ = v___x_4316_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_a_4314_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
}
}
else
{
lean_object* v_a_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4329_; 
v_a_4322_ = lean_ctor_get(v___x_4293_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4293_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4324_ = v___x_4293_;
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_a_4322_);
lean_dec(v___x_4293_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4327_; 
if (v_isShared_4325_ == 0)
{
v___x_4327_ = v___x_4324_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4322_);
v___x_4327_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
return v___x_4327_;
}
}
}
}
}
else
{
goto v___jp_4272_;
}
v___jp_4272_:
{
uint8_t v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4273_ = 0;
v___x_4274_ = lean_box(v___x_4273_);
v___x_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4274_);
return v___x_4275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq___boxed(lean_object* v_c_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_){
_start:
{
lean_object* v_res_4355_; 
v_res_4355_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v_c_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
lean_dec(v_a_4353_);
lean_dec_ref(v_a_4352_);
lean_dec(v_a_4351_);
lean_dec_ref(v_a_4350_);
lean_dec(v_a_4349_);
lean_dec_ref(v_a_4348_);
lean_dec(v_a_4347_);
lean_dec_ref(v_a_4346_);
lean_dec(v_a_4345_);
lean_dec(v_a_4344_);
lean_dec(v_a_4343_);
lean_dec_ref(v_c_4342_);
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(lean_object* v_c_4356_){
_start:
{
lean_object* v_p_4358_; 
v_p_4358_ = lean_ctor_get(v_c_4356_, 0);
if (lean_obj_tag(v_p_4358_) == 1)
{
lean_object* v_k_4359_; lean_object* v___x_4360_; uint8_t v___x_4361_; 
v_k_4359_ = lean_ctor_get(v_p_4358_, 0);
v___x_4360_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_4361_ = lean_int_dec_lt(v_k_4359_, v___x_4360_);
if (v___x_4361_ == 0)
{
lean_object* v___x_4362_; 
v___x_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4362_, 0, v_c_4356_);
return v___x_4362_;
}
else
{
lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4363_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_4358_);
v___x_4364_ = l_Lean_Grind_Linarith_Poly_mul(v_p_4358_, v___x_4363_);
v___x_4365_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4365_, 0, v_c_4356_);
v___x_4366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4366_, 0, v___x_4364_);
lean_ctor_set(v___x_4366_, 1, v___x_4365_);
v___x_4367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4367_, 0, v___x_4366_);
return v___x_4367_;
}
}
else
{
lean_object* v___x_4368_; 
v___x_4368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4368_, 0, v_c_4356_);
return v___x_4368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg___boxed(lean_object* v_c_4369_, lean_object* v_a_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4369_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(lean_object* v_c_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_){
_start:
{
lean_object* v___x_4385_; 
v___x_4385_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4372_);
return v___x_4385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___boxed(lean_object* v_c_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_){
_start:
{
lean_object* v_res_4399_; 
v_res_4399_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(v_c_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_);
lean_dec(v_a_4397_);
lean_dec_ref(v_a_4396_);
lean_dec(v_a_4395_);
lean_dec_ref(v_a_4394_);
lean_dec(v_a_4393_);
lean_dec_ref(v_a_4392_);
lean_dec(v_a_4391_);
lean_dec_ref(v_a_4390_);
lean_dec(v_a_4389_);
lean_dec(v_a_4388_);
lean_dec(v_a_4387_);
return v_res_4399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(lean_object* v___y_4400_, lean_object* v_snd_4401_, lean_object* v_fst_4402_, lean_object* v_s_4403_){
_start:
{
lean_object* v_structs_4404_; lean_object* v_typeIdOf_4405_; lean_object* v_exprToStructId_4406_; lean_object* v_exprToStructIdEntries_4407_; lean_object* v_forbiddenNatModules_4408_; lean_object* v_natStructs_4409_; lean_object* v_natTypeIdOf_4410_; lean_object* v_exprToNatStructId_4411_; lean_object* v___x_4412_; uint8_t v___x_4413_; 
v_structs_4404_ = lean_ctor_get(v_s_4403_, 0);
v_typeIdOf_4405_ = lean_ctor_get(v_s_4403_, 1);
v_exprToStructId_4406_ = lean_ctor_get(v_s_4403_, 2);
v_exprToStructIdEntries_4407_ = lean_ctor_get(v_s_4403_, 3);
v_forbiddenNatModules_4408_ = lean_ctor_get(v_s_4403_, 4);
v_natStructs_4409_ = lean_ctor_get(v_s_4403_, 5);
v_natTypeIdOf_4410_ = lean_ctor_get(v_s_4403_, 6);
v_exprToNatStructId_4411_ = lean_ctor_get(v_s_4403_, 7);
v___x_4412_ = lean_array_get_size(v_structs_4404_);
v___x_4413_ = lean_nat_dec_lt(v___y_4400_, v___x_4412_);
if (v___x_4413_ == 0)
{
lean_dec(v_fst_4402_);
lean_dec_ref(v_snd_4401_);
return v_s_4403_;
}
else
{
lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4477_; 
lean_inc_ref(v_exprToNatStructId_4411_);
lean_inc_ref(v_natTypeIdOf_4410_);
lean_inc_ref(v_natStructs_4409_);
lean_inc_ref(v_forbiddenNatModules_4408_);
lean_inc_ref(v_exprToStructIdEntries_4407_);
lean_inc_ref(v_exprToStructId_4406_);
lean_inc_ref(v_typeIdOf_4405_);
lean_inc_ref(v_structs_4404_);
v_isSharedCheck_4477_ = !lean_is_exclusive(v_s_4403_);
if (v_isSharedCheck_4477_ == 0)
{
lean_object* v_unused_4478_; lean_object* v_unused_4479_; lean_object* v_unused_4480_; lean_object* v_unused_4481_; lean_object* v_unused_4482_; lean_object* v_unused_4483_; lean_object* v_unused_4484_; lean_object* v_unused_4485_; 
v_unused_4478_ = lean_ctor_get(v_s_4403_, 7);
lean_dec(v_unused_4478_);
v_unused_4479_ = lean_ctor_get(v_s_4403_, 6);
lean_dec(v_unused_4479_);
v_unused_4480_ = lean_ctor_get(v_s_4403_, 5);
lean_dec(v_unused_4480_);
v_unused_4481_ = lean_ctor_get(v_s_4403_, 4);
lean_dec(v_unused_4481_);
v_unused_4482_ = lean_ctor_get(v_s_4403_, 3);
lean_dec(v_unused_4482_);
v_unused_4483_ = lean_ctor_get(v_s_4403_, 2);
lean_dec(v_unused_4483_);
v_unused_4484_ = lean_ctor_get(v_s_4403_, 1);
lean_dec(v_unused_4484_);
v_unused_4485_ = lean_ctor_get(v_s_4403_, 0);
lean_dec(v_unused_4485_);
v___x_4415_ = v_s_4403_;
v_isShared_4416_ = v_isSharedCheck_4477_;
goto v_resetjp_4414_;
}
else
{
lean_dec(v_s_4403_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4477_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v_v_4417_; lean_object* v_id_4418_; lean_object* v_ringId_x3f_4419_; lean_object* v_type_4420_; lean_object* v_u_4421_; lean_object* v_intModuleInst_4422_; lean_object* v_leInst_x3f_4423_; lean_object* v_ltInst_x3f_4424_; lean_object* v_lawfulOrderLTInst_x3f_4425_; lean_object* v_isPreorderInst_x3f_4426_; lean_object* v_orderedAddInst_x3f_4427_; lean_object* v_isLinearInst_x3f_4428_; lean_object* v_noNatDivInst_x3f_4429_; lean_object* v_ringInst_x3f_4430_; lean_object* v_commRingInst_x3f_4431_; lean_object* v_orderedRingInst_x3f_4432_; lean_object* v_fieldInst_x3f_4433_; lean_object* v_charInst_x3f_4434_; lean_object* v_zero_4435_; lean_object* v_ofNatZero_4436_; lean_object* v_one_x3f_4437_; lean_object* v_leFn_x3f_4438_; lean_object* v_ltFn_x3f_4439_; lean_object* v_addFn_4440_; lean_object* v_zsmulFn_4441_; lean_object* v_nsmulFn_4442_; lean_object* v_zsmulFn_x3f_4443_; lean_object* v_nsmulFn_x3f_4444_; lean_object* v_homomulFn_x3f_4445_; lean_object* v_subFn_4446_; lean_object* v_negFn_4447_; lean_object* v_vars_4448_; lean_object* v_varMap_4449_; lean_object* v_lowers_4450_; lean_object* v_uppers_4451_; lean_object* v_diseqs_4452_; lean_object* v_assignment_4453_; uint8_t v_caseSplits_4454_; lean_object* v_conflict_x3f_4455_; lean_object* v_diseqSplits_4456_; lean_object* v_elimEqs_4457_; lean_object* v_elimStack_4458_; lean_object* v_occurs_4459_; lean_object* v_ignored_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4476_; 
v_v_4417_ = lean_array_fget(v_structs_4404_, v___y_4400_);
v_id_4418_ = lean_ctor_get(v_v_4417_, 0);
v_ringId_x3f_4419_ = lean_ctor_get(v_v_4417_, 1);
v_type_4420_ = lean_ctor_get(v_v_4417_, 2);
v_u_4421_ = lean_ctor_get(v_v_4417_, 3);
v_intModuleInst_4422_ = lean_ctor_get(v_v_4417_, 4);
v_leInst_x3f_4423_ = lean_ctor_get(v_v_4417_, 5);
v_ltInst_x3f_4424_ = lean_ctor_get(v_v_4417_, 6);
v_lawfulOrderLTInst_x3f_4425_ = lean_ctor_get(v_v_4417_, 7);
v_isPreorderInst_x3f_4426_ = lean_ctor_get(v_v_4417_, 8);
v_orderedAddInst_x3f_4427_ = lean_ctor_get(v_v_4417_, 9);
v_isLinearInst_x3f_4428_ = lean_ctor_get(v_v_4417_, 10);
v_noNatDivInst_x3f_4429_ = lean_ctor_get(v_v_4417_, 11);
v_ringInst_x3f_4430_ = lean_ctor_get(v_v_4417_, 12);
v_commRingInst_x3f_4431_ = lean_ctor_get(v_v_4417_, 13);
v_orderedRingInst_x3f_4432_ = lean_ctor_get(v_v_4417_, 14);
v_fieldInst_x3f_4433_ = lean_ctor_get(v_v_4417_, 15);
v_charInst_x3f_4434_ = lean_ctor_get(v_v_4417_, 16);
v_zero_4435_ = lean_ctor_get(v_v_4417_, 17);
v_ofNatZero_4436_ = lean_ctor_get(v_v_4417_, 18);
v_one_x3f_4437_ = lean_ctor_get(v_v_4417_, 19);
v_leFn_x3f_4438_ = lean_ctor_get(v_v_4417_, 20);
v_ltFn_x3f_4439_ = lean_ctor_get(v_v_4417_, 21);
v_addFn_4440_ = lean_ctor_get(v_v_4417_, 22);
v_zsmulFn_4441_ = lean_ctor_get(v_v_4417_, 23);
v_nsmulFn_4442_ = lean_ctor_get(v_v_4417_, 24);
v_zsmulFn_x3f_4443_ = lean_ctor_get(v_v_4417_, 25);
v_nsmulFn_x3f_4444_ = lean_ctor_get(v_v_4417_, 26);
v_homomulFn_x3f_4445_ = lean_ctor_get(v_v_4417_, 27);
v_subFn_4446_ = lean_ctor_get(v_v_4417_, 28);
v_negFn_4447_ = lean_ctor_get(v_v_4417_, 29);
v_vars_4448_ = lean_ctor_get(v_v_4417_, 30);
v_varMap_4449_ = lean_ctor_get(v_v_4417_, 31);
v_lowers_4450_ = lean_ctor_get(v_v_4417_, 32);
v_uppers_4451_ = lean_ctor_get(v_v_4417_, 33);
v_diseqs_4452_ = lean_ctor_get(v_v_4417_, 34);
v_assignment_4453_ = lean_ctor_get(v_v_4417_, 35);
v_caseSplits_4454_ = lean_ctor_get_uint8(v_v_4417_, sizeof(void*)*42);
v_conflict_x3f_4455_ = lean_ctor_get(v_v_4417_, 36);
v_diseqSplits_4456_ = lean_ctor_get(v_v_4417_, 37);
v_elimEqs_4457_ = lean_ctor_get(v_v_4417_, 38);
v_elimStack_4458_ = lean_ctor_get(v_v_4417_, 39);
v_occurs_4459_ = lean_ctor_get(v_v_4417_, 40);
v_ignored_4460_ = lean_ctor_get(v_v_4417_, 41);
v_isSharedCheck_4476_ = !lean_is_exclusive(v_v_4417_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4462_ = v_v_4417_;
v_isShared_4463_ = v_isSharedCheck_4476_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_ignored_4460_);
lean_inc(v_occurs_4459_);
lean_inc(v_elimStack_4458_);
lean_inc(v_elimEqs_4457_);
lean_inc(v_diseqSplits_4456_);
lean_inc(v_conflict_x3f_4455_);
lean_inc(v_assignment_4453_);
lean_inc(v_diseqs_4452_);
lean_inc(v_uppers_4451_);
lean_inc(v_lowers_4450_);
lean_inc(v_varMap_4449_);
lean_inc(v_vars_4448_);
lean_inc(v_negFn_4447_);
lean_inc(v_subFn_4446_);
lean_inc(v_homomulFn_x3f_4445_);
lean_inc(v_nsmulFn_x3f_4444_);
lean_inc(v_zsmulFn_x3f_4443_);
lean_inc(v_nsmulFn_4442_);
lean_inc(v_zsmulFn_4441_);
lean_inc(v_addFn_4440_);
lean_inc(v_ltFn_x3f_4439_);
lean_inc(v_leFn_x3f_4438_);
lean_inc(v_one_x3f_4437_);
lean_inc(v_ofNatZero_4436_);
lean_inc(v_zero_4435_);
lean_inc(v_charInst_x3f_4434_);
lean_inc(v_fieldInst_x3f_4433_);
lean_inc(v_orderedRingInst_x3f_4432_);
lean_inc(v_commRingInst_x3f_4431_);
lean_inc(v_ringInst_x3f_4430_);
lean_inc(v_noNatDivInst_x3f_4429_);
lean_inc(v_isLinearInst_x3f_4428_);
lean_inc(v_orderedAddInst_x3f_4427_);
lean_inc(v_isPreorderInst_x3f_4426_);
lean_inc(v_lawfulOrderLTInst_x3f_4425_);
lean_inc(v_ltInst_x3f_4424_);
lean_inc(v_leInst_x3f_4423_);
lean_inc(v_intModuleInst_4422_);
lean_inc(v_u_4421_);
lean_inc(v_type_4420_);
lean_inc(v_ringId_x3f_4419_);
lean_inc(v_id_4418_);
lean_dec(v_v_4417_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4476_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4464_; lean_object* v_xs_x27_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4470_; 
v___x_4464_ = lean_box(0);
v_xs_x27_4465_ = lean_array_fset(v_structs_4404_, v___y_4400_, v___x_4464_);
v___x_4466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4466_, 0, v_snd_4401_);
v___x_4467_ = l_Lean_PersistentArray_set___redArg(v_elimEqs_4457_, v_fst_4402_, v___x_4466_);
v___x_4468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4468_, 0, v_fst_4402_);
lean_ctor_set(v___x_4468_, 1, v_elimStack_4458_);
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 39, v___x_4468_);
lean_ctor_set(v___x_4462_, 38, v___x_4467_);
v___x_4470_ = v___x_4462_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_id_4418_);
lean_ctor_set(v_reuseFailAlloc_4475_, 1, v_ringId_x3f_4419_);
lean_ctor_set(v_reuseFailAlloc_4475_, 2, v_type_4420_);
lean_ctor_set(v_reuseFailAlloc_4475_, 3, v_u_4421_);
lean_ctor_set(v_reuseFailAlloc_4475_, 4, v_intModuleInst_4422_);
lean_ctor_set(v_reuseFailAlloc_4475_, 5, v_leInst_x3f_4423_);
lean_ctor_set(v_reuseFailAlloc_4475_, 6, v_ltInst_x3f_4424_);
lean_ctor_set(v_reuseFailAlloc_4475_, 7, v_lawfulOrderLTInst_x3f_4425_);
lean_ctor_set(v_reuseFailAlloc_4475_, 8, v_isPreorderInst_x3f_4426_);
lean_ctor_set(v_reuseFailAlloc_4475_, 9, v_orderedAddInst_x3f_4427_);
lean_ctor_set(v_reuseFailAlloc_4475_, 10, v_isLinearInst_x3f_4428_);
lean_ctor_set(v_reuseFailAlloc_4475_, 11, v_noNatDivInst_x3f_4429_);
lean_ctor_set(v_reuseFailAlloc_4475_, 12, v_ringInst_x3f_4430_);
lean_ctor_set(v_reuseFailAlloc_4475_, 13, v_commRingInst_x3f_4431_);
lean_ctor_set(v_reuseFailAlloc_4475_, 14, v_orderedRingInst_x3f_4432_);
lean_ctor_set(v_reuseFailAlloc_4475_, 15, v_fieldInst_x3f_4433_);
lean_ctor_set(v_reuseFailAlloc_4475_, 16, v_charInst_x3f_4434_);
lean_ctor_set(v_reuseFailAlloc_4475_, 17, v_zero_4435_);
lean_ctor_set(v_reuseFailAlloc_4475_, 18, v_ofNatZero_4436_);
lean_ctor_set(v_reuseFailAlloc_4475_, 19, v_one_x3f_4437_);
lean_ctor_set(v_reuseFailAlloc_4475_, 20, v_leFn_x3f_4438_);
lean_ctor_set(v_reuseFailAlloc_4475_, 21, v_ltFn_x3f_4439_);
lean_ctor_set(v_reuseFailAlloc_4475_, 22, v_addFn_4440_);
lean_ctor_set(v_reuseFailAlloc_4475_, 23, v_zsmulFn_4441_);
lean_ctor_set(v_reuseFailAlloc_4475_, 24, v_nsmulFn_4442_);
lean_ctor_set(v_reuseFailAlloc_4475_, 25, v_zsmulFn_x3f_4443_);
lean_ctor_set(v_reuseFailAlloc_4475_, 26, v_nsmulFn_x3f_4444_);
lean_ctor_set(v_reuseFailAlloc_4475_, 27, v_homomulFn_x3f_4445_);
lean_ctor_set(v_reuseFailAlloc_4475_, 28, v_subFn_4446_);
lean_ctor_set(v_reuseFailAlloc_4475_, 29, v_negFn_4447_);
lean_ctor_set(v_reuseFailAlloc_4475_, 30, v_vars_4448_);
lean_ctor_set(v_reuseFailAlloc_4475_, 31, v_varMap_4449_);
lean_ctor_set(v_reuseFailAlloc_4475_, 32, v_lowers_4450_);
lean_ctor_set(v_reuseFailAlloc_4475_, 33, v_uppers_4451_);
lean_ctor_set(v_reuseFailAlloc_4475_, 34, v_diseqs_4452_);
lean_ctor_set(v_reuseFailAlloc_4475_, 35, v_assignment_4453_);
lean_ctor_set(v_reuseFailAlloc_4475_, 36, v_conflict_x3f_4455_);
lean_ctor_set(v_reuseFailAlloc_4475_, 37, v_diseqSplits_4456_);
lean_ctor_set(v_reuseFailAlloc_4475_, 38, v___x_4467_);
lean_ctor_set(v_reuseFailAlloc_4475_, 39, v___x_4468_);
lean_ctor_set(v_reuseFailAlloc_4475_, 40, v_occurs_4459_);
lean_ctor_set(v_reuseFailAlloc_4475_, 41, v_ignored_4460_);
lean_ctor_set_uint8(v_reuseFailAlloc_4475_, sizeof(void*)*42, v_caseSplits_4454_);
v___x_4470_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
lean_object* v___x_4471_; lean_object* v___x_4473_; 
v___x_4471_ = lean_array_fset(v_xs_x27_4465_, v___y_4400_, v___x_4470_);
if (v_isShared_4416_ == 0)
{
lean_ctor_set(v___x_4415_, 0, v___x_4471_);
v___x_4473_ = v___x_4415_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v___x_4471_);
lean_ctor_set(v_reuseFailAlloc_4474_, 1, v_typeIdOf_4405_);
lean_ctor_set(v_reuseFailAlloc_4474_, 2, v_exprToStructId_4406_);
lean_ctor_set(v_reuseFailAlloc_4474_, 3, v_exprToStructIdEntries_4407_);
lean_ctor_set(v_reuseFailAlloc_4474_, 4, v_forbiddenNatModules_4408_);
lean_ctor_set(v_reuseFailAlloc_4474_, 5, v_natStructs_4409_);
lean_ctor_set(v_reuseFailAlloc_4474_, 6, v_natTypeIdOf_4410_);
lean_ctor_set(v_reuseFailAlloc_4474_, 7, v_exprToNatStructId_4411_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed(lean_object* v___y_4486_, lean_object* v_snd_4487_, lean_object* v_fst_4488_, lean_object* v_s_4489_){
_start:
{
lean_object* v_res_4490_; 
v_res_4490_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(v___y_4486_, v_snd_4487_, v_fst_4488_, v_s_4489_);
lean_dec(v___y_4486_);
return v_res_4490_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1(void){
_start:
{
lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4492_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0));
v___x_4493_ = l_Lean_stringToMessageData(v___x_4492_);
return v___x_4493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object* v_c_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_){
_start:
{
lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v___y_4545_; lean_object* v___y_4546_; lean_object* v___y_4547_; lean_object* v___y_4548_; lean_object* v___y_4549_; lean_object* v___y_4550_; lean_object* v___y_4551_; lean_object* v___y_4552_; lean_object* v___y_4579_; lean_object* v___y_4580_; lean_object* v___y_4581_; lean_object* v___y_4582_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v___y_4590_; lean_object* v___y_4591_; lean_object* v___y_4592_; lean_object* v___y_4593_; lean_object* v___y_4594_; lean_object* v___y_4612_; lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4617_; lean_object* v___y_4618_; lean_object* v___y_4619_; lean_object* v___y_4620_; lean_object* v___y_4621_; lean_object* v___y_4622_; lean_object* v_cls_4710_; lean_object* v___x_4711_; lean_object* v_a_4712_; uint8_t v___x_4713_; 
v_cls_4710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0));
v___x_4711_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v_cls_4710_, v_a_4509_);
v_a_4712_ = lean_ctor_get(v___x_4711_, 0);
lean_inc(v_a_4712_);
lean_dec_ref(v___x_4711_);
v___x_4713_ = lean_unbox(v_a_4712_);
lean_dec(v_a_4712_);
if (v___x_4713_ == 0)
{
v___y_4612_ = v_a_4500_;
v___y_4613_ = v_a_4501_;
v___y_4614_ = v_a_4502_;
v___y_4615_ = v_a_4503_;
v___y_4616_ = v_a_4504_;
v___y_4617_ = v_a_4505_;
v___y_4618_ = v_a_4506_;
v___y_4619_ = v_a_4507_;
v___y_4620_ = v_a_4508_;
v___y_4621_ = v_a_4509_;
v___y_4622_ = v_a_4510_;
goto v___jp_4611_;
}
else
{
lean_object* v___x_4714_; 
v___x_4714_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_c_4499_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_);
if (lean_obj_tag(v___x_4714_) == 0)
{
lean_object* v_a_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; 
v_a_4715_ = lean_ctor_get(v___x_4714_, 0);
lean_inc(v_a_4715_);
lean_dec_ref(v___x_4714_);
v___x_4716_ = l_Lean_MessageData_ofExpr(v_a_4715_);
v___x_4717_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_4710_, v___x_4716_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_);
if (lean_obj_tag(v___x_4717_) == 0)
{
lean_dec_ref(v___x_4717_);
v___y_4612_ = v_a_4500_;
v___y_4613_ = v_a_4501_;
v___y_4614_ = v_a_4502_;
v___y_4615_ = v_a_4503_;
v___y_4616_ = v_a_4504_;
v___y_4617_ = v_a_4505_;
v___y_4618_ = v_a_4506_;
v___y_4619_ = v_a_4507_;
v___y_4620_ = v_a_4508_;
v___y_4621_ = v_a_4509_;
v___y_4622_ = v_a_4510_;
goto v___jp_4611_;
}
else
{
lean_dec_ref(v_c_4499_);
return v___x_4717_;
}
}
else
{
lean_object* v_a_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4725_; 
lean_dec_ref(v_c_4499_);
v_a_4718_ = lean_ctor_get(v___x_4714_, 0);
v_isSharedCheck_4725_ = !lean_is_exclusive(v___x_4714_);
if (v_isSharedCheck_4725_ == 0)
{
v___x_4720_ = v___x_4714_;
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_a_4718_);
lean_dec(v___x_4714_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4723_; 
if (v_isShared_4721_ == 0)
{
v___x_4723_ = v___x_4720_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_a_4718_);
v___x_4723_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
return v___x_4723_;
}
}
}
}
v___jp_4512_:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___x_4513_ = lean_box(0);
v___x_4514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4514_, 0, v___x_4513_);
return v___x_4514_;
}
v___jp_4515_:
{
lean_object* v___f_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
lean_inc(v___y_4521_);
v___f_4532_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4532_, 0, v___y_4521_);
lean_closure_set(v___f_4532_, 1, v___y_4517_);
lean_closure_set(v___f_4532_, 2, v___y_4516_);
v___x_4533_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4534_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4533_, v___f_4532_, v___y_4522_);
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_object* v___x_4535_; 
lean_dec_ref(v___x_4534_);
v___x_4535_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_);
return v___x_4535_;
}
else
{
lean_dec_ref(v___y_4520_);
lean_dec(v___y_4519_);
lean_dec(v___y_4518_);
return v___x_4534_;
}
}
v___jp_4536_:
{
lean_object* v___x_4553_; 
v___x_4553_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
if (lean_obj_tag(v___x_4553_) == 0)
{
lean_object* v_a_4554_; uint8_t v_caseSplits_4555_; 
v_a_4554_ = lean_ctor_get(v___x_4553_, 0);
lean_inc(v_a_4554_);
lean_dec_ref(v___x_4553_);
v_caseSplits_4555_ = lean_ctor_get_uint8(v_a_4554_, sizeof(void*)*42);
lean_dec(v_a_4554_);
if (v_caseSplits_4555_ == 0)
{
lean_object* v___x_4556_; 
v___x_4556_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
if (lean_obj_tag(v___x_4556_) == 0)
{
lean_object* v_a_4557_; uint8_t v___x_4558_; 
v_a_4557_ = lean_ctor_get(v___x_4556_, 0);
lean_inc(v_a_4557_);
lean_dec_ref(v___x_4556_);
v___x_4558_ = lean_unbox(v_a_4557_);
lean_dec(v_a_4557_);
if (v___x_4558_ == 0)
{
v___y_4516_ = v___y_4537_;
v___y_4517_ = v___y_4538_;
v___y_4518_ = v___y_4539_;
v___y_4519_ = v___y_4540_;
v___y_4520_ = v___y_4541_;
v___y_4521_ = v___y_4542_;
v___y_4522_ = v___y_4543_;
v___y_4523_ = v___y_4544_;
v___y_4524_ = v___y_4545_;
v___y_4525_ = v___y_4546_;
v___y_4526_ = v___y_4547_;
v___y_4527_ = v___y_4548_;
v___y_4528_ = v___y_4549_;
v___y_4529_ = v___y_4550_;
v___y_4530_ = v___y_4551_;
v___y_4531_ = v___y_4552_;
goto v___jp_4515_;
}
else
{
lean_object* v___x_4559_; lean_object* v_a_4560_; lean_object* v___x_4561_; 
lean_inc_ref(v___y_4541_);
v___x_4559_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v___y_4541_);
v_a_4560_ = lean_ctor_get(v___x_4559_, 0);
lean_inc(v_a_4560_);
lean_dec_ref(v___x_4559_);
v___x_4561_ = l_Lean_Meta_Grind_Arith_Linear_propagateImpEq(v_a_4560_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_dec_ref(v___x_4561_);
v___y_4516_ = v___y_4537_;
v___y_4517_ = v___y_4538_;
v___y_4518_ = v___y_4539_;
v___y_4519_ = v___y_4540_;
v___y_4520_ = v___y_4541_;
v___y_4521_ = v___y_4542_;
v___y_4522_ = v___y_4543_;
v___y_4523_ = v___y_4544_;
v___y_4524_ = v___y_4545_;
v___y_4525_ = v___y_4546_;
v___y_4526_ = v___y_4547_;
v___y_4527_ = v___y_4548_;
v___y_4528_ = v___y_4549_;
v___y_4529_ = v___y_4550_;
v___y_4530_ = v___y_4551_;
v___y_4531_ = v___y_4552_;
goto v___jp_4515_;
}
else
{
lean_dec_ref(v___y_4541_);
lean_dec(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec(v___y_4537_);
return v___x_4561_;
}
}
}
else
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4569_; 
lean_dec_ref(v___y_4541_);
lean_dec(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec(v___y_4537_);
v_a_4562_ = lean_ctor_get(v___x_4556_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4556_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4564_ = v___x_4556_;
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v___x_4556_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4567_; 
if (v_isShared_4565_ == 0)
{
v___x_4567_ = v___x_4564_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4562_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
}
}
else
{
v___y_4516_ = v___y_4537_;
v___y_4517_ = v___y_4538_;
v___y_4518_ = v___y_4539_;
v___y_4519_ = v___y_4540_;
v___y_4520_ = v___y_4541_;
v___y_4521_ = v___y_4542_;
v___y_4522_ = v___y_4543_;
v___y_4523_ = v___y_4544_;
v___y_4524_ = v___y_4545_;
v___y_4525_ = v___y_4546_;
v___y_4526_ = v___y_4547_;
v___y_4527_ = v___y_4548_;
v___y_4528_ = v___y_4549_;
v___y_4529_ = v___y_4550_;
v___y_4530_ = v___y_4551_;
v___y_4531_ = v___y_4552_;
goto v___jp_4515_;
}
}
else
{
lean_object* v_a_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4577_; 
lean_dec_ref(v___y_4541_);
lean_dec(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec(v___y_4537_);
v_a_4570_ = lean_ctor_get(v___x_4553_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4553_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4572_ = v___x_4553_;
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_a_4570_);
lean_dec(v___x_4553_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4575_; 
if (v_isShared_4573_ == 0)
{
v___x_4575_ = v___x_4572_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_a_4570_);
v___x_4575_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
return v___x_4575_;
}
}
}
}
v___jp_4578_:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v_a_4597_; uint8_t v___x_4598_; 
v___x_4595_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_4596_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_4595_, v___y_4593_);
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
lean_inc(v_a_4597_);
lean_dec_ref(v___x_4596_);
v___x_4598_ = lean_unbox(v_a_4597_);
lean_dec(v_a_4597_);
if (v___x_4598_ == 0)
{
v___y_4537_ = v___y_4579_;
v___y_4538_ = v___y_4580_;
v___y_4539_ = v___y_4581_;
v___y_4540_ = v___y_4582_;
v___y_4541_ = v___y_4583_;
v___y_4542_ = v___y_4584_;
v___y_4543_ = v___y_4585_;
v___y_4544_ = v___y_4586_;
v___y_4545_ = v___y_4587_;
v___y_4546_ = v___y_4588_;
v___y_4547_ = v___y_4589_;
v___y_4548_ = v___y_4590_;
v___y_4549_ = v___y_4591_;
v___y_4550_ = v___y_4592_;
v___y_4551_ = v___y_4593_;
v___y_4552_ = v___y_4594_;
goto v___jp_4536_;
}
else
{
lean_object* v___x_4599_; 
v___x_4599_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
if (lean_obj_tag(v___x_4599_) == 0)
{
lean_object* v_a_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; 
v_a_4600_ = lean_ctor_get(v___x_4599_, 0);
lean_inc(v_a_4600_);
lean_dec_ref(v___x_4599_);
v___x_4601_ = l_Lean_MessageData_ofExpr(v_a_4600_);
v___x_4602_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_4595_, v___x_4601_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_dec_ref(v___x_4602_);
v___y_4537_ = v___y_4579_;
v___y_4538_ = v___y_4580_;
v___y_4539_ = v___y_4581_;
v___y_4540_ = v___y_4582_;
v___y_4541_ = v___y_4583_;
v___y_4542_ = v___y_4584_;
v___y_4543_ = v___y_4585_;
v___y_4544_ = v___y_4586_;
v___y_4545_ = v___y_4587_;
v___y_4546_ = v___y_4588_;
v___y_4547_ = v___y_4589_;
v___y_4548_ = v___y_4590_;
v___y_4549_ = v___y_4591_;
v___y_4550_ = v___y_4592_;
v___y_4551_ = v___y_4593_;
v___y_4552_ = v___y_4594_;
goto v___jp_4536_;
}
else
{
lean_dec_ref(v___y_4583_);
lean_dec(v___y_4582_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec(v___y_4579_);
return v___x_4602_;
}
}
else
{
lean_object* v_a_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4610_; 
lean_dec_ref(v___y_4583_);
lean_dec(v___y_4582_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec(v___y_4579_);
v_a_4603_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4610_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4610_ == 0)
{
v___x_4605_ = v___x_4599_;
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_a_4603_);
lean_dec(v___x_4599_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4608_; 
if (v_isShared_4606_ == 0)
{
v___x_4608_ = v___x_4605_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_a_4603_);
v___x_4608_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
return v___x_4608_;
}
}
}
}
}
v___jp_4611_:
{
lean_object* v___x_4623_; 
lean_inc_ref(v___y_4621_);
v___x_4623_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_4499_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_object* v_a_4624_; lean_object* v_p_4625_; lean_object* v___x_4626_; uint8_t v___x_4627_; 
v_a_4624_ = lean_ctor_get(v___x_4623_, 0);
lean_inc(v_a_4624_);
lean_dec_ref(v___x_4623_);
v_p_4625_ = lean_ctor_get(v_a_4624_, 0);
v___x_4626_ = lean_box(0);
v___x_4627_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_4625_, v___x_4626_);
if (v___x_4627_ == 0)
{
lean_object* v___x_4628_; 
v___x_4628_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_a_4624_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
if (lean_obj_tag(v___x_4628_) == 0)
{
lean_object* v_a_4629_; lean_object* v_snd_4630_; lean_object* v_fst_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4677_; 
v_a_4629_ = lean_ctor_get(v___x_4628_, 0);
lean_inc(v_a_4629_);
lean_dec_ref(v___x_4628_);
v_snd_4630_ = lean_ctor_get(v_a_4629_, 1);
v_fst_4631_ = lean_ctor_get(v_a_4629_, 0);
v_isSharedCheck_4677_ = !lean_is_exclusive(v_a_4629_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4633_ = v_a_4629_;
v_isShared_4634_ = v_isSharedCheck_4677_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_snd_4630_);
lean_inc(v_fst_4631_);
lean_dec(v_a_4629_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4677_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v_fst_4635_; lean_object* v_snd_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4676_; 
v_fst_4635_ = lean_ctor_get(v_snd_4630_, 0);
v_snd_4636_ = lean_ctor_get(v_snd_4630_, 1);
v_isSharedCheck_4676_ = !lean_is_exclusive(v_snd_4630_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4638_ = v_snd_4630_;
v_isShared_4639_ = v_isSharedCheck_4676_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_snd_4636_);
lean_inc(v_fst_4635_);
lean_dec(v_snd_4630_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4676_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v_a_4642_; uint8_t v___x_4643_; 
v___x_4640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_4641_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_4640_, v___y_4621_);
v_a_4642_ = lean_ctor_get(v___x_4641_, 0);
lean_inc(v_a_4642_);
lean_dec_ref(v___x_4641_);
v___x_4643_ = lean_unbox(v_a_4642_);
lean_dec(v_a_4642_);
if (v___x_4643_ == 0)
{
lean_del_object(v___x_4638_);
lean_del_object(v___x_4633_);
lean_inc(v_snd_4636_);
lean_inc(v_fst_4635_);
v___y_4579_ = v_fst_4635_;
v___y_4580_ = v_snd_4636_;
v___y_4581_ = v_fst_4631_;
v___y_4582_ = v_fst_4635_;
v___y_4583_ = v_snd_4636_;
v___y_4584_ = v___y_4612_;
v___y_4585_ = v___y_4613_;
v___y_4586_ = v___y_4614_;
v___y_4587_ = v___y_4615_;
v___y_4588_ = v___y_4616_;
v___y_4589_ = v___y_4617_;
v___y_4590_ = v___y_4618_;
v___y_4591_ = v___y_4619_;
v___y_4592_ = v___y_4620_;
v___y_4593_ = v___y_4621_;
v___y_4594_ = v___y_4622_;
goto v___jp_4578_;
}
else
{
lean_object* v___x_4644_; 
v___x_4644_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_4635_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_object* v_a_4645_; lean_object* v___x_4646_; 
v_a_4645_ = lean_ctor_get(v___x_4644_, 0);
lean_inc(v_a_4645_);
lean_dec_ref(v___x_4644_);
v___x_4646_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_snd_4636_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v_a_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4651_; 
v_a_4647_ = lean_ctor_get(v___x_4646_, 0);
lean_inc(v_a_4647_);
lean_dec_ref(v___x_4646_);
v___x_4648_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1);
v___x_4649_ = l_Lean_MessageData_ofExpr(v_a_4645_);
if (v_isShared_4639_ == 0)
{
lean_ctor_set_tag(v___x_4638_, 7);
lean_ctor_set(v___x_4638_, 1, v___x_4649_);
lean_ctor_set(v___x_4638_, 0, v___x_4648_);
v___x_4651_ = v___x_4638_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v___x_4648_);
lean_ctor_set(v_reuseFailAlloc_4659_, 1, v___x_4649_);
v___x_4651_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
lean_object* v___x_4652_; lean_object* v___x_4654_; 
v___x_4652_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6);
if (v_isShared_4634_ == 0)
{
lean_ctor_set_tag(v___x_4633_, 7);
lean_ctor_set(v___x_4633_, 1, v___x_4652_);
lean_ctor_set(v___x_4633_, 0, v___x_4651_);
v___x_4654_ = v___x_4633_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v___x_4651_);
lean_ctor_set(v_reuseFailAlloc_4658_, 1, v___x_4652_);
v___x_4654_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4655_ = l_Lean_MessageData_ofExpr(v_a_4647_);
v___x_4656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4656_, 0, v___x_4654_);
lean_ctor_set(v___x_4656_, 1, v___x_4655_);
v___x_4657_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_4640_, v___x_4656_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
if (lean_obj_tag(v___x_4657_) == 0)
{
lean_dec_ref(v___x_4657_);
lean_inc(v_snd_4636_);
lean_inc(v_fst_4635_);
v___y_4579_ = v_fst_4635_;
v___y_4580_ = v_snd_4636_;
v___y_4581_ = v_fst_4631_;
v___y_4582_ = v_fst_4635_;
v___y_4583_ = v_snd_4636_;
v___y_4584_ = v___y_4612_;
v___y_4585_ = v___y_4613_;
v___y_4586_ = v___y_4614_;
v___y_4587_ = v___y_4615_;
v___y_4588_ = v___y_4616_;
v___y_4589_ = v___y_4617_;
v___y_4590_ = v___y_4618_;
v___y_4591_ = v___y_4619_;
v___y_4592_ = v___y_4620_;
v___y_4593_ = v___y_4621_;
v___y_4594_ = v___y_4622_;
goto v___jp_4578_;
}
else
{
lean_dec(v_snd_4636_);
lean_dec(v_fst_4635_);
lean_dec(v_fst_4631_);
return v___x_4657_;
}
}
}
}
else
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4667_; 
lean_dec(v_a_4645_);
lean_del_object(v___x_4638_);
lean_dec(v_snd_4636_);
lean_dec(v_fst_4635_);
lean_del_object(v___x_4633_);
lean_dec(v_fst_4631_);
v_a_4660_ = lean_ctor_get(v___x_4646_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4646_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4662_ = v___x_4646_;
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___x_4646_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v___x_4665_; 
if (v_isShared_4663_ == 0)
{
v___x_4665_ = v___x_4662_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_a_4660_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
}
else
{
lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4675_; 
lean_del_object(v___x_4638_);
lean_dec(v_snd_4636_);
lean_dec(v_fst_4635_);
lean_del_object(v___x_4633_);
lean_dec(v_fst_4631_);
v_a_4668_ = lean_ctor_get(v___x_4644_, 0);
v_isSharedCheck_4675_ = !lean_is_exclusive(v___x_4644_);
if (v_isSharedCheck_4675_ == 0)
{
v___x_4670_ = v___x_4644_;
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_dec(v___x_4644_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4673_; 
if (v_isShared_4671_ == 0)
{
v___x_4673_ = v___x_4670_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_a_4668_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
return v___x_4673_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4685_; 
v_a_4678_ = lean_ctor_get(v___x_4628_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4628_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4680_ = v___x_4628_;
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_dec(v___x_4628_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4683_; 
if (v_isShared_4681_ == 0)
{
v___x_4683_ = v___x_4680_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_a_4678_);
v___x_4683_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
return v___x_4683_;
}
}
}
}
else
{
lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v_a_4688_; uint8_t v___x_4689_; 
v___x_4686_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4687_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_4686_, v___y_4621_);
v_a_4688_ = lean_ctor_get(v___x_4687_, 0);
lean_inc(v_a_4688_);
lean_dec_ref(v___x_4687_);
v___x_4689_ = lean_unbox(v_a_4688_);
lean_dec(v_a_4688_);
if (v___x_4689_ == 0)
{
lean_dec(v_a_4624_);
goto v___jp_4512_;
}
else
{
lean_object* v___x_4690_; 
v___x_4690_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_a_4624_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
lean_dec(v_a_4624_);
if (lean_obj_tag(v___x_4690_) == 0)
{
lean_object* v_a_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; 
v_a_4691_ = lean_ctor_get(v___x_4690_, 0);
lean_inc(v_a_4691_);
lean_dec_ref(v___x_4690_);
v___x_4692_ = l_Lean_MessageData_ofExpr(v_a_4691_);
v___x_4693_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_4686_, v___x_4692_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
if (lean_obj_tag(v___x_4693_) == 0)
{
lean_dec_ref(v___x_4693_);
goto v___jp_4512_;
}
else
{
return v___x_4693_;
}
}
else
{
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4701_; 
v_a_4694_ = lean_ctor_get(v___x_4690_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4690_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4696_ = v___x_4690_;
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___x_4690_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4699_; 
if (v_isShared_4697_ == 0)
{
v___x_4699_ = v___x_4696_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
v___x_4699_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
return v___x_4699_;
}
}
}
}
}
}
else
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4709_; 
v_a_4702_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4704_ = v___x_4623_;
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4623_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4707_; 
if (v_isShared_4705_ == 0)
{
v___x_4707_ = v___x_4704_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_a_4702_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object* v_c_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_){
_start:
{
lean_object* v_res_4739_; 
v_res_4739_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v_c_4726_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_, v_a_4736_, v_a_4737_);
lean_dec(v_a_4737_);
lean_dec_ref(v_a_4736_);
lean_dec(v_a_4735_);
lean_dec_ref(v_a_4734_);
lean_dec(v_a_4733_);
lean_dec_ref(v_a_4732_);
lean_dec(v_a_4731_);
lean_dec_ref(v_a_4730_);
lean_dec(v_a_4729_);
lean_dec(v_a_4728_);
lean_dec(v_a_4727_);
return v_res_4739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object* v_a_4744_, lean_object* v_b_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_){
_start:
{
lean_object* v_cls_4751_; lean_object* v___x_4752_; lean_object* v_a_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4768_; 
v_cls_4751_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4752_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v_cls_4751_, v_a_4748_);
v_a_4753_ = lean_ctor_get(v___x_4752_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4752_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4755_ = v___x_4752_;
v_isShared_4756_ = v_isSharedCheck_4768_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_a_4753_);
lean_dec(v___x_4752_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4768_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
uint8_t v___x_4757_; 
v___x_4757_ = lean_unbox(v_a_4753_);
lean_dec(v_a_4753_);
if (v___x_4757_ == 0)
{
lean_object* v___x_4758_; lean_object* v___x_4760_; 
lean_dec_ref(v_b_4745_);
lean_dec_ref(v_a_4744_);
v___x_4758_ = lean_box(0);
if (v_isShared_4756_ == 0)
{
lean_ctor_set(v___x_4755_, 0, v___x_4758_);
v___x_4760_ = v___x_4755_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v___x_4758_);
v___x_4760_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
return v___x_4760_;
}
}
else
{
lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; 
lean_del_object(v___x_4755_);
v___x_4762_ = l_Lean_MessageData_ofExpr(v_a_4744_);
v___x_4763_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6);
v___x_4764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4764_, 0, v___x_4762_);
lean_ctor_set(v___x_4764_, 1, v___x_4763_);
v___x_4765_ = l_Lean_MessageData_ofExpr(v_b_4745_);
v___x_4766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4766_, 0, v___x_4764_);
lean_ctor_set(v___x_4766_, 1, v___x_4765_);
v___x_4767_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_4751_, v___x_4766_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_);
return v___x_4767_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object* v_a_4769_, lean_object* v_b_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_){
_start:
{
lean_object* v_res_4776_; 
v_res_4776_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4769_, v_b_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_);
lean_dec(v_a_4774_);
lean_dec_ref(v_a_4773_);
lean_dec(v_a_4772_);
lean_dec_ref(v_a_4771_);
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object* v_a_4777_, lean_object* v_b_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_){
_start:
{
lean_object* v___x_4791_; 
v___x_4791_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4777_, v_b_4778_, v_a_4786_, v_a_4787_, v_a_4788_, v_a_4789_);
return v___x_4791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object* v_a_4792_, lean_object* v_b_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_){
_start:
{
lean_object* v_res_4806_; 
v_res_4806_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(v_a_4792_, v_b_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
lean_dec(v_a_4804_);
lean_dec_ref(v_a_4803_);
lean_dec(v_a_4802_);
lean_dec_ref(v_a_4801_);
lean_dec(v_a_4800_);
lean_dec_ref(v_a_4799_);
lean_dec(v_a_4798_);
lean_dec_ref(v_a_4797_);
lean_dec(v_a_4796_);
lean_dec(v_a_4795_);
lean_dec(v_a_4794_);
return v_res_4806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object* v_a_4807_, lean_object* v_b_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_){
_start:
{
lean_object* v___x_4821_; 
v___x_4821_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4807_, v_a_4810_);
if (lean_obj_tag(v___x_4821_) == 0)
{
lean_object* v_a_4822_; uint8_t v___x_4823_; lean_object* v___x_4824_; 
v_a_4822_ = lean_ctor_get(v___x_4821_, 0);
lean_inc(v_a_4822_);
lean_dec_ref(v___x_4821_);
v___x_4823_ = 0;
lean_inc_ref(v_a_4807_);
v___x_4824_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_4807_, v___x_4823_, v_a_4822_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_);
if (lean_obj_tag(v___x_4824_) == 0)
{
lean_object* v_a_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4874_; 
v_a_4825_ = lean_ctor_get(v___x_4824_, 0);
v_isSharedCheck_4874_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4874_ == 0)
{
v___x_4827_ = v___x_4824_;
v_isShared_4828_ = v_isSharedCheck_4874_;
goto v_resetjp_4826_;
}
else
{
lean_inc(v_a_4825_);
lean_dec(v___x_4824_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_4874_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
if (lean_obj_tag(v_a_4825_) == 1)
{
lean_object* v_val_4829_; lean_object* v___x_4830_; 
lean_del_object(v___x_4827_);
v_val_4829_ = lean_ctor_get(v_a_4825_, 0);
lean_inc(v_val_4829_);
lean_dec_ref(v_a_4825_);
v___x_4830_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4808_, v_a_4810_);
if (lean_obj_tag(v___x_4830_) == 0)
{
lean_object* v_a_4831_; lean_object* v___x_4832_; 
v_a_4831_ = lean_ctor_get(v___x_4830_, 0);
lean_inc(v_a_4831_);
lean_dec_ref(v___x_4830_);
lean_inc_ref(v_b_4808_);
v___x_4832_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_4808_, v___x_4823_, v_a_4831_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_);
if (lean_obj_tag(v___x_4832_) == 0)
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4853_; 
v_a_4833_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4853_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4835_ = v___x_4832_;
v_isShared_4836_ = v_isSharedCheck_4853_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4832_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4853_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
if (lean_obj_tag(v_a_4833_) == 1)
{
lean_object* v_val_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; uint8_t v___x_4841_; 
v_val_4837_ = lean_ctor_get(v_a_4833_, 0);
lean_inc(v_val_4837_);
lean_dec_ref(v_a_4833_);
lean_inc(v_val_4837_);
lean_inc(v_val_4829_);
v___x_4838_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4838_, 0, v_val_4829_);
lean_ctor_set(v___x_4838_, 1, v_val_4837_);
v___x_4839_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4838_);
v___x_4840_ = lean_box(0);
v___x_4841_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4839_, v___x_4840_);
if (v___x_4841_ == 0)
{
lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; 
lean_del_object(v___x_4835_);
v___x_4842_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4842_, 0, v_a_4807_);
lean_ctor_set(v___x_4842_, 1, v_b_4808_);
lean_ctor_set(v___x_4842_, 2, v_val_4829_);
lean_ctor_set(v___x_4842_, 3, v_val_4837_);
v___x_4843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4843_, 0, v___x_4839_);
lean_ctor_set(v___x_4843_, 1, v___x_4842_);
v___x_4844_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_4843_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_);
return v___x_4844_;
}
else
{
lean_object* v___x_4845_; lean_object* v___x_4847_; 
lean_dec(v___x_4839_);
lean_dec(v_val_4837_);
lean_dec(v_val_4829_);
lean_dec_ref(v_b_4808_);
lean_dec_ref(v_a_4807_);
v___x_4845_ = lean_box(0);
if (v_isShared_4836_ == 0)
{
lean_ctor_set(v___x_4835_, 0, v___x_4845_);
v___x_4847_ = v___x_4835_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v___x_4845_);
v___x_4847_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
return v___x_4847_;
}
}
}
else
{
lean_object* v___x_4849_; lean_object* v___x_4851_; 
lean_dec(v_a_4833_);
lean_dec(v_val_4829_);
lean_dec_ref(v_b_4808_);
lean_dec_ref(v_a_4807_);
v___x_4849_ = lean_box(0);
if (v_isShared_4836_ == 0)
{
lean_ctor_set(v___x_4835_, 0, v___x_4849_);
v___x_4851_ = v___x_4835_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v___x_4849_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
return v___x_4851_;
}
}
}
}
else
{
lean_object* v_a_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4861_; 
lean_dec(v_val_4829_);
lean_dec_ref(v_b_4808_);
lean_dec_ref(v_a_4807_);
v_a_4854_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4856_ = v___x_4832_;
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_a_4854_);
lean_dec(v___x_4832_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
lean_object* v___x_4859_; 
if (v_isShared_4857_ == 0)
{
v___x_4859_ = v___x_4856_;
goto v_reusejp_4858_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v_a_4854_);
v___x_4859_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4858_;
}
v_reusejp_4858_:
{
return v___x_4859_;
}
}
}
}
else
{
lean_object* v_a_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4869_; 
lean_dec(v_val_4829_);
lean_dec_ref(v_b_4808_);
lean_dec_ref(v_a_4807_);
v_a_4862_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4869_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4869_ == 0)
{
v___x_4864_ = v___x_4830_;
v_isShared_4865_ = v_isSharedCheck_4869_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_a_4862_);
lean_dec(v___x_4830_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4869_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
lean_object* v___x_4867_; 
if (v_isShared_4865_ == 0)
{
v___x_4867_ = v___x_4864_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v_a_4862_);
v___x_4867_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
return v___x_4867_;
}
}
}
}
else
{
lean_object* v___x_4870_; lean_object* v___x_4872_; 
lean_dec(v_a_4825_);
lean_dec_ref(v_b_4808_);
lean_dec_ref(v_a_4807_);
v___x_4870_ = lean_box(0);
if (v_isShared_4828_ == 0)
{
lean_ctor_set(v___x_4827_, 0, v___x_4870_);
v___x_4872_ = v___x_4827_;
goto v_reusejp_4871_;
}
else
{
lean_object* v_reuseFailAlloc_4873_; 
v_reuseFailAlloc_4873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4873_, 0, v___x_4870_);
v___x_4872_ = v_reuseFailAlloc_4873_;
goto v_reusejp_4871_;
}
v_reusejp_4871_:
{
return v___x_4872_;
}
}
}
}
else
{
lean_object* v_a_4875_; lean_object* v___x_4877_; uint8_t v_isShared_4878_; uint8_t v_isSharedCheck_4882_; 
lean_dec_ref(v_b_4808_);
lean_dec_ref(v_a_4807_);
v_a_4875_ = lean_ctor_get(v___x_4824_, 0);
v_isSharedCheck_4882_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4882_ == 0)
{
v___x_4877_ = v___x_4824_;
v_isShared_4878_ = v_isSharedCheck_4882_;
goto v_resetjp_4876_;
}
else
{
lean_inc(v_a_4875_);
lean_dec(v___x_4824_);
v___x_4877_ = lean_box(0);
v_isShared_4878_ = v_isSharedCheck_4882_;
goto v_resetjp_4876_;
}
v_resetjp_4876_:
{
lean_object* v___x_4880_; 
if (v_isShared_4878_ == 0)
{
v___x_4880_ = v___x_4877_;
goto v_reusejp_4879_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v_a_4875_);
v___x_4880_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4879_;
}
v_reusejp_4879_:
{
return v___x_4880_;
}
}
}
}
else
{
lean_object* v_a_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4890_; 
lean_dec_ref(v_b_4808_);
lean_dec_ref(v_a_4807_);
v_a_4883_ = lean_ctor_get(v___x_4821_, 0);
v_isSharedCheck_4890_ = !lean_is_exclusive(v___x_4821_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4885_ = v___x_4821_;
v_isShared_4886_ = v_isSharedCheck_4890_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_a_4883_);
lean_dec(v___x_4821_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4890_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
lean_object* v___x_4888_; 
if (v_isShared_4886_ == 0)
{
v___x_4888_ = v___x_4885_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v_a_4883_);
v___x_4888_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
return v___x_4888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___boxed(lean_object* v_a_4891_, lean_object* v_b_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_){
_start:
{
lean_object* v_res_4905_; 
v_res_4905_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_4891_, v_b_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_);
lean_dec(v_a_4903_);
lean_dec_ref(v_a_4902_);
lean_dec(v_a_4901_);
lean_dec_ref(v_a_4900_);
lean_dec(v_a_4899_);
lean_dec_ref(v_a_4898_);
lean_dec(v_a_4897_);
lean_dec_ref(v_a_4896_);
lean_dec(v_a_4895_);
lean_dec(v_a_4894_);
lean_dec(v_a_4893_);
return v_res_4905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(lean_object* v_a_4906_, lean_object* v_b_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_){
_start:
{
lean_object* v___x_4920_; 
v___x_4920_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_);
if (lean_obj_tag(v___x_4920_) == 0)
{
lean_object* v_a_4921_; lean_object* v___x_4922_; 
v_a_4921_ = lean_ctor_get(v___x_4920_, 0);
lean_inc(v_a_4921_);
lean_dec_ref(v___x_4920_);
lean_inc_ref(v_a_4906_);
v___x_4922_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_4906_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_);
if (lean_obj_tag(v___x_4922_) == 0)
{
lean_object* v_a_4923_; lean_object* v_fst_4924_; lean_object* v___x_4925_; 
v_a_4923_ = lean_ctor_get(v___x_4922_, 0);
lean_inc(v_a_4923_);
lean_dec_ref(v___x_4922_);
v_fst_4924_ = lean_ctor_get(v_a_4923_, 0);
lean_inc(v_fst_4924_);
lean_dec(v_a_4923_);
lean_inc_ref(v_b_4907_);
v___x_4925_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_);
if (lean_obj_tag(v___x_4925_) == 0)
{
lean_object* v_a_4926_; lean_object* v_fst_4927_; lean_object* v___x_4929_; uint8_t v_isShared_4930_; uint8_t v_isSharedCheck_5010_; 
v_a_4926_ = lean_ctor_get(v___x_4925_, 0);
lean_inc(v_a_4926_);
lean_dec_ref(v___x_4925_);
v_fst_4927_ = lean_ctor_get(v_a_4926_, 0);
v_isSharedCheck_5010_ = !lean_is_exclusive(v_a_4926_);
if (v_isSharedCheck_5010_ == 0)
{
lean_object* v_unused_5011_; 
v_unused_5011_ = lean_ctor_get(v_a_4926_, 1);
lean_dec(v_unused_5011_);
v___x_4929_ = v_a_4926_;
v_isShared_4930_ = v_isSharedCheck_5010_;
goto v_resetjp_4928_;
}
else
{
lean_inc(v_fst_4927_);
lean_dec(v_a_4926_);
v___x_4929_ = lean_box(0);
v_isShared_4930_ = v_isSharedCheck_5010_;
goto v_resetjp_4928_;
}
v_resetjp_4928_:
{
lean_object* v___x_4931_; 
v___x_4931_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4906_, v_a_4909_);
if (lean_obj_tag(v___x_4931_) == 0)
{
lean_object* v_a_4932_; lean_object* v_id_4933_; lean_object* v_structId_4934_; uint8_t v___x_4935_; lean_object* v___x_4936_; 
v_a_4932_ = lean_ctor_get(v___x_4931_, 0);
lean_inc(v_a_4932_);
lean_dec_ref(v___x_4931_);
v_id_4933_ = lean_ctor_get(v_a_4921_, 0);
lean_inc(v_id_4933_);
v_structId_4934_ = lean_ctor_get(v_a_4921_, 1);
lean_inc(v_structId_4934_);
lean_dec(v_a_4921_);
v___x_4935_ = 0;
v___x_4936_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4924_, v___x_4935_, v_a_4932_, v_structId_4934_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v_a_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4993_; 
v_a_4937_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_4993_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4993_ == 0)
{
v___x_4939_ = v___x_4936_;
v_isShared_4940_ = v_isSharedCheck_4993_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_a_4937_);
lean_dec(v___x_4936_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4993_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
if (lean_obj_tag(v_a_4937_) == 1)
{
lean_object* v_val_4941_; lean_object* v___x_4942_; 
lean_del_object(v___x_4939_);
v_val_4941_ = lean_ctor_get(v_a_4937_, 0);
lean_inc(v_val_4941_);
lean_dec_ref(v_a_4937_);
v___x_4942_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4907_, v_a_4909_);
if (lean_obj_tag(v___x_4942_) == 0)
{
lean_object* v_a_4943_; lean_object* v___x_4944_; 
v_a_4943_ = lean_ctor_get(v___x_4942_, 0);
lean_inc(v_a_4943_);
lean_dec_ref(v___x_4942_);
v___x_4944_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4927_, v___x_4935_, v_a_4943_, v_structId_4934_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_);
if (lean_obj_tag(v___x_4944_) == 0)
{
lean_object* v_a_4945_; lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_4972_; 
v_a_4945_ = lean_ctor_get(v___x_4944_, 0);
v_isSharedCheck_4972_ = !lean_is_exclusive(v___x_4944_);
if (v_isSharedCheck_4972_ == 0)
{
v___x_4947_ = v___x_4944_;
v_isShared_4948_ = v_isSharedCheck_4972_;
goto v_resetjp_4946_;
}
else
{
lean_inc(v_a_4945_);
lean_dec(v___x_4944_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_4972_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
if (lean_obj_tag(v_a_4945_) == 1)
{
lean_object* v_val_4949_; lean_object* v___x_4951_; 
v_val_4949_ = lean_ctor_get(v_a_4945_, 0);
lean_inc(v_val_4949_);
lean_dec_ref(v_a_4945_);
lean_inc(v_val_4949_);
lean_inc(v_val_4941_);
if (v_isShared_4930_ == 0)
{
lean_ctor_set_tag(v___x_4929_, 3);
lean_ctor_set(v___x_4929_, 1, v_val_4949_);
lean_ctor_set(v___x_4929_, 0, v_val_4941_);
v___x_4951_ = v___x_4929_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_val_4941_);
lean_ctor_set(v_reuseFailAlloc_4967_, 1, v_val_4949_);
v___x_4951_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
lean_object* v___x_4952_; lean_object* v___x_4953_; uint8_t v___x_4954_; 
v___x_4952_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4951_);
v___x_4953_ = lean_box(0);
v___x_4954_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4952_, v___x_4953_);
if (v___x_4954_ == 0)
{
lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; 
lean_del_object(v___x_4947_);
lean_inc(v_val_4949_);
lean_inc(v_val_4941_);
lean_inc(v_id_4933_);
lean_inc_ref(v_b_4907_);
lean_inc_ref(v_a_4906_);
v___x_4955_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4955_, 0, v_a_4906_);
lean_ctor_set(v___x_4955_, 1, v_b_4907_);
lean_ctor_set(v___x_4955_, 2, v_id_4933_);
lean_ctor_set(v___x_4955_, 3, v_val_4941_);
lean_ctor_set(v___x_4955_, 4, v_val_4949_);
lean_inc(v___x_4952_);
v___x_4956_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4956_, 0, v___x_4952_);
lean_ctor_set(v___x_4956_, 1, v___x_4955_);
lean_ctor_set_uint8(v___x_4956_, sizeof(void*)*2, v___x_4935_);
v___x_4957_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4956_, v_structId_4934_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_);
if (lean_obj_tag(v___x_4957_) == 0)
{
lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; 
lean_dec_ref(v___x_4957_);
v___x_4958_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4959_ = l_Lean_Grind_Linarith_Poly_mul(v___x_4952_, v___x_4958_);
v___x_4960_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4960_, 0, v_b_4907_);
lean_ctor_set(v___x_4960_, 1, v_a_4906_);
lean_ctor_set(v___x_4960_, 2, v_id_4933_);
lean_ctor_set(v___x_4960_, 3, v_val_4949_);
lean_ctor_set(v___x_4960_, 4, v_val_4941_);
v___x_4961_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4961_, 0, v___x_4959_);
lean_ctor_set(v___x_4961_, 1, v___x_4960_);
lean_ctor_set_uint8(v___x_4961_, sizeof(void*)*2, v___x_4935_);
v___x_4962_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4961_, v_structId_4934_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_);
lean_dec(v_structId_4934_);
return v___x_4962_;
}
else
{
lean_dec(v___x_4952_);
lean_dec(v_val_4949_);
lean_dec(v_val_4941_);
lean_dec(v_structId_4934_);
lean_dec(v_id_4933_);
lean_dec_ref(v_b_4907_);
lean_dec_ref(v_a_4906_);
return v___x_4957_;
}
}
else
{
lean_object* v___x_4963_; lean_object* v___x_4965_; 
lean_dec(v___x_4952_);
lean_dec(v_val_4949_);
lean_dec(v_val_4941_);
lean_dec(v_structId_4934_);
lean_dec(v_id_4933_);
lean_dec_ref(v_b_4907_);
lean_dec_ref(v_a_4906_);
v___x_4963_ = lean_box(0);
if (v_isShared_4948_ == 0)
{
lean_ctor_set(v___x_4947_, 0, v___x_4963_);
v___x_4965_ = v___x_4947_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v___x_4963_);
v___x_4965_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4964_;
}
v_reusejp_4964_:
{
return v___x_4965_;
}
}
}
}
else
{
lean_object* v___x_4968_; lean_object* v___x_4970_; 
lean_dec(v_a_4945_);
lean_dec(v_val_4941_);
lean_dec(v_structId_4934_);
lean_dec(v_id_4933_);
lean_del_object(v___x_4929_);
lean_dec_ref(v_b_4907_);
lean_dec_ref(v_a_4906_);
v___x_4968_ = lean_box(0);
if (v_isShared_4948_ == 0)
{
lean_ctor_set(v___x_4947_, 0, v___x_4968_);
v___x_4970_ = v___x_4947_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4971_; 
v_reuseFailAlloc_4971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4971_, 0, v___x_4968_);
v___x_4970_ = v_reuseFailAlloc_4971_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
return v___x_4970_;
}
}
}
}
else
{
lean_object* v_a_4973_; lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_4980_; 
lean_dec(v_val_4941_);
lean_dec(v_structId_4934_);
lean_dec(v_id_4933_);
lean_del_object(v___x_4929_);
lean_dec_ref(v_b_4907_);
lean_dec_ref(v_a_4906_);
v_a_4973_ = lean_ctor_get(v___x_4944_, 0);
v_isSharedCheck_4980_ = !lean_is_exclusive(v___x_4944_);
if (v_isSharedCheck_4980_ == 0)
{
v___x_4975_ = v___x_4944_;
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
else
{
lean_inc(v_a_4973_);
lean_dec(v___x_4944_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
lean_object* v___x_4978_; 
if (v_isShared_4976_ == 0)
{
v___x_4978_ = v___x_4975_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_a_4973_);
v___x_4978_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
return v___x_4978_;
}
}
}
}
else
{
lean_object* v_a_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4988_; 
lean_dec(v_val_4941_);
lean_dec(v_structId_4934_);
lean_dec(v_id_4933_);
lean_del_object(v___x_4929_);
lean_dec(v_fst_4927_);
lean_dec_ref(v_b_4907_);
lean_dec_ref(v_a_4906_);
v_a_4981_ = lean_ctor_get(v___x_4942_, 0);
v_isSharedCheck_4988_ = !lean_is_exclusive(v___x_4942_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4983_ = v___x_4942_;
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_a_4981_);
lean_dec(v___x_4942_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4986_; 
if (v_isShared_4984_ == 0)
{
v___x_4986_ = v___x_4983_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v_a_4981_);
v___x_4986_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
return v___x_4986_;
}
}
}
}
else
{
lean_object* v___x_4989_; lean_object* v___x_4991_; 
lean_dec(v_a_4937_);
lean_dec(v_structId_4934_);
lean_dec(v_id_4933_);
lean_del_object(v___x_4929_);
lean_dec(v_fst_4927_);
lean_dec_ref(v_b_4907_);
lean_dec_ref(v_a_4906_);
v___x_4989_ = lean_box(0);
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 0, v___x_4989_);
v___x_4991_ = v___x_4939_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v___x_4989_);
v___x_4991_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
return v___x_4991_;
}
}
}
}
else
{
lean_object* v_a_4994_; lean_object* v___x_4996_; uint8_t v_isShared_4997_; uint8_t v_isSharedCheck_5001_; 
lean_dec(v_structId_4934_);
lean_dec(v_id_4933_);
lean_del_object(v___x_4929_);
lean_dec(v_fst_4927_);
lean_dec_ref(v_b_4907_);
lean_dec_ref(v_a_4906_);
v_a_4994_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_5001_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_5001_ == 0)
{
v___x_4996_ = v___x_4936_;
v_isShared_4997_ = v_isSharedCheck_5001_;
goto v_resetjp_4995_;
}
else
{
lean_inc(v_a_4994_);
lean_dec(v___x_4936_);
v___x_4996_ = lean_box(0);
v_isShared_4997_ = v_isSharedCheck_5001_;
goto v_resetjp_4995_;
}
v_resetjp_4995_:
{
lean_object* v___x_4999_; 
if (v_isShared_4997_ == 0)
{
v___x_4999_ = v___x_4996_;
goto v_reusejp_4998_;
}
else
{
lean_object* v_reuseFailAlloc_5000_; 
v_reuseFailAlloc_5000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5000_, 0, v_a_4994_);
v___x_4999_ = v_reuseFailAlloc_5000_;
goto v_reusejp_4998_;
}
v_reusejp_4998_:
{
return v___x_4999_;
}
}
}
}
else
{
lean_object* v_a_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5009_; 
lean_del_object(v___x_4929_);
lean_dec(v_fst_4927_);
lean_dec(v_fst_4924_);
lean_dec(v_a_4921_);
lean_dec_ref(v_b_4907_);
lean_dec_ref(v_a_4906_);
v_a_5002_ = lean_ctor_get(v___x_4931_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v___x_4931_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_5004_ = v___x_4931_;
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_a_5002_);
lean_dec(v___x_4931_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
lean_object* v___x_5007_; 
if (v_isShared_5005_ == 0)
{
v___x_5007_ = v___x_5004_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v_a_5002_);
v___x_5007_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
return v___x_5007_;
}
}
}
}
}
else
{
lean_object* v_a_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5019_; 
lean_dec(v_fst_4924_);
lean_dec(v_a_4921_);
lean_dec_ref(v_b_4907_);
lean_dec_ref(v_a_4906_);
v_a_5012_ = lean_ctor_get(v___x_4925_, 0);
v_isSharedCheck_5019_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_5019_ == 0)
{
v___x_5014_ = v___x_4925_;
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
else
{
lean_inc(v_a_5012_);
lean_dec(v___x_4925_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___x_5017_; 
if (v_isShared_5015_ == 0)
{
v___x_5017_ = v___x_5014_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v_a_5012_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
return v___x_5017_;
}
}
}
}
else
{
lean_object* v_a_5020_; lean_object* v___x_5022_; uint8_t v_isShared_5023_; uint8_t v_isSharedCheck_5027_; 
lean_dec(v_a_4921_);
lean_dec_ref(v_b_4907_);
lean_dec_ref(v_a_4906_);
v_a_5020_ = lean_ctor_get(v___x_4922_, 0);
v_isSharedCheck_5027_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_5022_ = v___x_4922_;
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
else
{
lean_inc(v_a_5020_);
lean_dec(v___x_4922_);
v___x_5022_ = lean_box(0);
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
v_resetjp_5021_:
{
lean_object* v___x_5025_; 
if (v_isShared_5023_ == 0)
{
v___x_5025_ = v___x_5022_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v_a_5020_);
v___x_5025_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
return v___x_5025_;
}
}
}
}
else
{
lean_object* v_a_5028_; lean_object* v___x_5030_; uint8_t v_isShared_5031_; uint8_t v_isSharedCheck_5035_; 
lean_dec_ref(v_b_4907_);
lean_dec_ref(v_a_4906_);
v_a_5028_ = lean_ctor_get(v___x_4920_, 0);
v_isSharedCheck_5035_ = !lean_is_exclusive(v___x_4920_);
if (v_isSharedCheck_5035_ == 0)
{
v___x_5030_ = v___x_4920_;
v_isShared_5031_ = v_isSharedCheck_5035_;
goto v_resetjp_5029_;
}
else
{
lean_inc(v_a_5028_);
lean_dec(v___x_4920_);
v___x_5030_ = lean_box(0);
v_isShared_5031_ = v_isSharedCheck_5035_;
goto v_resetjp_5029_;
}
v_resetjp_5029_:
{
lean_object* v___x_5033_; 
if (v_isShared_5031_ == 0)
{
v___x_5033_ = v___x_5030_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5034_; 
v_reuseFailAlloc_5034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5034_, 0, v_a_5028_);
v___x_5033_ = v_reuseFailAlloc_5034_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
return v___x_5033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27___boxed(lean_object* v_a_5036_, lean_object* v_b_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_){
_start:
{
lean_object* v_res_5050_; 
v_res_5050_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5036_, v_b_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_, v_a_5043_, v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_, v_a_5048_);
lean_dec(v_a_5048_);
lean_dec_ref(v_a_5047_);
lean_dec(v_a_5046_);
lean_dec_ref(v_a_5045_);
lean_dec(v_a_5044_);
lean_dec_ref(v_a_5043_);
lean_dec(v_a_5042_);
lean_dec_ref(v_a_5041_);
lean_dec(v_a_5040_);
lean_dec(v_a_5039_);
lean_dec(v_a_5038_);
return v_res_5050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(lean_object* v_a_5051_, lean_object* v_b_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_){
_start:
{
lean_object* v___x_5065_; 
v___x_5065_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
if (lean_obj_tag(v___x_5065_) == 0)
{
lean_object* v_a_5066_; lean_object* v___x_5067_; 
v_a_5066_ = lean_ctor_get(v___x_5065_, 0);
lean_inc(v_a_5066_);
lean_dec_ref(v___x_5065_);
lean_inc_ref(v_a_5051_);
v___x_5067_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5051_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
if (lean_obj_tag(v___x_5067_) == 0)
{
lean_object* v_a_5068_; lean_object* v_fst_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5165_; 
v_a_5068_ = lean_ctor_get(v___x_5067_, 0);
lean_inc(v_a_5068_);
lean_dec_ref(v___x_5067_);
v_fst_5069_ = lean_ctor_get(v_a_5068_, 0);
v_isSharedCheck_5165_ = !lean_is_exclusive(v_a_5068_);
if (v_isSharedCheck_5165_ == 0)
{
lean_object* v_unused_5166_; 
v_unused_5166_ = lean_ctor_get(v_a_5068_, 1);
lean_dec(v_unused_5166_);
v___x_5071_ = v_a_5068_;
v_isShared_5072_ = v_isSharedCheck_5165_;
goto v_resetjp_5070_;
}
else
{
lean_inc(v_fst_5069_);
lean_dec(v_a_5068_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5165_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5073_; 
lean_inc_ref(v_b_5052_);
v___x_5073_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
if (lean_obj_tag(v___x_5073_) == 0)
{
lean_object* v_a_5074_; lean_object* v_fst_5075_; lean_object* v___x_5077_; uint8_t v_isShared_5078_; uint8_t v_isSharedCheck_5155_; 
v_a_5074_ = lean_ctor_get(v___x_5073_, 0);
lean_inc(v_a_5074_);
lean_dec_ref(v___x_5073_);
v_fst_5075_ = lean_ctor_get(v_a_5074_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v_a_5074_);
if (v_isSharedCheck_5155_ == 0)
{
lean_object* v_unused_5156_; 
v_unused_5156_ = lean_ctor_get(v_a_5074_, 1);
lean_dec(v_unused_5156_);
v___x_5077_ = v_a_5074_;
v_isShared_5078_ = v_isSharedCheck_5155_;
goto v_resetjp_5076_;
}
else
{
lean_inc(v_fst_5075_);
lean_dec(v_a_5074_);
v___x_5077_ = lean_box(0);
v_isShared_5078_ = v_isSharedCheck_5155_;
goto v_resetjp_5076_;
}
v_resetjp_5076_:
{
lean_object* v___x_5079_; 
v___x_5079_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5051_, v_a_5054_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_object* v_a_5080_; lean_object* v_id_5081_; lean_object* v_structId_5082_; uint8_t v___x_5083_; lean_object* v___x_5084_; 
v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
lean_inc(v_a_5080_);
lean_dec_ref(v___x_5079_);
v_id_5081_ = lean_ctor_get(v_a_5066_, 0);
lean_inc(v_id_5081_);
v_structId_5082_ = lean_ctor_get(v_a_5066_, 1);
lean_inc(v_structId_5082_);
lean_dec(v_a_5066_);
v___x_5083_ = 0;
v___x_5084_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5069_, v___x_5083_, v_a_5080_, v_structId_5082_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
if (lean_obj_tag(v___x_5084_) == 0)
{
lean_object* v_a_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5138_; 
v_a_5085_ = lean_ctor_get(v___x_5084_, 0);
v_isSharedCheck_5138_ = !lean_is_exclusive(v___x_5084_);
if (v_isSharedCheck_5138_ == 0)
{
v___x_5087_ = v___x_5084_;
v_isShared_5088_ = v_isSharedCheck_5138_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_a_5085_);
lean_dec(v___x_5084_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5138_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
if (lean_obj_tag(v_a_5085_) == 1)
{
lean_object* v_val_5089_; lean_object* v___x_5090_; 
lean_del_object(v___x_5087_);
v_val_5089_ = lean_ctor_get(v_a_5085_, 0);
lean_inc(v_val_5089_);
lean_dec_ref(v_a_5085_);
v___x_5090_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5052_, v_a_5054_);
if (lean_obj_tag(v___x_5090_) == 0)
{
lean_object* v_a_5091_; lean_object* v___x_5092_; 
v_a_5091_ = lean_ctor_get(v___x_5090_, 0);
lean_inc(v_a_5091_);
lean_dec_ref(v___x_5090_);
v___x_5092_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5075_, v___x_5083_, v_a_5091_, v_structId_5082_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
if (lean_obj_tag(v___x_5092_) == 0)
{
lean_object* v_a_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5117_; 
v_a_5093_ = lean_ctor_get(v___x_5092_, 0);
v_isSharedCheck_5117_ = !lean_is_exclusive(v___x_5092_);
if (v_isSharedCheck_5117_ == 0)
{
v___x_5095_ = v___x_5092_;
v_isShared_5096_ = v_isSharedCheck_5117_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_a_5093_);
lean_dec(v___x_5092_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5117_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
if (lean_obj_tag(v_a_5093_) == 1)
{
lean_object* v_val_5097_; lean_object* v___x_5099_; 
v_val_5097_ = lean_ctor_get(v_a_5093_, 0);
lean_inc(v_val_5097_);
lean_dec_ref(v_a_5093_);
lean_inc(v_val_5097_);
lean_inc(v_val_5089_);
if (v_isShared_5078_ == 0)
{
lean_ctor_set_tag(v___x_5077_, 3);
lean_ctor_set(v___x_5077_, 1, v_val_5097_);
lean_ctor_set(v___x_5077_, 0, v_val_5089_);
v___x_5099_ = v___x_5077_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v_val_5089_);
lean_ctor_set(v_reuseFailAlloc_5112_, 1, v_val_5097_);
v___x_5099_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
lean_object* v___x_5100_; lean_object* v___x_5101_; uint8_t v___x_5102_; 
v___x_5100_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5099_);
v___x_5101_ = lean_box(0);
v___x_5102_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_5100_, v___x_5101_);
if (v___x_5102_ == 0)
{
lean_object* v___x_5103_; lean_object* v___x_5105_; 
lean_del_object(v___x_5095_);
v___x_5103_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5103_, 0, v_a_5051_);
lean_ctor_set(v___x_5103_, 1, v_b_5052_);
lean_ctor_set(v___x_5103_, 2, v_id_5081_);
lean_ctor_set(v___x_5103_, 3, v_val_5089_);
lean_ctor_set(v___x_5103_, 4, v_val_5097_);
if (v_isShared_5072_ == 0)
{
lean_ctor_set(v___x_5071_, 1, v___x_5103_);
lean_ctor_set(v___x_5071_, 0, v___x_5100_);
v___x_5105_ = v___x_5071_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5107_; 
v_reuseFailAlloc_5107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5107_, 0, v___x_5100_);
lean_ctor_set(v_reuseFailAlloc_5107_, 1, v___x_5103_);
v___x_5105_ = v_reuseFailAlloc_5107_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
lean_object* v___x_5106_; 
v___x_5106_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_5105_, v_structId_5082_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
lean_dec(v_structId_5082_);
return v___x_5106_;
}
}
else
{
lean_object* v___x_5108_; lean_object* v___x_5110_; 
lean_dec(v___x_5100_);
lean_dec(v_val_5097_);
lean_dec(v_val_5089_);
lean_dec(v_structId_5082_);
lean_dec(v_id_5081_);
lean_del_object(v___x_5071_);
lean_dec_ref(v_b_5052_);
lean_dec_ref(v_a_5051_);
v___x_5108_ = lean_box(0);
if (v_isShared_5096_ == 0)
{
lean_ctor_set(v___x_5095_, 0, v___x_5108_);
v___x_5110_ = v___x_5095_;
goto v_reusejp_5109_;
}
else
{
lean_object* v_reuseFailAlloc_5111_; 
v_reuseFailAlloc_5111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5111_, 0, v___x_5108_);
v___x_5110_ = v_reuseFailAlloc_5111_;
goto v_reusejp_5109_;
}
v_reusejp_5109_:
{
return v___x_5110_;
}
}
}
}
else
{
lean_object* v___x_5113_; lean_object* v___x_5115_; 
lean_dec(v_a_5093_);
lean_dec(v_val_5089_);
lean_dec(v_structId_5082_);
lean_dec(v_id_5081_);
lean_del_object(v___x_5077_);
lean_del_object(v___x_5071_);
lean_dec_ref(v_b_5052_);
lean_dec_ref(v_a_5051_);
v___x_5113_ = lean_box(0);
if (v_isShared_5096_ == 0)
{
lean_ctor_set(v___x_5095_, 0, v___x_5113_);
v___x_5115_ = v___x_5095_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v___x_5113_);
v___x_5115_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
return v___x_5115_;
}
}
}
}
else
{
lean_object* v_a_5118_; lean_object* v___x_5120_; uint8_t v_isShared_5121_; uint8_t v_isSharedCheck_5125_; 
lean_dec(v_val_5089_);
lean_dec(v_structId_5082_);
lean_dec(v_id_5081_);
lean_del_object(v___x_5077_);
lean_del_object(v___x_5071_);
lean_dec_ref(v_b_5052_);
lean_dec_ref(v_a_5051_);
v_a_5118_ = lean_ctor_get(v___x_5092_, 0);
v_isSharedCheck_5125_ = !lean_is_exclusive(v___x_5092_);
if (v_isSharedCheck_5125_ == 0)
{
v___x_5120_ = v___x_5092_;
v_isShared_5121_ = v_isSharedCheck_5125_;
goto v_resetjp_5119_;
}
else
{
lean_inc(v_a_5118_);
lean_dec(v___x_5092_);
v___x_5120_ = lean_box(0);
v_isShared_5121_ = v_isSharedCheck_5125_;
goto v_resetjp_5119_;
}
v_resetjp_5119_:
{
lean_object* v___x_5123_; 
if (v_isShared_5121_ == 0)
{
v___x_5123_ = v___x_5120_;
goto v_reusejp_5122_;
}
else
{
lean_object* v_reuseFailAlloc_5124_; 
v_reuseFailAlloc_5124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_a_5118_);
v___x_5123_ = v_reuseFailAlloc_5124_;
goto v_reusejp_5122_;
}
v_reusejp_5122_:
{
return v___x_5123_;
}
}
}
}
else
{
lean_object* v_a_5126_; lean_object* v___x_5128_; uint8_t v_isShared_5129_; uint8_t v_isSharedCheck_5133_; 
lean_dec(v_val_5089_);
lean_dec(v_structId_5082_);
lean_dec(v_id_5081_);
lean_del_object(v___x_5077_);
lean_dec(v_fst_5075_);
lean_del_object(v___x_5071_);
lean_dec_ref(v_b_5052_);
lean_dec_ref(v_a_5051_);
v_a_5126_ = lean_ctor_get(v___x_5090_, 0);
v_isSharedCheck_5133_ = !lean_is_exclusive(v___x_5090_);
if (v_isSharedCheck_5133_ == 0)
{
v___x_5128_ = v___x_5090_;
v_isShared_5129_ = v_isSharedCheck_5133_;
goto v_resetjp_5127_;
}
else
{
lean_inc(v_a_5126_);
lean_dec(v___x_5090_);
v___x_5128_ = lean_box(0);
v_isShared_5129_ = v_isSharedCheck_5133_;
goto v_resetjp_5127_;
}
v_resetjp_5127_:
{
lean_object* v___x_5131_; 
if (v_isShared_5129_ == 0)
{
v___x_5131_ = v___x_5128_;
goto v_reusejp_5130_;
}
else
{
lean_object* v_reuseFailAlloc_5132_; 
v_reuseFailAlloc_5132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_a_5126_);
v___x_5131_ = v_reuseFailAlloc_5132_;
goto v_reusejp_5130_;
}
v_reusejp_5130_:
{
return v___x_5131_;
}
}
}
}
else
{
lean_object* v___x_5134_; lean_object* v___x_5136_; 
lean_dec(v_a_5085_);
lean_dec(v_structId_5082_);
lean_dec(v_id_5081_);
lean_del_object(v___x_5077_);
lean_dec(v_fst_5075_);
lean_del_object(v___x_5071_);
lean_dec_ref(v_b_5052_);
lean_dec_ref(v_a_5051_);
v___x_5134_ = lean_box(0);
if (v_isShared_5088_ == 0)
{
lean_ctor_set(v___x_5087_, 0, v___x_5134_);
v___x_5136_ = v___x_5087_;
goto v_reusejp_5135_;
}
else
{
lean_object* v_reuseFailAlloc_5137_; 
v_reuseFailAlloc_5137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5137_, 0, v___x_5134_);
v___x_5136_ = v_reuseFailAlloc_5137_;
goto v_reusejp_5135_;
}
v_reusejp_5135_:
{
return v___x_5136_;
}
}
}
}
else
{
lean_object* v_a_5139_; lean_object* v___x_5141_; uint8_t v_isShared_5142_; uint8_t v_isSharedCheck_5146_; 
lean_dec(v_structId_5082_);
lean_dec(v_id_5081_);
lean_del_object(v___x_5077_);
lean_dec(v_fst_5075_);
lean_del_object(v___x_5071_);
lean_dec_ref(v_b_5052_);
lean_dec_ref(v_a_5051_);
v_a_5139_ = lean_ctor_get(v___x_5084_, 0);
v_isSharedCheck_5146_ = !lean_is_exclusive(v___x_5084_);
if (v_isSharedCheck_5146_ == 0)
{
v___x_5141_ = v___x_5084_;
v_isShared_5142_ = v_isSharedCheck_5146_;
goto v_resetjp_5140_;
}
else
{
lean_inc(v_a_5139_);
lean_dec(v___x_5084_);
v___x_5141_ = lean_box(0);
v_isShared_5142_ = v_isSharedCheck_5146_;
goto v_resetjp_5140_;
}
v_resetjp_5140_:
{
lean_object* v___x_5144_; 
if (v_isShared_5142_ == 0)
{
v___x_5144_ = v___x_5141_;
goto v_reusejp_5143_;
}
else
{
lean_object* v_reuseFailAlloc_5145_; 
v_reuseFailAlloc_5145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5145_, 0, v_a_5139_);
v___x_5144_ = v_reuseFailAlloc_5145_;
goto v_reusejp_5143_;
}
v_reusejp_5143_:
{
return v___x_5144_;
}
}
}
}
else
{
lean_object* v_a_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5154_; 
lean_del_object(v___x_5077_);
lean_dec(v_fst_5075_);
lean_del_object(v___x_5071_);
lean_dec(v_fst_5069_);
lean_dec(v_a_5066_);
lean_dec_ref(v_b_5052_);
lean_dec_ref(v_a_5051_);
v_a_5147_ = lean_ctor_get(v___x_5079_, 0);
v_isSharedCheck_5154_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5154_ == 0)
{
v___x_5149_ = v___x_5079_;
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_a_5147_);
lean_dec(v___x_5079_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___x_5152_; 
if (v_isShared_5150_ == 0)
{
v___x_5152_ = v___x_5149_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_a_5147_);
v___x_5152_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
return v___x_5152_;
}
}
}
}
}
else
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5164_; 
lean_del_object(v___x_5071_);
lean_dec(v_fst_5069_);
lean_dec(v_a_5066_);
lean_dec_ref(v_b_5052_);
lean_dec_ref(v_a_5051_);
v_a_5157_ = lean_ctor_get(v___x_5073_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5073_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5159_ = v___x_5073_;
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___x_5073_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v___x_5162_; 
if (v_isShared_5160_ == 0)
{
v___x_5162_ = v___x_5159_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5157_);
v___x_5162_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
return v___x_5162_;
}
}
}
}
}
else
{
lean_object* v_a_5167_; lean_object* v___x_5169_; uint8_t v_isShared_5170_; uint8_t v_isSharedCheck_5174_; 
lean_dec(v_a_5066_);
lean_dec_ref(v_b_5052_);
lean_dec_ref(v_a_5051_);
v_a_5167_ = lean_ctor_get(v___x_5067_, 0);
v_isSharedCheck_5174_ = !lean_is_exclusive(v___x_5067_);
if (v_isSharedCheck_5174_ == 0)
{
v___x_5169_ = v___x_5067_;
v_isShared_5170_ = v_isSharedCheck_5174_;
goto v_resetjp_5168_;
}
else
{
lean_inc(v_a_5167_);
lean_dec(v___x_5067_);
v___x_5169_ = lean_box(0);
v_isShared_5170_ = v_isSharedCheck_5174_;
goto v_resetjp_5168_;
}
v_resetjp_5168_:
{
lean_object* v___x_5172_; 
if (v_isShared_5170_ == 0)
{
v___x_5172_ = v___x_5169_;
goto v_reusejp_5171_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v_a_5167_);
v___x_5172_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5171_;
}
v_reusejp_5171_:
{
return v___x_5172_;
}
}
}
}
else
{
lean_object* v_a_5175_; lean_object* v___x_5177_; uint8_t v_isShared_5178_; uint8_t v_isSharedCheck_5182_; 
lean_dec_ref(v_b_5052_);
lean_dec_ref(v_a_5051_);
v_a_5175_ = lean_ctor_get(v___x_5065_, 0);
v_isSharedCheck_5182_ = !lean_is_exclusive(v___x_5065_);
if (v_isSharedCheck_5182_ == 0)
{
v___x_5177_ = v___x_5065_;
v_isShared_5178_ = v_isSharedCheck_5182_;
goto v_resetjp_5176_;
}
else
{
lean_inc(v_a_5175_);
lean_dec(v___x_5065_);
v___x_5177_ = lean_box(0);
v_isShared_5178_ = v_isSharedCheck_5182_;
goto v_resetjp_5176_;
}
v_resetjp_5176_:
{
lean_object* v___x_5180_; 
if (v_isShared_5178_ == 0)
{
v___x_5180_ = v___x_5177_;
goto v_reusejp_5179_;
}
else
{
lean_object* v_reuseFailAlloc_5181_; 
v_reuseFailAlloc_5181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5181_, 0, v_a_5175_);
v___x_5180_ = v_reuseFailAlloc_5181_;
goto v_reusejp_5179_;
}
v_reusejp_5179_:
{
return v___x_5180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq___boxed(lean_object* v_a_5183_, lean_object* v_b_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_){
_start:
{
lean_object* v_res_5197_; 
v_res_5197_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5183_, v_b_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_);
lean_dec(v_a_5195_);
lean_dec_ref(v_a_5194_);
lean_dec(v_a_5193_);
lean_dec_ref(v_a_5192_);
lean_dec(v_a_5191_);
lean_dec_ref(v_a_5190_);
lean_dec(v_a_5189_);
lean_dec_ref(v_a_5188_);
lean_dec(v_a_5187_);
lean_dec(v_a_5186_);
lean_dec(v_a_5185_);
return v_res_5197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq(lean_object* v_a_5198_, lean_object* v_b_5199_, lean_object* v_a_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_){
_start:
{
uint8_t v___x_5211_; 
v___x_5211_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_5198_, v_b_5199_);
if (v___x_5211_ == 0)
{
lean_object* v___x_5212_; 
v___x_5212_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5198_, v_b_5199_, v_a_5200_, v_a_5208_);
if (lean_obj_tag(v___x_5212_) == 0)
{
lean_object* v_a_5213_; 
v_a_5213_ = lean_ctor_get(v___x_5212_, 0);
lean_inc(v_a_5213_);
lean_dec_ref(v___x_5212_);
if (lean_obj_tag(v_a_5213_) == 1)
{
lean_object* v_val_5214_; lean_object* v___x_5215_; 
v_val_5214_ = lean_ctor_get(v_a_5213_, 0);
lean_inc(v_val_5214_);
lean_dec_ref(v_a_5213_);
v___x_5215_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_val_5214_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_, v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_);
if (lean_obj_tag(v___x_5215_) == 0)
{
lean_object* v_a_5216_; uint8_t v___x_5217_; 
v_a_5216_ = lean_ctor_get(v___x_5215_, 0);
lean_inc(v_a_5216_);
lean_dec_ref(v___x_5215_);
v___x_5217_ = lean_unbox(v_a_5216_);
lean_dec(v_a_5216_);
if (v___x_5217_ == 0)
{
lean_object* v___x_5218_; 
v___x_5218_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5214_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_, v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_);
if (lean_obj_tag(v___x_5218_) == 0)
{
lean_object* v_a_5219_; uint8_t v___x_5220_; 
v_a_5219_ = lean_ctor_get(v___x_5218_, 0);
lean_inc(v_a_5219_);
lean_dec_ref(v___x_5218_);
v___x_5220_ = lean_unbox(v_a_5219_);
lean_dec(v_a_5219_);
if (v___x_5220_ == 0)
{
lean_object* v___x_5221_; 
v___x_5221_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_5198_, v_b_5199_, v_val_5214_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_, v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_);
lean_dec(v_val_5214_);
return v___x_5221_;
}
else
{
lean_object* v___x_5222_; 
lean_dec(v_val_5214_);
v___x_5222_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_5198_, v_b_5199_, v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_);
return v___x_5222_;
}
}
else
{
lean_object* v_a_5223_; lean_object* v___x_5225_; uint8_t v_isShared_5226_; uint8_t v_isSharedCheck_5230_; 
lean_dec(v_val_5214_);
lean_dec_ref(v_b_5199_);
lean_dec_ref(v_a_5198_);
v_a_5223_ = lean_ctor_get(v___x_5218_, 0);
v_isSharedCheck_5230_ = !lean_is_exclusive(v___x_5218_);
if (v_isSharedCheck_5230_ == 0)
{
v___x_5225_ = v___x_5218_;
v_isShared_5226_ = v_isSharedCheck_5230_;
goto v_resetjp_5224_;
}
else
{
lean_inc(v_a_5223_);
lean_dec(v___x_5218_);
v___x_5225_ = lean_box(0);
v_isShared_5226_ = v_isSharedCheck_5230_;
goto v_resetjp_5224_;
}
v_resetjp_5224_:
{
lean_object* v___x_5228_; 
if (v_isShared_5226_ == 0)
{
v___x_5228_ = v___x_5225_;
goto v_reusejp_5227_;
}
else
{
lean_object* v_reuseFailAlloc_5229_; 
v_reuseFailAlloc_5229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5229_, 0, v_a_5223_);
v___x_5228_ = v_reuseFailAlloc_5229_;
goto v_reusejp_5227_;
}
v_reusejp_5227_:
{
return v___x_5228_;
}
}
}
}
else
{
lean_object* v___x_5231_; 
v___x_5231_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5214_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_, v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_);
if (lean_obj_tag(v___x_5231_) == 0)
{
lean_object* v_a_5232_; uint8_t v___x_5233_; 
v_a_5232_ = lean_ctor_get(v___x_5231_, 0);
lean_inc(v_a_5232_);
lean_dec_ref(v___x_5231_);
v___x_5233_ = lean_unbox(v_a_5232_);
lean_dec(v_a_5232_);
if (v___x_5233_ == 0)
{
lean_object* v___x_5234_; 
v___x_5234_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_5198_, v_b_5199_, v_val_5214_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_, v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_);
lean_dec(v_val_5214_);
return v___x_5234_;
}
else
{
lean_object* v___x_5235_; 
v___x_5235_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_5198_, v_b_5199_, v_val_5214_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_, v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_);
lean_dec(v_val_5214_);
return v___x_5235_;
}
}
else
{
lean_object* v_a_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5243_; 
lean_dec(v_val_5214_);
lean_dec_ref(v_b_5199_);
lean_dec_ref(v_a_5198_);
v_a_5236_ = lean_ctor_get(v___x_5231_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___x_5231_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5238_ = v___x_5231_;
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_a_5236_);
lean_dec(v___x_5231_);
v___x_5238_ = lean_box(0);
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
v_resetjp_5237_:
{
lean_object* v___x_5241_; 
if (v_isShared_5239_ == 0)
{
v___x_5241_ = v___x_5238_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v_a_5236_);
v___x_5241_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
return v___x_5241_;
}
}
}
}
}
else
{
lean_object* v_a_5244_; lean_object* v___x_5246_; uint8_t v_isShared_5247_; uint8_t v_isSharedCheck_5251_; 
lean_dec(v_val_5214_);
lean_dec_ref(v_b_5199_);
lean_dec_ref(v_a_5198_);
v_a_5244_ = lean_ctor_get(v___x_5215_, 0);
v_isSharedCheck_5251_ = !lean_is_exclusive(v___x_5215_);
if (v_isSharedCheck_5251_ == 0)
{
v___x_5246_ = v___x_5215_;
v_isShared_5247_ = v_isSharedCheck_5251_;
goto v_resetjp_5245_;
}
else
{
lean_inc(v_a_5244_);
lean_dec(v___x_5215_);
v___x_5246_ = lean_box(0);
v_isShared_5247_ = v_isSharedCheck_5251_;
goto v_resetjp_5245_;
}
v_resetjp_5245_:
{
lean_object* v___x_5249_; 
if (v_isShared_5247_ == 0)
{
v___x_5249_ = v___x_5246_;
goto v_reusejp_5248_;
}
else
{
lean_object* v_reuseFailAlloc_5250_; 
v_reuseFailAlloc_5250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5250_, 0, v_a_5244_);
v___x_5249_ = v_reuseFailAlloc_5250_;
goto v_reusejp_5248_;
}
v_reusejp_5248_:
{
return v___x_5249_;
}
}
}
}
else
{
lean_object* v___x_5252_; 
lean_dec(v_a_5213_);
v___x_5252_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5198_, v_b_5199_, v_a_5200_, v_a_5208_);
if (lean_obj_tag(v___x_5252_) == 0)
{
lean_object* v_a_5253_; lean_object* v___x_5255_; uint8_t v_isShared_5256_; uint8_t v_isSharedCheck_5275_; 
v_a_5253_ = lean_ctor_get(v___x_5252_, 0);
v_isSharedCheck_5275_ = !lean_is_exclusive(v___x_5252_);
if (v_isSharedCheck_5275_ == 0)
{
v___x_5255_ = v___x_5252_;
v_isShared_5256_ = v_isSharedCheck_5275_;
goto v_resetjp_5254_;
}
else
{
lean_inc(v_a_5253_);
lean_dec(v___x_5252_);
v___x_5255_ = lean_box(0);
v_isShared_5256_ = v_isSharedCheck_5275_;
goto v_resetjp_5254_;
}
v_resetjp_5254_:
{
if (lean_obj_tag(v_a_5253_) == 1)
{
lean_object* v_val_5257_; lean_object* v___x_5258_; 
lean_del_object(v___x_5255_);
v_val_5257_ = lean_ctor_get(v_a_5253_, 0);
lean_inc(v_val_5257_);
lean_dec_ref(v_a_5253_);
v___x_5258_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_5257_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_, v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_);
if (lean_obj_tag(v___x_5258_) == 0)
{
lean_object* v_a_5259_; lean_object* v_orderedAddInst_x3f_5260_; 
v_a_5259_ = lean_ctor_get(v___x_5258_, 0);
lean_inc(v_a_5259_);
lean_dec_ref(v___x_5258_);
v_orderedAddInst_x3f_5260_ = lean_ctor_get(v_a_5259_, 9);
lean_inc(v_orderedAddInst_x3f_5260_);
lean_dec(v_a_5259_);
if (lean_obj_tag(v_orderedAddInst_x3f_5260_) == 0)
{
lean_object* v___x_5261_; 
v___x_5261_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5198_, v_b_5199_, v_val_5257_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_, v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_);
lean_dec(v_val_5257_);
return v___x_5261_;
}
else
{
lean_object* v___x_5262_; 
lean_dec_ref(v_orderedAddInst_x3f_5260_);
v___x_5262_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5198_, v_b_5199_, v_val_5257_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_, v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_);
lean_dec(v_val_5257_);
return v___x_5262_;
}
}
else
{
lean_object* v_a_5263_; lean_object* v___x_5265_; uint8_t v_isShared_5266_; uint8_t v_isSharedCheck_5270_; 
lean_dec(v_val_5257_);
lean_dec_ref(v_b_5199_);
lean_dec_ref(v_a_5198_);
v_a_5263_ = lean_ctor_get(v___x_5258_, 0);
v_isSharedCheck_5270_ = !lean_is_exclusive(v___x_5258_);
if (v_isSharedCheck_5270_ == 0)
{
v___x_5265_ = v___x_5258_;
v_isShared_5266_ = v_isSharedCheck_5270_;
goto v_resetjp_5264_;
}
else
{
lean_inc(v_a_5263_);
lean_dec(v___x_5258_);
v___x_5265_ = lean_box(0);
v_isShared_5266_ = v_isSharedCheck_5270_;
goto v_resetjp_5264_;
}
v_resetjp_5264_:
{
lean_object* v___x_5268_; 
if (v_isShared_5266_ == 0)
{
v___x_5268_ = v___x_5265_;
goto v_reusejp_5267_;
}
else
{
lean_object* v_reuseFailAlloc_5269_; 
v_reuseFailAlloc_5269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5269_, 0, v_a_5263_);
v___x_5268_ = v_reuseFailAlloc_5269_;
goto v_reusejp_5267_;
}
v_reusejp_5267_:
{
return v___x_5268_;
}
}
}
}
else
{
lean_object* v___x_5271_; lean_object* v___x_5273_; 
lean_dec(v_a_5253_);
lean_dec_ref(v_b_5199_);
lean_dec_ref(v_a_5198_);
v___x_5271_ = lean_box(0);
if (v_isShared_5256_ == 0)
{
lean_ctor_set(v___x_5255_, 0, v___x_5271_);
v___x_5273_ = v___x_5255_;
goto v_reusejp_5272_;
}
else
{
lean_object* v_reuseFailAlloc_5274_; 
v_reuseFailAlloc_5274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5274_, 0, v___x_5271_);
v___x_5273_ = v_reuseFailAlloc_5274_;
goto v_reusejp_5272_;
}
v_reusejp_5272_:
{
return v___x_5273_;
}
}
}
}
else
{
lean_object* v_a_5276_; lean_object* v___x_5278_; uint8_t v_isShared_5279_; uint8_t v_isSharedCheck_5283_; 
lean_dec_ref(v_b_5199_);
lean_dec_ref(v_a_5198_);
v_a_5276_ = lean_ctor_get(v___x_5252_, 0);
v_isSharedCheck_5283_ = !lean_is_exclusive(v___x_5252_);
if (v_isSharedCheck_5283_ == 0)
{
v___x_5278_ = v___x_5252_;
v_isShared_5279_ = v_isSharedCheck_5283_;
goto v_resetjp_5277_;
}
else
{
lean_inc(v_a_5276_);
lean_dec(v___x_5252_);
v___x_5278_ = lean_box(0);
v_isShared_5279_ = v_isSharedCheck_5283_;
goto v_resetjp_5277_;
}
v_resetjp_5277_:
{
lean_object* v___x_5281_; 
if (v_isShared_5279_ == 0)
{
v___x_5281_ = v___x_5278_;
goto v_reusejp_5280_;
}
else
{
lean_object* v_reuseFailAlloc_5282_; 
v_reuseFailAlloc_5282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5282_, 0, v_a_5276_);
v___x_5281_ = v_reuseFailAlloc_5282_;
goto v_reusejp_5280_;
}
v_reusejp_5280_:
{
return v___x_5281_;
}
}
}
}
}
else
{
lean_object* v_a_5284_; lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5291_; 
lean_dec_ref(v_b_5199_);
lean_dec_ref(v_a_5198_);
v_a_5284_ = lean_ctor_get(v___x_5212_, 0);
v_isSharedCheck_5291_ = !lean_is_exclusive(v___x_5212_);
if (v_isSharedCheck_5291_ == 0)
{
v___x_5286_ = v___x_5212_;
v_isShared_5287_ = v_isSharedCheck_5291_;
goto v_resetjp_5285_;
}
else
{
lean_inc(v_a_5284_);
lean_dec(v___x_5212_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5291_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
lean_object* v___x_5289_; 
if (v_isShared_5287_ == 0)
{
v___x_5289_ = v___x_5286_;
goto v_reusejp_5288_;
}
else
{
lean_object* v_reuseFailAlloc_5290_; 
v_reuseFailAlloc_5290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5290_, 0, v_a_5284_);
v___x_5289_ = v_reuseFailAlloc_5290_;
goto v_reusejp_5288_;
}
v_reusejp_5288_:
{
return v___x_5289_;
}
}
}
}
else
{
lean_object* v___x_5292_; lean_object* v___x_5293_; 
lean_dec_ref(v_b_5199_);
lean_dec_ref(v_a_5198_);
v___x_5292_ = lean_box(0);
v___x_5293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5293_, 0, v___x_5292_);
return v___x_5293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed(lean_object* v_a_5294_, lean_object* v_b_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_, lean_object* v_a_5298_, lean_object* v_a_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_, lean_object* v_a_5305_, lean_object* v_a_5306_){
_start:
{
lean_object* v_res_5307_; 
v_res_5307_ = l_Lean_Meta_Grind_Arith_Linear_processNewEq(v_a_5294_, v_b_5295_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_);
lean_dec(v_a_5305_);
lean_dec_ref(v_a_5304_);
lean_dec(v_a_5303_);
lean_dec_ref(v_a_5302_);
lean_dec(v_a_5301_);
lean_dec_ref(v_a_5300_);
lean_dec(v_a_5299_);
lean_dec_ref(v_a_5298_);
lean_dec(v_a_5297_);
lean_dec(v_a_5296_);
return v_res_5307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object* v_a_5308_, lean_object* v_b_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_){
_start:
{
uint8_t v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; 
v___x_5322_ = 0;
v___x_5323_ = lean_unsigned_to_nat(0u);
v___x_5324_ = lean_box(v___x_5322_);
lean_inc_ref(v_a_5308_);
v___x_5325_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5325_, 0, v_a_5308_);
lean_closure_set(v___x_5325_, 1, v___x_5324_);
lean_closure_set(v___x_5325_, 2, v___x_5323_);
v___x_5326_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5325_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_);
if (lean_obj_tag(v___x_5326_) == 0)
{
lean_object* v_a_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5428_; 
v_a_5327_ = lean_ctor_get(v___x_5326_, 0);
v_isSharedCheck_5428_ = !lean_is_exclusive(v___x_5326_);
if (v_isSharedCheck_5428_ == 0)
{
v___x_5329_ = v___x_5326_;
v_isShared_5330_ = v_isSharedCheck_5428_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_a_5327_);
lean_dec(v___x_5326_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5428_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
if (lean_obj_tag(v_a_5327_) == 1)
{
lean_object* v_val_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; 
lean_del_object(v___x_5329_);
v_val_5331_ = lean_ctor_get(v_a_5327_, 0);
lean_inc(v_val_5331_);
lean_dec_ref(v_a_5327_);
v___x_5332_ = lean_box(v___x_5322_);
lean_inc_ref(v_b_5309_);
v___x_5333_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5333_, 0, v_b_5309_);
lean_closure_set(v___x_5333_, 1, v___x_5332_);
lean_closure_set(v___x_5333_, 2, v___x_5323_);
v___x_5334_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5333_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_);
if (lean_obj_tag(v___x_5334_) == 0)
{
lean_object* v_a_5335_; lean_object* v___x_5337_; uint8_t v_isShared_5338_; uint8_t v_isSharedCheck_5415_; 
v_a_5335_ = lean_ctor_get(v___x_5334_, 0);
v_isSharedCheck_5415_ = !lean_is_exclusive(v___x_5334_);
if (v_isSharedCheck_5415_ == 0)
{
v___x_5337_ = v___x_5334_;
v_isShared_5338_ = v_isSharedCheck_5415_;
goto v_resetjp_5336_;
}
else
{
lean_inc(v_a_5335_);
lean_dec(v___x_5334_);
v___x_5337_ = lean_box(0);
v_isShared_5338_ = v_isSharedCheck_5415_;
goto v_resetjp_5336_;
}
v_resetjp_5336_:
{
if (lean_obj_tag(v_a_5335_) == 1)
{
lean_object* v_val_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; 
lean_del_object(v___x_5337_);
v_val_5339_ = lean_ctor_get(v_a_5335_, 0);
lean_inc(v_val_5339_);
lean_dec_ref(v_a_5335_);
lean_inc(v_val_5339_);
lean_inc(v_val_5331_);
v___x_5340_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_5340_, 0, v_val_5331_);
lean_ctor_set(v___x_5340_, 1, v_val_5339_);
v___x_5341_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_5340_);
lean_inc_ref(v_b_5309_);
lean_inc_ref(v_a_5308_);
v___x_5342_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5342_, 0, v_a_5308_);
lean_ctor_set(v___x_5342_, 1, v_b_5309_);
lean_ctor_set(v___x_5342_, 2, v_val_5331_);
lean_ctor_set(v___x_5342_, 3, v_val_5339_);
v___x_5343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5343_, 0, v___x_5341_);
lean_ctor_set(v___x_5343_, 1, v___x_5342_);
v___x_5344_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(v___x_5343_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_);
if (lean_obj_tag(v___x_5344_) == 0)
{
lean_object* v_a_5345_; lean_object* v___x_5346_; 
v_a_5345_ = lean_ctor_get(v___x_5344_, 0);
lean_inc(v_a_5345_);
lean_dec_ref(v___x_5344_);
v___x_5346_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5308_, v_a_5311_);
lean_dec_ref(v_a_5308_);
if (lean_obj_tag(v___x_5346_) == 0)
{
lean_object* v_a_5347_; lean_object* v___x_5348_; 
v_a_5347_ = lean_ctor_get(v___x_5346_, 0);
lean_inc(v_a_5347_);
lean_dec_ref(v___x_5346_);
v___x_5348_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5309_, v_a_5311_);
lean_dec_ref(v_b_5309_);
if (lean_obj_tag(v___x_5348_) == 0)
{
lean_object* v_a_5349_; lean_object* v_p_5350_; lean_object* v___y_5352_; uint8_t v___x_5386_; 
v_a_5349_ = lean_ctor_get(v___x_5348_, 0);
lean_inc(v_a_5349_);
lean_dec_ref(v___x_5348_);
v_p_5350_ = lean_ctor_get(v_a_5345_, 0);
v___x_5386_ = lean_nat_dec_le(v_a_5347_, v_a_5349_);
if (v___x_5386_ == 0)
{
lean_dec(v_a_5349_);
v___y_5352_ = v_a_5347_;
goto v___jp_5351_;
}
else
{
lean_dec(v_a_5347_);
v___y_5352_ = v_a_5349_;
goto v___jp_5351_;
}
v___jp_5351_:
{
lean_object* v___x_5353_; 
lean_inc(v___y_5352_);
lean_inc_ref(v_p_5350_);
v___x_5353_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_5350_, v___y_5352_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_);
if (lean_obj_tag(v___x_5353_) == 0)
{
lean_object* v_a_5354_; lean_object* v___x_5355_; 
v_a_5354_ = lean_ctor_get(v___x_5353_, 0);
lean_inc(v_a_5354_);
lean_dec_ref(v___x_5353_);
v___x_5355_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5354_, v___x_5322_, v___y_5352_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_);
if (lean_obj_tag(v___x_5355_) == 0)
{
lean_object* v_a_5356_; lean_object* v___x_5358_; uint8_t v_isShared_5359_; uint8_t v_isSharedCheck_5369_; 
v_a_5356_ = lean_ctor_get(v___x_5355_, 0);
v_isSharedCheck_5369_ = !lean_is_exclusive(v___x_5355_);
if (v_isSharedCheck_5369_ == 0)
{
v___x_5358_ = v___x_5355_;
v_isShared_5359_ = v_isSharedCheck_5369_;
goto v_resetjp_5357_;
}
else
{
lean_inc(v_a_5356_);
lean_dec(v___x_5355_);
v___x_5358_ = lean_box(0);
v_isShared_5359_ = v_isSharedCheck_5369_;
goto v_resetjp_5357_;
}
v_resetjp_5357_:
{
if (lean_obj_tag(v_a_5356_) == 1)
{
lean_object* v_val_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; 
lean_del_object(v___x_5358_);
v_val_5360_ = lean_ctor_get(v_a_5356_, 0);
lean_inc(v_val_5360_);
lean_dec_ref(v_a_5356_);
lean_inc(v_val_5360_);
v___x_5361_ = l_Lean_Grind_Linarith_Expr_norm(v_val_5360_);
v___x_5362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5362_, 0, v_a_5345_);
lean_ctor_set(v___x_5362_, 1, v_val_5360_);
v___x_5363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5363_, 0, v___x_5361_);
lean_ctor_set(v___x_5363_, 1, v___x_5362_);
v___x_5364_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5363_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_);
return v___x_5364_;
}
else
{
lean_object* v___x_5365_; lean_object* v___x_5367_; 
lean_dec(v_a_5356_);
lean_dec(v_a_5345_);
v___x_5365_ = lean_box(0);
if (v_isShared_5359_ == 0)
{
lean_ctor_set(v___x_5358_, 0, v___x_5365_);
v___x_5367_ = v___x_5358_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v___x_5365_);
v___x_5367_ = v_reuseFailAlloc_5368_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
return v___x_5367_;
}
}
}
}
else
{
lean_object* v_a_5370_; lean_object* v___x_5372_; uint8_t v_isShared_5373_; uint8_t v_isSharedCheck_5377_; 
lean_dec(v_a_5345_);
v_a_5370_ = lean_ctor_get(v___x_5355_, 0);
v_isSharedCheck_5377_ = !lean_is_exclusive(v___x_5355_);
if (v_isSharedCheck_5377_ == 0)
{
v___x_5372_ = v___x_5355_;
v_isShared_5373_ = v_isSharedCheck_5377_;
goto v_resetjp_5371_;
}
else
{
lean_inc(v_a_5370_);
lean_dec(v___x_5355_);
v___x_5372_ = lean_box(0);
v_isShared_5373_ = v_isSharedCheck_5377_;
goto v_resetjp_5371_;
}
v_resetjp_5371_:
{
lean_object* v___x_5375_; 
if (v_isShared_5373_ == 0)
{
v___x_5375_ = v___x_5372_;
goto v_reusejp_5374_;
}
else
{
lean_object* v_reuseFailAlloc_5376_; 
v_reuseFailAlloc_5376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5376_, 0, v_a_5370_);
v___x_5375_ = v_reuseFailAlloc_5376_;
goto v_reusejp_5374_;
}
v_reusejp_5374_:
{
return v___x_5375_;
}
}
}
}
else
{
lean_object* v_a_5378_; lean_object* v___x_5380_; uint8_t v_isShared_5381_; uint8_t v_isSharedCheck_5385_; 
lean_dec(v___y_5352_);
lean_dec(v_a_5345_);
v_a_5378_ = lean_ctor_get(v___x_5353_, 0);
v_isSharedCheck_5385_ = !lean_is_exclusive(v___x_5353_);
if (v_isSharedCheck_5385_ == 0)
{
v___x_5380_ = v___x_5353_;
v_isShared_5381_ = v_isSharedCheck_5385_;
goto v_resetjp_5379_;
}
else
{
lean_inc(v_a_5378_);
lean_dec(v___x_5353_);
v___x_5380_ = lean_box(0);
v_isShared_5381_ = v_isSharedCheck_5385_;
goto v_resetjp_5379_;
}
v_resetjp_5379_:
{
lean_object* v___x_5383_; 
if (v_isShared_5381_ == 0)
{
v___x_5383_ = v___x_5380_;
goto v_reusejp_5382_;
}
else
{
lean_object* v_reuseFailAlloc_5384_; 
v_reuseFailAlloc_5384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5384_, 0, v_a_5378_);
v___x_5383_ = v_reuseFailAlloc_5384_;
goto v_reusejp_5382_;
}
v_reusejp_5382_:
{
return v___x_5383_;
}
}
}
}
}
else
{
lean_object* v_a_5387_; lean_object* v___x_5389_; uint8_t v_isShared_5390_; uint8_t v_isSharedCheck_5394_; 
lean_dec(v_a_5347_);
lean_dec(v_a_5345_);
v_a_5387_ = lean_ctor_get(v___x_5348_, 0);
v_isSharedCheck_5394_ = !lean_is_exclusive(v___x_5348_);
if (v_isSharedCheck_5394_ == 0)
{
v___x_5389_ = v___x_5348_;
v_isShared_5390_ = v_isSharedCheck_5394_;
goto v_resetjp_5388_;
}
else
{
lean_inc(v_a_5387_);
lean_dec(v___x_5348_);
v___x_5389_ = lean_box(0);
v_isShared_5390_ = v_isSharedCheck_5394_;
goto v_resetjp_5388_;
}
v_resetjp_5388_:
{
lean_object* v___x_5392_; 
if (v_isShared_5390_ == 0)
{
v___x_5392_ = v___x_5389_;
goto v_reusejp_5391_;
}
else
{
lean_object* v_reuseFailAlloc_5393_; 
v_reuseFailAlloc_5393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5393_, 0, v_a_5387_);
v___x_5392_ = v_reuseFailAlloc_5393_;
goto v_reusejp_5391_;
}
v_reusejp_5391_:
{
return v___x_5392_;
}
}
}
}
else
{
lean_object* v_a_5395_; lean_object* v___x_5397_; uint8_t v_isShared_5398_; uint8_t v_isSharedCheck_5402_; 
lean_dec(v_a_5345_);
lean_dec_ref(v_b_5309_);
v_a_5395_ = lean_ctor_get(v___x_5346_, 0);
v_isSharedCheck_5402_ = !lean_is_exclusive(v___x_5346_);
if (v_isSharedCheck_5402_ == 0)
{
v___x_5397_ = v___x_5346_;
v_isShared_5398_ = v_isSharedCheck_5402_;
goto v_resetjp_5396_;
}
else
{
lean_inc(v_a_5395_);
lean_dec(v___x_5346_);
v___x_5397_ = lean_box(0);
v_isShared_5398_ = v_isSharedCheck_5402_;
goto v_resetjp_5396_;
}
v_resetjp_5396_:
{
lean_object* v___x_5400_; 
if (v_isShared_5398_ == 0)
{
v___x_5400_ = v___x_5397_;
goto v_reusejp_5399_;
}
else
{
lean_object* v_reuseFailAlloc_5401_; 
v_reuseFailAlloc_5401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5401_, 0, v_a_5395_);
v___x_5400_ = v_reuseFailAlloc_5401_;
goto v_reusejp_5399_;
}
v_reusejp_5399_:
{
return v___x_5400_;
}
}
}
}
else
{
lean_object* v_a_5403_; lean_object* v___x_5405_; uint8_t v_isShared_5406_; uint8_t v_isSharedCheck_5410_; 
lean_dec_ref(v_b_5309_);
lean_dec_ref(v_a_5308_);
v_a_5403_ = lean_ctor_get(v___x_5344_, 0);
v_isSharedCheck_5410_ = !lean_is_exclusive(v___x_5344_);
if (v_isSharedCheck_5410_ == 0)
{
v___x_5405_ = v___x_5344_;
v_isShared_5406_ = v_isSharedCheck_5410_;
goto v_resetjp_5404_;
}
else
{
lean_inc(v_a_5403_);
lean_dec(v___x_5344_);
v___x_5405_ = lean_box(0);
v_isShared_5406_ = v_isSharedCheck_5410_;
goto v_resetjp_5404_;
}
v_resetjp_5404_:
{
lean_object* v___x_5408_; 
if (v_isShared_5406_ == 0)
{
v___x_5408_ = v___x_5405_;
goto v_reusejp_5407_;
}
else
{
lean_object* v_reuseFailAlloc_5409_; 
v_reuseFailAlloc_5409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5409_, 0, v_a_5403_);
v___x_5408_ = v_reuseFailAlloc_5409_;
goto v_reusejp_5407_;
}
v_reusejp_5407_:
{
return v___x_5408_;
}
}
}
}
else
{
lean_object* v___x_5411_; lean_object* v___x_5413_; 
lean_dec(v_a_5335_);
lean_dec(v_val_5331_);
lean_dec_ref(v_b_5309_);
lean_dec_ref(v_a_5308_);
v___x_5411_ = lean_box(0);
if (v_isShared_5338_ == 0)
{
lean_ctor_set(v___x_5337_, 0, v___x_5411_);
v___x_5413_ = v___x_5337_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v___x_5411_);
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
lean_dec(v_val_5331_);
lean_dec_ref(v_b_5309_);
lean_dec_ref(v_a_5308_);
v_a_5416_ = lean_ctor_get(v___x_5334_, 0);
v_isSharedCheck_5423_ = !lean_is_exclusive(v___x_5334_);
if (v_isSharedCheck_5423_ == 0)
{
v___x_5418_ = v___x_5334_;
v_isShared_5419_ = v_isSharedCheck_5423_;
goto v_resetjp_5417_;
}
else
{
lean_inc(v_a_5416_);
lean_dec(v___x_5334_);
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
else
{
lean_object* v___x_5424_; lean_object* v___x_5426_; 
lean_dec(v_a_5327_);
lean_dec_ref(v_b_5309_);
lean_dec_ref(v_a_5308_);
v___x_5424_ = lean_box(0);
if (v_isShared_5330_ == 0)
{
lean_ctor_set(v___x_5329_, 0, v___x_5424_);
v___x_5426_ = v___x_5329_;
goto v_reusejp_5425_;
}
else
{
lean_object* v_reuseFailAlloc_5427_; 
v_reuseFailAlloc_5427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5427_, 0, v___x_5424_);
v___x_5426_ = v_reuseFailAlloc_5427_;
goto v_reusejp_5425_;
}
v_reusejp_5425_:
{
return v___x_5426_;
}
}
}
}
else
{
lean_object* v_a_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5436_; 
lean_dec_ref(v_b_5309_);
lean_dec_ref(v_a_5308_);
v_a_5429_ = lean_ctor_get(v___x_5326_, 0);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5326_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5431_ = v___x_5326_;
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_a_5429_);
lean_dec(v___x_5326_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
lean_object* v___x_5434_; 
if (v_isShared_5432_ == 0)
{
v___x_5434_ = v___x_5431_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_a_5429_);
v___x_5434_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
return v___x_5434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq___boxed(lean_object* v_a_5437_, lean_object* v_b_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_, lean_object* v_a_5450_){
_start:
{
lean_object* v_res_5451_; 
v_res_5451_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5437_, v_b_5438_, v_a_5439_, v_a_5440_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_);
lean_dec(v_a_5449_);
lean_dec_ref(v_a_5448_);
lean_dec(v_a_5447_);
lean_dec_ref(v_a_5446_);
lean_dec(v_a_5445_);
lean_dec_ref(v_a_5444_);
lean_dec(v_a_5443_);
lean_dec_ref(v_a_5442_);
lean_dec(v_a_5441_);
lean_dec(v_a_5440_);
lean_dec(v_a_5439_);
return v_res_5451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(lean_object* v_a_5452_, lean_object* v_b_5453_, lean_object* v_a_5454_, lean_object* v_a_5455_, lean_object* v_a_5456_, lean_object* v_a_5457_, lean_object* v_a_5458_, lean_object* v_a_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_){
_start:
{
lean_object* v___x_5466_; 
v___x_5466_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5452_, v_a_5455_);
if (lean_obj_tag(v___x_5466_) == 0)
{
lean_object* v_a_5467_; uint8_t v___x_5468_; lean_object* v___x_5469_; 
v_a_5467_ = lean_ctor_get(v___x_5466_, 0);
lean_inc(v_a_5467_);
lean_dec_ref(v___x_5466_);
v___x_5468_ = 0;
lean_inc_ref(v_a_5452_);
v___x_5469_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5452_, v___x_5468_, v_a_5467_, v_a_5454_, v_a_5455_, v_a_5456_, v_a_5457_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_, v_a_5462_, v_a_5463_, v_a_5464_);
if (lean_obj_tag(v___x_5469_) == 0)
{
lean_object* v_a_5470_; lean_object* v___x_5472_; uint8_t v_isShared_5473_; uint8_t v_isSharedCheck_5513_; 
v_a_5470_ = lean_ctor_get(v___x_5469_, 0);
v_isSharedCheck_5513_ = !lean_is_exclusive(v___x_5469_);
if (v_isSharedCheck_5513_ == 0)
{
v___x_5472_ = v___x_5469_;
v_isShared_5473_ = v_isSharedCheck_5513_;
goto v_resetjp_5471_;
}
else
{
lean_inc(v_a_5470_);
lean_dec(v___x_5469_);
v___x_5472_ = lean_box(0);
v_isShared_5473_ = v_isSharedCheck_5513_;
goto v_resetjp_5471_;
}
v_resetjp_5471_:
{
if (lean_obj_tag(v_a_5470_) == 1)
{
lean_object* v_val_5474_; lean_object* v___x_5475_; 
lean_del_object(v___x_5472_);
v_val_5474_ = lean_ctor_get(v_a_5470_, 0);
lean_inc(v_val_5474_);
lean_dec_ref(v_a_5470_);
v___x_5475_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5453_, v_a_5455_);
if (lean_obj_tag(v___x_5475_) == 0)
{
lean_object* v_a_5476_; lean_object* v___x_5477_; 
v_a_5476_ = lean_ctor_get(v___x_5475_, 0);
lean_inc(v_a_5476_);
lean_dec_ref(v___x_5475_);
lean_inc_ref(v_b_5453_);
v___x_5477_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_5453_, v___x_5468_, v_a_5476_, v_a_5454_, v_a_5455_, v_a_5456_, v_a_5457_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_, v_a_5462_, v_a_5463_, v_a_5464_);
if (lean_obj_tag(v___x_5477_) == 0)
{
lean_object* v_a_5478_; lean_object* v___x_5480_; uint8_t v_isShared_5481_; uint8_t v_isSharedCheck_5492_; 
v_a_5478_ = lean_ctor_get(v___x_5477_, 0);
v_isSharedCheck_5492_ = !lean_is_exclusive(v___x_5477_);
if (v_isSharedCheck_5492_ == 0)
{
v___x_5480_ = v___x_5477_;
v_isShared_5481_ = v_isSharedCheck_5492_;
goto v_resetjp_5479_;
}
else
{
lean_inc(v_a_5478_);
lean_dec(v___x_5477_);
v___x_5480_ = lean_box(0);
v_isShared_5481_ = v_isSharedCheck_5492_;
goto v_resetjp_5479_;
}
v_resetjp_5479_:
{
if (lean_obj_tag(v_a_5478_) == 1)
{
lean_object* v_val_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; 
lean_del_object(v___x_5480_);
v_val_5482_ = lean_ctor_get(v_a_5478_, 0);
lean_inc(v_val_5482_);
lean_dec_ref(v_a_5478_);
lean_inc(v_val_5482_);
lean_inc(v_val_5474_);
v___x_5483_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5483_, 0, v_val_5474_);
lean_ctor_set(v___x_5483_, 1, v_val_5482_);
v___x_5484_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5483_);
v___x_5485_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5485_, 0, v_a_5452_);
lean_ctor_set(v___x_5485_, 1, v_b_5453_);
lean_ctor_set(v___x_5485_, 2, v_val_5474_);
lean_ctor_set(v___x_5485_, 3, v_val_5482_);
v___x_5486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5486_, 0, v___x_5484_);
lean_ctor_set(v___x_5486_, 1, v___x_5485_);
v___x_5487_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5486_, v_a_5454_, v_a_5455_, v_a_5456_, v_a_5457_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_, v_a_5462_, v_a_5463_, v_a_5464_);
return v___x_5487_;
}
else
{
lean_object* v___x_5488_; lean_object* v___x_5490_; 
lean_dec(v_a_5478_);
lean_dec(v_val_5474_);
lean_dec_ref(v_b_5453_);
lean_dec_ref(v_a_5452_);
v___x_5488_ = lean_box(0);
if (v_isShared_5481_ == 0)
{
lean_ctor_set(v___x_5480_, 0, v___x_5488_);
v___x_5490_ = v___x_5480_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v___x_5488_);
v___x_5490_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
return v___x_5490_;
}
}
}
}
else
{
lean_object* v_a_5493_; lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5500_; 
lean_dec(v_val_5474_);
lean_dec_ref(v_b_5453_);
lean_dec_ref(v_a_5452_);
v_a_5493_ = lean_ctor_get(v___x_5477_, 0);
v_isSharedCheck_5500_ = !lean_is_exclusive(v___x_5477_);
if (v_isSharedCheck_5500_ == 0)
{
v___x_5495_ = v___x_5477_;
v_isShared_5496_ = v_isSharedCheck_5500_;
goto v_resetjp_5494_;
}
else
{
lean_inc(v_a_5493_);
lean_dec(v___x_5477_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5500_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
lean_object* v___x_5498_; 
if (v_isShared_5496_ == 0)
{
v___x_5498_ = v___x_5495_;
goto v_reusejp_5497_;
}
else
{
lean_object* v_reuseFailAlloc_5499_; 
v_reuseFailAlloc_5499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5499_, 0, v_a_5493_);
v___x_5498_ = v_reuseFailAlloc_5499_;
goto v_reusejp_5497_;
}
v_reusejp_5497_:
{
return v___x_5498_;
}
}
}
}
else
{
lean_object* v_a_5501_; lean_object* v___x_5503_; uint8_t v_isShared_5504_; uint8_t v_isSharedCheck_5508_; 
lean_dec(v_val_5474_);
lean_dec_ref(v_b_5453_);
lean_dec_ref(v_a_5452_);
v_a_5501_ = lean_ctor_get(v___x_5475_, 0);
v_isSharedCheck_5508_ = !lean_is_exclusive(v___x_5475_);
if (v_isSharedCheck_5508_ == 0)
{
v___x_5503_ = v___x_5475_;
v_isShared_5504_ = v_isSharedCheck_5508_;
goto v_resetjp_5502_;
}
else
{
lean_inc(v_a_5501_);
lean_dec(v___x_5475_);
v___x_5503_ = lean_box(0);
v_isShared_5504_ = v_isSharedCheck_5508_;
goto v_resetjp_5502_;
}
v_resetjp_5502_:
{
lean_object* v___x_5506_; 
if (v_isShared_5504_ == 0)
{
v___x_5506_ = v___x_5503_;
goto v_reusejp_5505_;
}
else
{
lean_object* v_reuseFailAlloc_5507_; 
v_reuseFailAlloc_5507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5507_, 0, v_a_5501_);
v___x_5506_ = v_reuseFailAlloc_5507_;
goto v_reusejp_5505_;
}
v_reusejp_5505_:
{
return v___x_5506_;
}
}
}
}
else
{
lean_object* v___x_5509_; lean_object* v___x_5511_; 
lean_dec(v_a_5470_);
lean_dec_ref(v_b_5453_);
lean_dec_ref(v_a_5452_);
v___x_5509_ = lean_box(0);
if (v_isShared_5473_ == 0)
{
lean_ctor_set(v___x_5472_, 0, v___x_5509_);
v___x_5511_ = v___x_5472_;
goto v_reusejp_5510_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v___x_5509_);
v___x_5511_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5510_;
}
v_reusejp_5510_:
{
return v___x_5511_;
}
}
}
}
else
{
lean_object* v_a_5514_; lean_object* v___x_5516_; uint8_t v_isShared_5517_; uint8_t v_isSharedCheck_5521_; 
lean_dec_ref(v_b_5453_);
lean_dec_ref(v_a_5452_);
v_a_5514_ = lean_ctor_get(v___x_5469_, 0);
v_isSharedCheck_5521_ = !lean_is_exclusive(v___x_5469_);
if (v_isSharedCheck_5521_ == 0)
{
v___x_5516_ = v___x_5469_;
v_isShared_5517_ = v_isSharedCheck_5521_;
goto v_resetjp_5515_;
}
else
{
lean_inc(v_a_5514_);
lean_dec(v___x_5469_);
v___x_5516_ = lean_box(0);
v_isShared_5517_ = v_isSharedCheck_5521_;
goto v_resetjp_5515_;
}
v_resetjp_5515_:
{
lean_object* v___x_5519_; 
if (v_isShared_5517_ == 0)
{
v___x_5519_ = v___x_5516_;
goto v_reusejp_5518_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_a_5514_);
v___x_5519_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5518_;
}
v_reusejp_5518_:
{
return v___x_5519_;
}
}
}
}
else
{
lean_object* v_a_5522_; lean_object* v___x_5524_; uint8_t v_isShared_5525_; uint8_t v_isSharedCheck_5529_; 
lean_dec_ref(v_b_5453_);
lean_dec_ref(v_a_5452_);
v_a_5522_ = lean_ctor_get(v___x_5466_, 0);
v_isSharedCheck_5529_ = !lean_is_exclusive(v___x_5466_);
if (v_isSharedCheck_5529_ == 0)
{
v___x_5524_ = v___x_5466_;
v_isShared_5525_ = v_isSharedCheck_5529_;
goto v_resetjp_5523_;
}
else
{
lean_inc(v_a_5522_);
lean_dec(v___x_5466_);
v___x_5524_ = lean_box(0);
v_isShared_5525_ = v_isSharedCheck_5529_;
goto v_resetjp_5523_;
}
v_resetjp_5523_:
{
lean_object* v___x_5527_; 
if (v_isShared_5525_ == 0)
{
v___x_5527_ = v___x_5524_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v_a_5522_);
v___x_5527_ = v_reuseFailAlloc_5528_;
goto v_reusejp_5526_;
}
v_reusejp_5526_:
{
return v___x_5527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq___boxed(lean_object* v_a_5530_, lean_object* v_b_5531_, lean_object* v_a_5532_, lean_object* v_a_5533_, lean_object* v_a_5534_, lean_object* v_a_5535_, lean_object* v_a_5536_, lean_object* v_a_5537_, lean_object* v_a_5538_, lean_object* v_a_5539_, lean_object* v_a_5540_, lean_object* v_a_5541_, lean_object* v_a_5542_, lean_object* v_a_5543_){
_start:
{
lean_object* v_res_5544_; 
v_res_5544_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5530_, v_b_5531_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_, v_a_5536_, v_a_5537_, v_a_5538_, v_a_5539_, v_a_5540_, v_a_5541_, v_a_5542_);
lean_dec(v_a_5542_);
lean_dec_ref(v_a_5541_);
lean_dec(v_a_5540_);
lean_dec_ref(v_a_5539_);
lean_dec(v_a_5538_);
lean_dec_ref(v_a_5537_);
lean_dec(v_a_5536_);
lean_dec_ref(v_a_5535_);
lean_dec(v_a_5534_);
lean_dec(v_a_5533_);
lean_dec(v_a_5532_);
return v_res_5544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(lean_object* v_a_5545_, lean_object* v_b_5546_, lean_object* v_a_5547_, lean_object* v_a_5548_, lean_object* v_a_5549_, lean_object* v_a_5550_, lean_object* v_a_5551_, lean_object* v_a_5552_, lean_object* v_a_5553_, lean_object* v_a_5554_, lean_object* v_a_5555_, lean_object* v_a_5556_, lean_object* v_a_5557_){
_start:
{
lean_object* v___x_5559_; 
v___x_5559_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5547_, v_a_5548_, v_a_5549_, v_a_5550_, v_a_5551_, v_a_5552_, v_a_5553_, v_a_5554_, v_a_5555_, v_a_5556_, v_a_5557_);
if (lean_obj_tag(v___x_5559_) == 0)
{
lean_object* v_a_5560_; lean_object* v_addRightCancelInst_x3f_5561_; 
v_a_5560_ = lean_ctor_get(v___x_5559_, 0);
lean_inc(v_a_5560_);
lean_dec_ref(v___x_5559_);
v_addRightCancelInst_x3f_5561_ = lean_ctor_get(v_a_5560_, 11);
if (lean_obj_tag(v_addRightCancelInst_x3f_5561_) == 0)
{
lean_object* v___x_5562_; 
lean_dec(v_a_5560_);
v___x_5562_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(v_a_5545_, v_b_5546_, v_a_5547_, v_a_5548_, v_a_5549_, v_a_5550_, v_a_5551_, v_a_5552_, v_a_5553_, v_a_5554_, v_a_5555_, v_a_5556_, v_a_5557_);
return v___x_5562_;
}
else
{
lean_object* v_id_5563_; lean_object* v_structId_5564_; lean_object* v___x_5565_; 
v_id_5563_ = lean_ctor_get(v_a_5560_, 0);
lean_inc(v_id_5563_);
v_structId_5564_ = lean_ctor_get(v_a_5560_, 1);
lean_inc(v_structId_5564_);
lean_dec(v_a_5560_);
lean_inc_ref(v_a_5545_);
v___x_5565_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5545_, v_a_5547_, v_a_5548_, v_a_5549_, v_a_5550_, v_a_5551_, v_a_5552_, v_a_5553_, v_a_5554_, v_a_5555_, v_a_5556_, v_a_5557_);
if (lean_obj_tag(v___x_5565_) == 0)
{
lean_object* v_a_5566_; lean_object* v_fst_5567_; lean_object* v___x_5569_; uint8_t v_isShared_5570_; uint8_t v_isSharedCheck_5655_; 
v_a_5566_ = lean_ctor_get(v___x_5565_, 0);
lean_inc(v_a_5566_);
lean_dec_ref(v___x_5565_);
v_fst_5567_ = lean_ctor_get(v_a_5566_, 0);
v_isSharedCheck_5655_ = !lean_is_exclusive(v_a_5566_);
if (v_isSharedCheck_5655_ == 0)
{
lean_object* v_unused_5656_; 
v_unused_5656_ = lean_ctor_get(v_a_5566_, 1);
lean_dec(v_unused_5656_);
v___x_5569_ = v_a_5566_;
v_isShared_5570_ = v_isSharedCheck_5655_;
goto v_resetjp_5568_;
}
else
{
lean_inc(v_fst_5567_);
lean_dec(v_a_5566_);
v___x_5569_ = lean_box(0);
v_isShared_5570_ = v_isSharedCheck_5655_;
goto v_resetjp_5568_;
}
v_resetjp_5568_:
{
lean_object* v___x_5571_; 
lean_inc_ref(v_b_5546_);
v___x_5571_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5546_, v_a_5547_, v_a_5548_, v_a_5549_, v_a_5550_, v_a_5551_, v_a_5552_, v_a_5553_, v_a_5554_, v_a_5555_, v_a_5556_, v_a_5557_);
if (lean_obj_tag(v___x_5571_) == 0)
{
lean_object* v_a_5572_; lean_object* v_fst_5573_; lean_object* v___x_5575_; uint8_t v_isShared_5576_; uint8_t v_isSharedCheck_5645_; 
v_a_5572_ = lean_ctor_get(v___x_5571_, 0);
lean_inc(v_a_5572_);
lean_dec_ref(v___x_5571_);
v_fst_5573_ = lean_ctor_get(v_a_5572_, 0);
v_isSharedCheck_5645_ = !lean_is_exclusive(v_a_5572_);
if (v_isSharedCheck_5645_ == 0)
{
lean_object* v_unused_5646_; 
v_unused_5646_ = lean_ctor_get(v_a_5572_, 1);
lean_dec(v_unused_5646_);
v___x_5575_ = v_a_5572_;
v_isShared_5576_ = v_isSharedCheck_5645_;
goto v_resetjp_5574_;
}
else
{
lean_inc(v_fst_5573_);
lean_dec(v_a_5572_);
v___x_5575_ = lean_box(0);
v_isShared_5576_ = v_isSharedCheck_5645_;
goto v_resetjp_5574_;
}
v_resetjp_5574_:
{
lean_object* v___x_5577_; 
v___x_5577_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5545_, v_a_5548_);
if (lean_obj_tag(v___x_5577_) == 0)
{
lean_object* v_a_5578_; uint8_t v___x_5579_; lean_object* v___x_5580_; 
v_a_5578_ = lean_ctor_get(v___x_5577_, 0);
lean_inc(v_a_5578_);
lean_dec_ref(v___x_5577_);
v___x_5579_ = 0;
v___x_5580_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5567_, v___x_5579_, v_a_5578_, v_structId_5564_, v_a_5548_, v_a_5549_, v_a_5550_, v_a_5551_, v_a_5552_, v_a_5553_, v_a_5554_, v_a_5555_, v_a_5556_, v_a_5557_);
if (lean_obj_tag(v___x_5580_) == 0)
{
lean_object* v_a_5581_; lean_object* v___x_5583_; uint8_t v_isShared_5584_; uint8_t v_isSharedCheck_5628_; 
v_a_5581_ = lean_ctor_get(v___x_5580_, 0);
v_isSharedCheck_5628_ = !lean_is_exclusive(v___x_5580_);
if (v_isSharedCheck_5628_ == 0)
{
v___x_5583_ = v___x_5580_;
v_isShared_5584_ = v_isSharedCheck_5628_;
goto v_resetjp_5582_;
}
else
{
lean_inc(v_a_5581_);
lean_dec(v___x_5580_);
v___x_5583_ = lean_box(0);
v_isShared_5584_ = v_isSharedCheck_5628_;
goto v_resetjp_5582_;
}
v_resetjp_5582_:
{
if (lean_obj_tag(v_a_5581_) == 1)
{
lean_object* v_val_5585_; lean_object* v___x_5586_; 
lean_del_object(v___x_5583_);
v_val_5585_ = lean_ctor_get(v_a_5581_, 0);
lean_inc(v_val_5585_);
lean_dec_ref(v_a_5581_);
v___x_5586_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5546_, v_a_5548_);
if (lean_obj_tag(v___x_5586_) == 0)
{
lean_object* v_a_5587_; lean_object* v___x_5588_; 
v_a_5587_ = lean_ctor_get(v___x_5586_, 0);
lean_inc(v_a_5587_);
lean_dec_ref(v___x_5586_);
v___x_5588_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5573_, v___x_5579_, v_a_5587_, v_structId_5564_, v_a_5548_, v_a_5549_, v_a_5550_, v_a_5551_, v_a_5552_, v_a_5553_, v_a_5554_, v_a_5555_, v_a_5556_, v_a_5557_);
if (lean_obj_tag(v___x_5588_) == 0)
{
lean_object* v_a_5589_; lean_object* v___x_5591_; uint8_t v_isShared_5592_; uint8_t v_isSharedCheck_5607_; 
v_a_5589_ = lean_ctor_get(v___x_5588_, 0);
v_isSharedCheck_5607_ = !lean_is_exclusive(v___x_5588_);
if (v_isSharedCheck_5607_ == 0)
{
v___x_5591_ = v___x_5588_;
v_isShared_5592_ = v_isSharedCheck_5607_;
goto v_resetjp_5590_;
}
else
{
lean_inc(v_a_5589_);
lean_dec(v___x_5588_);
v___x_5591_ = lean_box(0);
v_isShared_5592_ = v_isSharedCheck_5607_;
goto v_resetjp_5590_;
}
v_resetjp_5590_:
{
if (lean_obj_tag(v_a_5589_) == 1)
{
lean_object* v_val_5593_; lean_object* v___x_5595_; 
lean_del_object(v___x_5591_);
v_val_5593_ = lean_ctor_get(v_a_5589_, 0);
lean_inc(v_val_5593_);
lean_dec_ref(v_a_5589_);
lean_inc(v_val_5593_);
lean_inc(v_val_5585_);
if (v_isShared_5576_ == 0)
{
lean_ctor_set_tag(v___x_5575_, 3);
lean_ctor_set(v___x_5575_, 1, v_val_5593_);
lean_ctor_set(v___x_5575_, 0, v_val_5585_);
v___x_5595_ = v___x_5575_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5602_; 
v_reuseFailAlloc_5602_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5602_, 0, v_val_5585_);
lean_ctor_set(v_reuseFailAlloc_5602_, 1, v_val_5593_);
v___x_5595_ = v_reuseFailAlloc_5602_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5599_; 
v___x_5596_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5595_);
v___x_5597_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5597_, 0, v_a_5545_);
lean_ctor_set(v___x_5597_, 1, v_b_5546_);
lean_ctor_set(v___x_5597_, 2, v_id_5563_);
lean_ctor_set(v___x_5597_, 3, v_val_5585_);
lean_ctor_set(v___x_5597_, 4, v_val_5593_);
if (v_isShared_5570_ == 0)
{
lean_ctor_set(v___x_5569_, 1, v___x_5597_);
lean_ctor_set(v___x_5569_, 0, v___x_5596_);
v___x_5599_ = v___x_5569_;
goto v_reusejp_5598_;
}
else
{
lean_object* v_reuseFailAlloc_5601_; 
v_reuseFailAlloc_5601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5601_, 0, v___x_5596_);
lean_ctor_set(v_reuseFailAlloc_5601_, 1, v___x_5597_);
v___x_5599_ = v_reuseFailAlloc_5601_;
goto v_reusejp_5598_;
}
v_reusejp_5598_:
{
lean_object* v___x_5600_; 
v___x_5600_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5599_, v_structId_5564_, v_a_5548_, v_a_5549_, v_a_5550_, v_a_5551_, v_a_5552_, v_a_5553_, v_a_5554_, v_a_5555_, v_a_5556_, v_a_5557_);
lean_dec(v_structId_5564_);
return v___x_5600_;
}
}
}
else
{
lean_object* v___x_5603_; lean_object* v___x_5605_; 
lean_dec(v_a_5589_);
lean_dec(v_val_5585_);
lean_del_object(v___x_5575_);
lean_del_object(v___x_5569_);
lean_dec(v_structId_5564_);
lean_dec(v_id_5563_);
lean_dec_ref(v_b_5546_);
lean_dec_ref(v_a_5545_);
v___x_5603_ = lean_box(0);
if (v_isShared_5592_ == 0)
{
lean_ctor_set(v___x_5591_, 0, v___x_5603_);
v___x_5605_ = v___x_5591_;
goto v_reusejp_5604_;
}
else
{
lean_object* v_reuseFailAlloc_5606_; 
v_reuseFailAlloc_5606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5606_, 0, v___x_5603_);
v___x_5605_ = v_reuseFailAlloc_5606_;
goto v_reusejp_5604_;
}
v_reusejp_5604_:
{
return v___x_5605_;
}
}
}
}
else
{
lean_object* v_a_5608_; lean_object* v___x_5610_; uint8_t v_isShared_5611_; uint8_t v_isSharedCheck_5615_; 
lean_dec(v_val_5585_);
lean_del_object(v___x_5575_);
lean_del_object(v___x_5569_);
lean_dec(v_structId_5564_);
lean_dec(v_id_5563_);
lean_dec_ref(v_b_5546_);
lean_dec_ref(v_a_5545_);
v_a_5608_ = lean_ctor_get(v___x_5588_, 0);
v_isSharedCheck_5615_ = !lean_is_exclusive(v___x_5588_);
if (v_isSharedCheck_5615_ == 0)
{
v___x_5610_ = v___x_5588_;
v_isShared_5611_ = v_isSharedCheck_5615_;
goto v_resetjp_5609_;
}
else
{
lean_inc(v_a_5608_);
lean_dec(v___x_5588_);
v___x_5610_ = lean_box(0);
v_isShared_5611_ = v_isSharedCheck_5615_;
goto v_resetjp_5609_;
}
v_resetjp_5609_:
{
lean_object* v___x_5613_; 
if (v_isShared_5611_ == 0)
{
v___x_5613_ = v___x_5610_;
goto v_reusejp_5612_;
}
else
{
lean_object* v_reuseFailAlloc_5614_; 
v_reuseFailAlloc_5614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5614_, 0, v_a_5608_);
v___x_5613_ = v_reuseFailAlloc_5614_;
goto v_reusejp_5612_;
}
v_reusejp_5612_:
{
return v___x_5613_;
}
}
}
}
else
{
lean_object* v_a_5616_; lean_object* v___x_5618_; uint8_t v_isShared_5619_; uint8_t v_isSharedCheck_5623_; 
lean_dec(v_val_5585_);
lean_del_object(v___x_5575_);
lean_dec(v_fst_5573_);
lean_del_object(v___x_5569_);
lean_dec(v_structId_5564_);
lean_dec(v_id_5563_);
lean_dec_ref(v_b_5546_);
lean_dec_ref(v_a_5545_);
v_a_5616_ = lean_ctor_get(v___x_5586_, 0);
v_isSharedCheck_5623_ = !lean_is_exclusive(v___x_5586_);
if (v_isSharedCheck_5623_ == 0)
{
v___x_5618_ = v___x_5586_;
v_isShared_5619_ = v_isSharedCheck_5623_;
goto v_resetjp_5617_;
}
else
{
lean_inc(v_a_5616_);
lean_dec(v___x_5586_);
v___x_5618_ = lean_box(0);
v_isShared_5619_ = v_isSharedCheck_5623_;
goto v_resetjp_5617_;
}
v_resetjp_5617_:
{
lean_object* v___x_5621_; 
if (v_isShared_5619_ == 0)
{
v___x_5621_ = v___x_5618_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v_a_5616_);
v___x_5621_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
return v___x_5621_;
}
}
}
}
else
{
lean_object* v___x_5624_; lean_object* v___x_5626_; 
lean_dec(v_a_5581_);
lean_del_object(v___x_5575_);
lean_dec(v_fst_5573_);
lean_del_object(v___x_5569_);
lean_dec(v_structId_5564_);
lean_dec(v_id_5563_);
lean_dec_ref(v_b_5546_);
lean_dec_ref(v_a_5545_);
v___x_5624_ = lean_box(0);
if (v_isShared_5584_ == 0)
{
lean_ctor_set(v___x_5583_, 0, v___x_5624_);
v___x_5626_ = v___x_5583_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5627_; 
v_reuseFailAlloc_5627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5627_, 0, v___x_5624_);
v___x_5626_ = v_reuseFailAlloc_5627_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
return v___x_5626_;
}
}
}
}
else
{
lean_object* v_a_5629_; lean_object* v___x_5631_; uint8_t v_isShared_5632_; uint8_t v_isSharedCheck_5636_; 
lean_del_object(v___x_5575_);
lean_dec(v_fst_5573_);
lean_del_object(v___x_5569_);
lean_dec(v_structId_5564_);
lean_dec(v_id_5563_);
lean_dec_ref(v_b_5546_);
lean_dec_ref(v_a_5545_);
v_a_5629_ = lean_ctor_get(v___x_5580_, 0);
v_isSharedCheck_5636_ = !lean_is_exclusive(v___x_5580_);
if (v_isSharedCheck_5636_ == 0)
{
v___x_5631_ = v___x_5580_;
v_isShared_5632_ = v_isSharedCheck_5636_;
goto v_resetjp_5630_;
}
else
{
lean_inc(v_a_5629_);
lean_dec(v___x_5580_);
v___x_5631_ = lean_box(0);
v_isShared_5632_ = v_isSharedCheck_5636_;
goto v_resetjp_5630_;
}
v_resetjp_5630_:
{
lean_object* v___x_5634_; 
if (v_isShared_5632_ == 0)
{
v___x_5634_ = v___x_5631_;
goto v_reusejp_5633_;
}
else
{
lean_object* v_reuseFailAlloc_5635_; 
v_reuseFailAlloc_5635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5635_, 0, v_a_5629_);
v___x_5634_ = v_reuseFailAlloc_5635_;
goto v_reusejp_5633_;
}
v_reusejp_5633_:
{
return v___x_5634_;
}
}
}
}
else
{
lean_object* v_a_5637_; lean_object* v___x_5639_; uint8_t v_isShared_5640_; uint8_t v_isSharedCheck_5644_; 
lean_del_object(v___x_5575_);
lean_dec(v_fst_5573_);
lean_del_object(v___x_5569_);
lean_dec(v_fst_5567_);
lean_dec(v_structId_5564_);
lean_dec(v_id_5563_);
lean_dec_ref(v_b_5546_);
lean_dec_ref(v_a_5545_);
v_a_5637_ = lean_ctor_get(v___x_5577_, 0);
v_isSharedCheck_5644_ = !lean_is_exclusive(v___x_5577_);
if (v_isSharedCheck_5644_ == 0)
{
v___x_5639_ = v___x_5577_;
v_isShared_5640_ = v_isSharedCheck_5644_;
goto v_resetjp_5638_;
}
else
{
lean_inc(v_a_5637_);
lean_dec(v___x_5577_);
v___x_5639_ = lean_box(0);
v_isShared_5640_ = v_isSharedCheck_5644_;
goto v_resetjp_5638_;
}
v_resetjp_5638_:
{
lean_object* v___x_5642_; 
if (v_isShared_5640_ == 0)
{
v___x_5642_ = v___x_5639_;
goto v_reusejp_5641_;
}
else
{
lean_object* v_reuseFailAlloc_5643_; 
v_reuseFailAlloc_5643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5643_, 0, v_a_5637_);
v___x_5642_ = v_reuseFailAlloc_5643_;
goto v_reusejp_5641_;
}
v_reusejp_5641_:
{
return v___x_5642_;
}
}
}
}
}
else
{
lean_object* v_a_5647_; lean_object* v___x_5649_; uint8_t v_isShared_5650_; uint8_t v_isSharedCheck_5654_; 
lean_del_object(v___x_5569_);
lean_dec(v_fst_5567_);
lean_dec(v_structId_5564_);
lean_dec(v_id_5563_);
lean_dec_ref(v_b_5546_);
lean_dec_ref(v_a_5545_);
v_a_5647_ = lean_ctor_get(v___x_5571_, 0);
v_isSharedCheck_5654_ = !lean_is_exclusive(v___x_5571_);
if (v_isSharedCheck_5654_ == 0)
{
v___x_5649_ = v___x_5571_;
v_isShared_5650_ = v_isSharedCheck_5654_;
goto v_resetjp_5648_;
}
else
{
lean_inc(v_a_5647_);
lean_dec(v___x_5571_);
v___x_5649_ = lean_box(0);
v_isShared_5650_ = v_isSharedCheck_5654_;
goto v_resetjp_5648_;
}
v_resetjp_5648_:
{
lean_object* v___x_5652_; 
if (v_isShared_5650_ == 0)
{
v___x_5652_ = v___x_5649_;
goto v_reusejp_5651_;
}
else
{
lean_object* v_reuseFailAlloc_5653_; 
v_reuseFailAlloc_5653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5653_, 0, v_a_5647_);
v___x_5652_ = v_reuseFailAlloc_5653_;
goto v_reusejp_5651_;
}
v_reusejp_5651_:
{
return v___x_5652_;
}
}
}
}
}
else
{
lean_object* v_a_5657_; lean_object* v___x_5659_; uint8_t v_isShared_5660_; uint8_t v_isSharedCheck_5664_; 
lean_dec(v_structId_5564_);
lean_dec(v_id_5563_);
lean_dec_ref(v_b_5546_);
lean_dec_ref(v_a_5545_);
v_a_5657_ = lean_ctor_get(v___x_5565_, 0);
v_isSharedCheck_5664_ = !lean_is_exclusive(v___x_5565_);
if (v_isSharedCheck_5664_ == 0)
{
v___x_5659_ = v___x_5565_;
v_isShared_5660_ = v_isSharedCheck_5664_;
goto v_resetjp_5658_;
}
else
{
lean_inc(v_a_5657_);
lean_dec(v___x_5565_);
v___x_5659_ = lean_box(0);
v_isShared_5660_ = v_isSharedCheck_5664_;
goto v_resetjp_5658_;
}
v_resetjp_5658_:
{
lean_object* v___x_5662_; 
if (v_isShared_5660_ == 0)
{
v___x_5662_ = v___x_5659_;
goto v_reusejp_5661_;
}
else
{
lean_object* v_reuseFailAlloc_5663_; 
v_reuseFailAlloc_5663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5663_, 0, v_a_5657_);
v___x_5662_ = v_reuseFailAlloc_5663_;
goto v_reusejp_5661_;
}
v_reusejp_5661_:
{
return v___x_5662_;
}
}
}
}
}
else
{
lean_object* v_a_5665_; lean_object* v___x_5667_; uint8_t v_isShared_5668_; uint8_t v_isSharedCheck_5672_; 
lean_dec_ref(v_b_5546_);
lean_dec_ref(v_a_5545_);
v_a_5665_ = lean_ctor_get(v___x_5559_, 0);
v_isSharedCheck_5672_ = !lean_is_exclusive(v___x_5559_);
if (v_isSharedCheck_5672_ == 0)
{
v___x_5667_ = v___x_5559_;
v_isShared_5668_ = v_isSharedCheck_5672_;
goto v_resetjp_5666_;
}
else
{
lean_inc(v_a_5665_);
lean_dec(v___x_5559_);
v___x_5667_ = lean_box(0);
v_isShared_5668_ = v_isSharedCheck_5672_;
goto v_resetjp_5666_;
}
v_resetjp_5666_:
{
lean_object* v___x_5670_; 
if (v_isShared_5668_ == 0)
{
v___x_5670_ = v___x_5667_;
goto v_reusejp_5669_;
}
else
{
lean_object* v_reuseFailAlloc_5671_; 
v_reuseFailAlloc_5671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5671_, 0, v_a_5665_);
v___x_5670_ = v_reuseFailAlloc_5671_;
goto v_reusejp_5669_;
}
v_reusejp_5669_:
{
return v___x_5670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq___boxed(lean_object* v_a_5673_, lean_object* v_b_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_, lean_object* v_a_5683_, lean_object* v_a_5684_, lean_object* v_a_5685_, lean_object* v_a_5686_){
_start:
{
lean_object* v_res_5687_; 
v_res_5687_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5673_, v_b_5674_, v_a_5675_, v_a_5676_, v_a_5677_, v_a_5678_, v_a_5679_, v_a_5680_, v_a_5681_, v_a_5682_, v_a_5683_, v_a_5684_, v_a_5685_);
lean_dec(v_a_5685_);
lean_dec_ref(v_a_5684_);
lean_dec(v_a_5683_);
lean_dec_ref(v_a_5682_);
lean_dec(v_a_5681_);
lean_dec_ref(v_a_5680_);
lean_dec(v_a_5679_);
lean_dec_ref(v_a_5678_);
lean_dec(v_a_5677_);
lean_dec(v_a_5676_);
lean_dec(v_a_5675_);
return v_res_5687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(lean_object* v_a_5688_, lean_object* v_b_5689_, lean_object* v_a_5690_, lean_object* v_a_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_, lean_object* v_a_5699_){
_start:
{
lean_object* v___x_5701_; 
v___x_5701_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5688_, v_b_5689_, v_a_5690_, v_a_5698_);
if (lean_obj_tag(v___x_5701_) == 0)
{
lean_object* v_a_5702_; 
v_a_5702_ = lean_ctor_get(v___x_5701_, 0);
lean_inc(v_a_5702_);
lean_dec_ref(v___x_5701_);
if (lean_obj_tag(v_a_5702_) == 1)
{
lean_object* v_val_5703_; lean_object* v___x_5704_; 
v_val_5703_ = lean_ctor_get(v_a_5702_, 0);
lean_inc(v_val_5703_);
lean_dec_ref(v_a_5702_);
v___x_5704_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5703_, v_a_5690_, v_a_5691_, v_a_5692_, v_a_5693_, v_a_5694_, v_a_5695_, v_a_5696_, v_a_5697_, v_a_5698_, v_a_5699_);
if (lean_obj_tag(v___x_5704_) == 0)
{
lean_object* v_a_5705_; uint8_t v___x_5706_; 
v_a_5705_ = lean_ctor_get(v___x_5704_, 0);
lean_inc(v_a_5705_);
lean_dec_ref(v___x_5704_);
v___x_5706_ = lean_unbox(v_a_5705_);
lean_dec(v_a_5705_);
if (v___x_5706_ == 0)
{
lean_object* v___x_5707_; 
v___x_5707_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5688_, v_b_5689_, v_val_5703_, v_a_5690_, v_a_5691_, v_a_5692_, v_a_5693_, v_a_5694_, v_a_5695_, v_a_5696_, v_a_5697_, v_a_5698_, v_a_5699_);
lean_dec(v_val_5703_);
return v___x_5707_;
}
else
{
lean_object* v___x_5708_; 
v___x_5708_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5688_, v_b_5689_, v_val_5703_, v_a_5690_, v_a_5691_, v_a_5692_, v_a_5693_, v_a_5694_, v_a_5695_, v_a_5696_, v_a_5697_, v_a_5698_, v_a_5699_);
lean_dec(v_val_5703_);
return v___x_5708_;
}
}
else
{
lean_object* v_a_5709_; lean_object* v___x_5711_; uint8_t v_isShared_5712_; uint8_t v_isSharedCheck_5716_; 
lean_dec(v_val_5703_);
lean_dec_ref(v_b_5689_);
lean_dec_ref(v_a_5688_);
v_a_5709_ = lean_ctor_get(v___x_5704_, 0);
v_isSharedCheck_5716_ = !lean_is_exclusive(v___x_5704_);
if (v_isSharedCheck_5716_ == 0)
{
v___x_5711_ = v___x_5704_;
v_isShared_5712_ = v_isSharedCheck_5716_;
goto v_resetjp_5710_;
}
else
{
lean_inc(v_a_5709_);
lean_dec(v___x_5704_);
v___x_5711_ = lean_box(0);
v_isShared_5712_ = v_isSharedCheck_5716_;
goto v_resetjp_5710_;
}
v_resetjp_5710_:
{
lean_object* v___x_5714_; 
if (v_isShared_5712_ == 0)
{
v___x_5714_ = v___x_5711_;
goto v_reusejp_5713_;
}
else
{
lean_object* v_reuseFailAlloc_5715_; 
v_reuseFailAlloc_5715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5715_, 0, v_a_5709_);
v___x_5714_ = v_reuseFailAlloc_5715_;
goto v_reusejp_5713_;
}
v_reusejp_5713_:
{
return v___x_5714_;
}
}
}
}
else
{
lean_object* v___x_5717_; 
lean_dec(v_a_5702_);
v___x_5717_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5688_, v_b_5689_, v_a_5690_, v_a_5698_);
if (lean_obj_tag(v___x_5717_) == 0)
{
lean_object* v_a_5718_; lean_object* v___x_5720_; uint8_t v_isShared_5721_; uint8_t v_isSharedCheck_5728_; 
v_a_5718_ = lean_ctor_get(v___x_5717_, 0);
v_isSharedCheck_5728_ = !lean_is_exclusive(v___x_5717_);
if (v_isSharedCheck_5728_ == 0)
{
v___x_5720_ = v___x_5717_;
v_isShared_5721_ = v_isSharedCheck_5728_;
goto v_resetjp_5719_;
}
else
{
lean_inc(v_a_5718_);
lean_dec(v___x_5717_);
v___x_5720_ = lean_box(0);
v_isShared_5721_ = v_isSharedCheck_5728_;
goto v_resetjp_5719_;
}
v_resetjp_5719_:
{
if (lean_obj_tag(v_a_5718_) == 1)
{
lean_object* v_val_5722_; lean_object* v___x_5723_; 
lean_del_object(v___x_5720_);
v_val_5722_ = lean_ctor_get(v_a_5718_, 0);
lean_inc(v_val_5722_);
lean_dec_ref(v_a_5718_);
v___x_5723_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5688_, v_b_5689_, v_val_5722_, v_a_5690_, v_a_5691_, v_a_5692_, v_a_5693_, v_a_5694_, v_a_5695_, v_a_5696_, v_a_5697_, v_a_5698_, v_a_5699_);
lean_dec(v_val_5722_);
return v___x_5723_;
}
else
{
lean_object* v___x_5724_; lean_object* v___x_5726_; 
lean_dec(v_a_5718_);
lean_dec_ref(v_b_5689_);
lean_dec_ref(v_a_5688_);
v___x_5724_ = lean_box(0);
if (v_isShared_5721_ == 0)
{
lean_ctor_set(v___x_5720_, 0, v___x_5724_);
v___x_5726_ = v___x_5720_;
goto v_reusejp_5725_;
}
else
{
lean_object* v_reuseFailAlloc_5727_; 
v_reuseFailAlloc_5727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5727_, 0, v___x_5724_);
v___x_5726_ = v_reuseFailAlloc_5727_;
goto v_reusejp_5725_;
}
v_reusejp_5725_:
{
return v___x_5726_;
}
}
}
}
else
{
lean_object* v_a_5729_; lean_object* v___x_5731_; uint8_t v_isShared_5732_; uint8_t v_isSharedCheck_5736_; 
lean_dec_ref(v_b_5689_);
lean_dec_ref(v_a_5688_);
v_a_5729_ = lean_ctor_get(v___x_5717_, 0);
v_isSharedCheck_5736_ = !lean_is_exclusive(v___x_5717_);
if (v_isSharedCheck_5736_ == 0)
{
v___x_5731_ = v___x_5717_;
v_isShared_5732_ = v_isSharedCheck_5736_;
goto v_resetjp_5730_;
}
else
{
lean_inc(v_a_5729_);
lean_dec(v___x_5717_);
v___x_5731_ = lean_box(0);
v_isShared_5732_ = v_isSharedCheck_5736_;
goto v_resetjp_5730_;
}
v_resetjp_5730_:
{
lean_object* v___x_5734_; 
if (v_isShared_5732_ == 0)
{
v___x_5734_ = v___x_5731_;
goto v_reusejp_5733_;
}
else
{
lean_object* v_reuseFailAlloc_5735_; 
v_reuseFailAlloc_5735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5735_, 0, v_a_5729_);
v___x_5734_ = v_reuseFailAlloc_5735_;
goto v_reusejp_5733_;
}
v_reusejp_5733_:
{
return v___x_5734_;
}
}
}
}
}
else
{
lean_object* v_a_5737_; lean_object* v___x_5739_; uint8_t v_isShared_5740_; uint8_t v_isSharedCheck_5744_; 
lean_dec_ref(v_b_5689_);
lean_dec_ref(v_a_5688_);
v_a_5737_ = lean_ctor_get(v___x_5701_, 0);
v_isSharedCheck_5744_ = !lean_is_exclusive(v___x_5701_);
if (v_isSharedCheck_5744_ == 0)
{
v___x_5739_ = v___x_5701_;
v_isShared_5740_ = v_isSharedCheck_5744_;
goto v_resetjp_5738_;
}
else
{
lean_inc(v_a_5737_);
lean_dec(v___x_5701_);
v___x_5739_ = lean_box(0);
v_isShared_5740_ = v_isSharedCheck_5744_;
goto v_resetjp_5738_;
}
v_resetjp_5738_:
{
lean_object* v___x_5742_; 
if (v_isShared_5740_ == 0)
{
v___x_5742_ = v___x_5739_;
goto v_reusejp_5741_;
}
else
{
lean_object* v_reuseFailAlloc_5743_; 
v_reuseFailAlloc_5743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5743_, 0, v_a_5737_);
v___x_5742_ = v_reuseFailAlloc_5743_;
goto v_reusejp_5741_;
}
v_reusejp_5741_:
{
return v___x_5742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed(lean_object* v_a_5745_, lean_object* v_b_5746_, lean_object* v_a_5747_, lean_object* v_a_5748_, lean_object* v_a_5749_, lean_object* v_a_5750_, lean_object* v_a_5751_, lean_object* v_a_5752_, lean_object* v_a_5753_, lean_object* v_a_5754_, lean_object* v_a_5755_, lean_object* v_a_5756_, lean_object* v_a_5757_){
_start:
{
lean_object* v_res_5758_; 
v_res_5758_ = l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(v_a_5745_, v_b_5746_, v_a_5747_, v_a_5748_, v_a_5749_, v_a_5750_, v_a_5751_, v_a_5752_, v_a_5753_, v_a_5754_, v_a_5755_, v_a_5756_);
lean_dec(v_a_5756_);
lean_dec_ref(v_a_5755_);
lean_dec(v_a_5754_);
lean_dec_ref(v_a_5753_);
lean_dec(v_a_5752_);
lean_dec_ref(v_a_5751_);
lean_dec(v_a_5750_);
lean_dec_ref(v_a_5749_);
lean_dec(v_a_5748_);
lean_dec(v_a_5747_);
return v_res_5758_;
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
