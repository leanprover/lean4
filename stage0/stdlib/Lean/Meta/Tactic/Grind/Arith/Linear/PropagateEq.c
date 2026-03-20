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
lean_inc(v_a_916_);
lean_inc_ref(v_a_915_);
lean_inc(v_a_914_);
lean_inc_ref(v_a_913_);
lean_inc(v_a_912_);
lean_inc_ref(v_a_911_);
lean_inc(v_a_910_);
lean_inc_ref(v_a_909_);
lean_inc(v_a_908_);
lean_inc(v_a_907_);
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
lean_inc(v_a_916_);
lean_inc_ref(v_a_915_);
lean_inc(v_a_914_);
lean_inc_ref(v_a_913_);
lean_inc(v_a_912_);
lean_inc_ref(v_a_911_);
lean_inc(v_a_910_);
lean_inc_ref(v_a_909_);
lean_inc(v_a_908_);
lean_inc(v_a_907_);
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
lean_inc(v_a_916_);
lean_inc_ref(v_a_915_);
lean_inc(v_a_914_);
lean_inc_ref(v_a_913_);
lean_inc(v_a_912_);
lean_inc_ref(v_a_911_);
lean_inc(v_a_910_);
lean_inc_ref(v_a_909_);
lean_inc(v_a_908_);
lean_inc(v_a_907_);
v___x_946_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(v___x_945_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v_p_948_; lean_object* v___x_949_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref(v___x_946_);
v_p_948_ = lean_ctor_get(v_a_947_, 0);
lean_inc(v_a_916_);
lean_inc_ref(v_a_915_);
lean_inc(v_a_914_);
lean_inc_ref(v_a_913_);
lean_inc(v_a_912_);
lean_inc_ref(v_a_911_);
lean_inc(v_a_910_);
lean_inc_ref(v_a_909_);
lean_inc(v_a_908_);
lean_inc(v_a_907_);
lean_inc(v___y_941_);
lean_inc_ref(v_p_948_);
v___x_949_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_948_, v___y_941_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_951_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref(v___x_949_);
lean_inc(v_a_916_);
lean_inc_ref(v_a_915_);
lean_inc(v_a_914_);
lean_inc_ref(v_a_913_);
lean_inc(v_a_912_);
lean_inc_ref(v_a_911_);
lean_inc(v_a_910_);
lean_inc_ref(v_a_909_);
lean_inc(v_a_908_);
lean_inc(v_a_907_);
lean_inc(v_a_906_);
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
lean_inc(v_a_916_);
lean_inc_ref(v_a_915_);
lean_inc(v_a_914_);
lean_inc_ref(v_a_913_);
lean_inc(v_a_912_);
lean_inc_ref(v_a_911_);
lean_inc(v_a_910_);
lean_inc_ref(v_a_909_);
lean_inc(v_a_908_);
lean_inc(v_a_907_);
lean_inc(v_a_906_);
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
lean_inc(v_a_916_);
lean_inc_ref(v_a_915_);
lean_inc(v_a_914_);
lean_inc_ref(v_a_913_);
lean_inc(v_a_912_);
lean_inc_ref(v_a_911_);
lean_inc(v_a_910_);
lean_inc_ref(v_a_909_);
lean_inc(v_a_908_);
lean_inc(v_a_907_);
lean_inc(v___y_941_);
v___x_971_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v___x_967_, v___y_941_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref(v___x_971_);
lean_inc(v_a_916_);
lean_inc_ref(v_a_915_);
lean_inc(v_a_914_);
lean_inc_ref(v_a_913_);
lean_inc(v_a_912_);
lean_inc_ref(v_a_911_);
lean_inc(v_a_910_);
lean_inc_ref(v_a_909_);
lean_inc(v_a_908_);
lean_inc(v_a_907_);
lean_inc(v_a_906_);
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
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
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
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
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
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
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
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
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
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
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
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
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
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
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
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
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
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
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
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
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
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
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
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
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
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
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
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
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
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
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
lean_inc(v_a_1110_);
lean_inc_ref(v_a_1109_);
lean_inc(v_a_1108_);
lean_inc_ref(v_a_1107_);
lean_inc(v_a_1106_);
lean_inc_ref(v_a_1105_);
lean_inc(v_a_1104_);
lean_inc_ref(v_a_1103_);
lean_inc(v_a_1102_);
lean_inc(v_a_1101_);
lean_inc(v_a_1100_);
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
lean_inc(v_a_1110_);
lean_inc_ref(v_a_1109_);
lean_inc(v_a_1108_);
lean_inc_ref(v_a_1107_);
lean_inc(v_a_1106_);
lean_inc_ref(v_a_1105_);
lean_inc(v_a_1104_);
lean_inc_ref(v_a_1103_);
lean_inc(v_a_1102_);
lean_inc(v_a_1101_);
lean_inc(v_a_1100_);
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
lean_inc(v_a_1110_);
lean_inc_ref(v_a_1109_);
lean_inc(v_a_1108_);
lean_inc_ref(v_a_1107_);
lean_inc(v_a_1106_);
lean_inc_ref(v_a_1105_);
lean_inc(v_a_1104_);
lean_inc_ref(v_a_1103_);
lean_inc(v_a_1102_);
lean_inc(v_a_1101_);
lean_inc(v_a_1100_);
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
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec(v_a_1100_);
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
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec(v_a_1100_);
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
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec(v_a_1100_);
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
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec(v_a_1100_);
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
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec(v_a_1100_);
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
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec(v_a_1100_);
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
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec(v_a_1100_);
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
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec(v_a_1100_);
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
lean_object* v___x_1216_; lean_object* v___f_1217_; lean_object* v___x_3554__overap_1218_; lean_object* v___x_1219_; 
v___x_1216_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0);
v___f_1217_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1217_, 0, v___x_1216_);
v___x_3554__overap_1218_ = lean_panic_fn(v___f_1217_, v_msg_1203_);
v___x_1219_ = lean_apply_12(v___x_3554__overap_1218_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, lean_box(0));
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___boxed(lean_object* v_msg_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v_msg_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
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
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec(v___y_1271_);
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
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
lean_dec(v_a_1250_);
lean_dec_ref(v_a_1249_);
lean_dec(v_a_1248_);
lean_dec(v_a_1247_);
lean_dec(v_a_1246_);
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
lean_object* v_fileName_1401_; lean_object* v_fileMap_1402_; lean_object* v_options_1403_; lean_object* v_currRecDepth_1404_; lean_object* v_maxRecDepth_1405_; lean_object* v_ref_1406_; lean_object* v_currNamespace_1407_; lean_object* v_openDecls_1408_; lean_object* v_initHeartbeats_1409_; lean_object* v_maxHeartbeats_1410_; lean_object* v_quotContext_1411_; lean_object* v_currMacroScope_1412_; uint8_t v_diag_1413_; lean_object* v_cancelTk_x3f_1414_; uint8_t v_suppressElabErrors_1415_; lean_object* v_inheritedTraceOptions_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1536_; 
v_fileName_1401_ = lean_ctor_get(v_a_1398_, 0);
v_fileMap_1402_ = lean_ctor_get(v_a_1398_, 1);
v_options_1403_ = lean_ctor_get(v_a_1398_, 2);
v_currRecDepth_1404_ = lean_ctor_get(v_a_1398_, 3);
v_maxRecDepth_1405_ = lean_ctor_get(v_a_1398_, 4);
v_ref_1406_ = lean_ctor_get(v_a_1398_, 5);
v_currNamespace_1407_ = lean_ctor_get(v_a_1398_, 6);
v_openDecls_1408_ = lean_ctor_get(v_a_1398_, 7);
v_initHeartbeats_1409_ = lean_ctor_get(v_a_1398_, 8);
v_maxHeartbeats_1410_ = lean_ctor_get(v_a_1398_, 9);
v_quotContext_1411_ = lean_ctor_get(v_a_1398_, 10);
v_currMacroScope_1412_ = lean_ctor_get(v_a_1398_, 11);
v_diag_1413_ = lean_ctor_get_uint8(v_a_1398_, sizeof(void*)*14);
v_cancelTk_x3f_1414_ = lean_ctor_get(v_a_1398_, 12);
v_suppressElabErrors_1415_ = lean_ctor_get_uint8(v_a_1398_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1416_ = lean_ctor_get(v_a_1398_, 13);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_a_1398_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1418_ = v_a_1398_;
v_isShared_1419_ = v_isSharedCheck_1536_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_inheritedTraceOptions_1416_);
lean_inc(v_cancelTk_x3f_1414_);
lean_inc(v_currMacroScope_1412_);
lean_inc(v_quotContext_1411_);
lean_inc(v_maxHeartbeats_1410_);
lean_inc(v_initHeartbeats_1409_);
lean_inc(v_openDecls_1408_);
lean_inc(v_currNamespace_1407_);
lean_inc(v_ref_1406_);
lean_inc(v_maxRecDepth_1405_);
lean_inc(v_currRecDepth_1404_);
lean_inc(v_options_1403_);
lean_inc(v_fileMap_1402_);
lean_inc(v_fileName_1401_);
lean_dec(v_a_1398_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1536_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
uint8_t v___x_1420_; 
v___x_1420_ = lean_nat_dec_eq(v_currRecDepth_1404_, v_maxRecDepth_1405_);
if (v___x_1420_ == 0)
{
lean_object* v_p_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1425_; 
v_p_1421_ = lean_ctor_get(v_c_1388_, 0);
v___x_1422_ = lean_unsigned_to_nat(1u);
v___x_1423_ = lean_nat_add(v_currRecDepth_1404_, v___x_1422_);
lean_dec(v_currRecDepth_1404_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 3, v___x_1423_);
v___x_1425_ = v___x_1418_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_fileName_1401_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_fileMap_1402_);
lean_ctor_set(v_reuseFailAlloc_1534_, 2, v_options_1403_);
lean_ctor_set(v_reuseFailAlloc_1534_, 3, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1534_, 4, v_maxRecDepth_1405_);
lean_ctor_set(v_reuseFailAlloc_1534_, 5, v_ref_1406_);
lean_ctor_set(v_reuseFailAlloc_1534_, 6, v_currNamespace_1407_);
lean_ctor_set(v_reuseFailAlloc_1534_, 7, v_openDecls_1408_);
lean_ctor_set(v_reuseFailAlloc_1534_, 8, v_initHeartbeats_1409_);
lean_ctor_set(v_reuseFailAlloc_1534_, 9, v_maxHeartbeats_1410_);
lean_ctor_set(v_reuseFailAlloc_1534_, 10, v_quotContext_1411_);
lean_ctor_set(v_reuseFailAlloc_1534_, 11, v_currMacroScope_1412_);
lean_ctor_set(v_reuseFailAlloc_1534_, 12, v_cancelTk_x3f_1414_);
lean_ctor_set(v_reuseFailAlloc_1534_, 13, v_inheritedTraceOptions_1416_);
lean_ctor_set_uint8(v_reuseFailAlloc_1534_, sizeof(void*)*14, v_diag_1413_);
lean_ctor_set_uint8(v_reuseFailAlloc_1534_, sizeof(void*)*14 + 1, v_suppressElabErrors_1415_);
v___x_1425_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
lean_object* v___x_1426_; 
lean_inc(v_p_1421_);
v___x_1426_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_1421_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v___x_1425_, v_a_1399_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1525_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1429_ = v___x_1426_;
v_isShared_1430_ = v_isSharedCheck_1525_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1525_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
if (lean_obj_tag(v_a_1427_) == 1)
{
lean_object* v_val_1431_; lean_object* v_snd_1432_; lean_object* v_fst_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1521_; 
lean_del_object(v___x_1429_);
v_val_1431_ = lean_ctor_get(v_a_1427_, 0);
lean_inc(v_val_1431_);
lean_dec_ref(v_a_1427_);
v_snd_1432_ = lean_ctor_get(v_val_1431_, 1);
v_fst_1433_ = lean_ctor_get(v_val_1431_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_val_1431_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1435_ = v_val_1431_;
v_isShared_1436_ = v_isSharedCheck_1521_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_snd_1432_);
lean_inc(v_fst_1433_);
lean_dec(v_val_1431_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1521_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v_fst_1437_; lean_object* v_snd_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1520_; 
v_fst_1437_ = lean_ctor_get(v_snd_1432_, 0);
v_snd_1438_ = lean_ctor_get(v_snd_1432_, 1);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_snd_1432_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1440_ = v_snd_1432_;
v_isShared_1441_ = v_isSharedCheck_1520_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_snd_1438_);
lean_inc(v_fst_1437_);
lean_dec(v_snd_1432_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1520_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_1460_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_1459_, v___x_1425_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; uint8_t v___x_1462_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref(v___x_1460_);
v___x_1462_ = lean_unbox(v_a_1461_);
lean_dec(v_a_1461_);
if (v___x_1462_ == 0)
{
lean_del_object(v___x_1435_);
v___y_1443_ = v_a_1389_;
v___y_1444_ = v_a_1390_;
v___y_1445_ = v_a_1391_;
v___y_1446_ = v_a_1392_;
v___y_1447_ = v_a_1393_;
v___y_1448_ = v_a_1394_;
v___y_1449_ = v_a_1395_;
v___y_1450_ = v_a_1396_;
v___y_1451_ = v_a_1397_;
v___y_1452_ = v___x_1425_;
v___y_1453_ = v_a_1399_;
goto v___jp_1442_;
}
else
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_1433_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v___x_1425_, v_a_1399_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1465_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref(v___x_1463_);
v___x_1465_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_c_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v___x_1425_, v_a_1399_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1467_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref(v___x_1465_);
v___x_1467_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_fst_1437_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v___x_1425_, v_a_1399_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1472_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1468_);
lean_dec_ref(v___x_1467_);
v___x_1469_ = l_Lean_MessageData_ofExpr(v_a_1464_);
v___x_1470_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6);
if (v_isShared_1436_ == 0)
{
lean_ctor_set_tag(v___x_1435_, 7);
lean_ctor_set(v___x_1435_, 1, v___x_1470_);
lean_ctor_set(v___x_1435_, 0, v___x_1469_);
v___x_1472_ = v___x_1435_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1473_ = l_Lean_MessageData_ofExpr(v_a_1466_);
v___x_1474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1472_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
lean_ctor_set(v___x_1475_, 1, v___x_1470_);
v___x_1476_ = l_Lean_MessageData_ofExpr(v_a_1468_);
v___x_1477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1475_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_1459_, v___x_1477_, v_a_1396_, v_a_1397_, v___x_1425_, v_a_1399_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_dec_ref(v___x_1478_);
v___y_1443_ = v_a_1389_;
v___y_1444_ = v_a_1390_;
v___y_1445_ = v_a_1391_;
v___y_1446_ = v_a_1392_;
v___y_1447_ = v_a_1393_;
v___y_1448_ = v_a_1394_;
v___y_1449_ = v_a_1395_;
v___y_1450_ = v_a_1396_;
v___y_1451_ = v_a_1397_;
v___y_1452_ = v___x_1425_;
v___y_1453_ = v_a_1399_;
goto v___jp_1442_;
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_del_object(v___x_1440_);
lean_dec(v_snd_1438_);
lean_dec(v_fst_1437_);
lean_dec(v_fst_1433_);
lean_dec_ref(v___x_1425_);
lean_dec_ref(v_c_1388_);
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec(v_a_1466_);
lean_dec(v_a_1464_);
lean_del_object(v___x_1440_);
lean_dec(v_snd_1438_);
lean_dec(v_fst_1437_);
lean_del_object(v___x_1435_);
lean_dec(v_fst_1433_);
lean_dec_ref(v___x_1425_);
lean_dec_ref(v_c_1388_);
v_a_1488_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1467_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1467_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec(v_a_1464_);
lean_del_object(v___x_1440_);
lean_dec(v_snd_1438_);
lean_dec(v_fst_1437_);
lean_del_object(v___x_1435_);
lean_dec(v_fst_1433_);
lean_dec_ref(v___x_1425_);
lean_dec_ref(v_c_1388_);
v_a_1496_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1465_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1465_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_del_object(v___x_1440_);
lean_dec(v_snd_1438_);
lean_dec(v_fst_1437_);
lean_del_object(v___x_1435_);
lean_dec(v_fst_1433_);
lean_dec_ref(v___x_1425_);
lean_dec_ref(v_c_1388_);
v_a_1504_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1463_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1463_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
lean_del_object(v___x_1440_);
lean_dec(v_snd_1438_);
lean_dec(v_fst_1437_);
lean_del_object(v___x_1435_);
lean_dec(v_fst_1433_);
lean_dec_ref(v___x_1425_);
lean_dec_ref(v_c_1388_);
v_a_1512_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1460_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1460_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
v___jp_1442_:
{
lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1454_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_1454_, 0, v_fst_1433_);
lean_ctor_set(v___x_1454_, 1, v_fst_1437_);
lean_ctor_set(v___x_1454_, 2, v_c_1388_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 1, v___x_1454_);
lean_ctor_set(v___x_1440_, 0, v_snd_1438_);
v___x_1456_ = v___x_1440_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_snd_1438_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
v_c_1388_ = v___x_1456_;
v_a_1389_ = v___y_1443_;
v_a_1390_ = v___y_1444_;
v_a_1391_ = v___y_1445_;
v_a_1392_ = v___y_1446_;
v_a_1393_ = v___y_1447_;
v_a_1394_ = v___y_1448_;
v_a_1395_ = v___y_1449_;
v_a_1396_ = v___y_1450_;
v_a_1397_ = v___y_1451_;
v_a_1398_ = v___y_1452_;
v_a_1399_ = v___y_1453_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_1523_; 
lean_dec(v_a_1427_);
lean_dec_ref(v___x_1425_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v_c_1388_);
v___x_1523_ = v___x_1429_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_c_1388_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_dec_ref(v___x_1425_);
lean_dec_ref(v_c_1388_);
v_a_1526_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1426_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1426_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
else
{
lean_object* v___x_1535_; 
lean_del_object(v___x_1418_);
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
v___x_1535_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1406_);
return v___x_1535_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object* v_c_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_);
lean_dec(v_a_1548_);
lean_dec(v_a_1546_);
lean_dec_ref(v_a_1545_);
lean_dec(v_a_1544_);
lean_dec_ref(v_a_1543_);
lean_dec(v_a_1542_);
lean_dec_ref(v_a_1541_);
lean_dec(v_a_1540_);
lean_dec(v_a_1539_);
lean_dec(v_a_1538_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v_ref_1557_; lean_object* v___x_1558_; lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1567_; 
v_ref_1557_ = lean_ctor_get(v___y_1554_, 5);
v___x_1558_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3_spec__6(v_msg_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1565_; 
lean_inc(v_ref_1557_);
v___x_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1563_, 0, v_ref_1557_);
lean_ctor_set(v___x_1563_, 1, v_a_1559_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set_tag(v___x_1561_, 1);
lean_ctor_set(v___x_1561_, 0, v___x_1563_);
v___x_1565_ = v___x_1561_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
return v_res_1574_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0));
v___x_1577_ = l_Lean_stringToMessageData(v___x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1602_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1602_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1602_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v_leFn_x3f_1595_; 
v_leFn_x3f_1595_ = lean_ctor_get(v_a_1591_, 20);
lean_inc(v_leFn_x3f_1595_);
lean_dec(v_a_1591_);
if (lean_obj_tag(v_leFn_x3f_1595_) == 1)
{
lean_object* v_val_1596_; lean_object* v___x_1598_; 
v_val_1596_ = lean_ctor_get(v_leFn_x3f_1595_, 0);
lean_inc(v_val_1596_);
lean_dec_ref(v_leFn_x3f_1595_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v_val_1596_);
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_val_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec(v_leFn_x3f_1595_);
lean_del_object(v___x_1593_);
v___x_1600_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1);
v___x_1601_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1600_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
return v___x_1601_;
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
v_a_1603_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1590_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1590_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___boxed(lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec(v___y_1611_);
return v_res_1623_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0));
v___x_1626_ = l_Lean_stringToMessageData(v___x_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1651_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1651_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1651_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v_ltFn_x3f_1644_; 
v_ltFn_x3f_1644_ = lean_ctor_get(v_a_1640_, 21);
lean_inc(v_ltFn_x3f_1644_);
lean_dec(v_a_1640_);
if (lean_obj_tag(v_ltFn_x3f_1644_) == 1)
{
lean_object* v_val_1645_; lean_object* v___x_1647_; 
v_val_1645_ = lean_ctor_get(v_ltFn_x3f_1644_, 0);
lean_inc(v_val_1645_);
lean_dec_ref(v_ltFn_x3f_1644_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v_val_1645_);
v___x_1647_ = v___x_1642_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_val_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec(v_ltFn_x3f_1644_);
lean_del_object(v___x_1642_);
v___x_1649_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1);
v___x_1650_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1649_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
return v___x_1650_;
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
v_a_1652_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1639_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1639_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___boxed(lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec(v___y_1660_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(lean_object* v_p_1673_, uint8_t v_strict_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
if (v_strict_1674_ == 0)
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1689_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref(v___x_1687_);
v___x_1689_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_p_1673_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1691_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref(v___x_1689_);
v___x_1691_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1701_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1694_ = v___x_1691_;
v_isShared_1695_ = v_isSharedCheck_1701_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1691_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1701_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v_ofNatZero_1696_; lean_object* v___x_1697_; lean_object* v___x_1699_; 
v_ofNatZero_1696_ = lean_ctor_get(v_a_1692_, 18);
lean_inc_ref(v_ofNatZero_1696_);
lean_dec(v_a_1692_);
v___x_1697_ = l_Lean_mkAppB(v_a_1688_, v_a_1690_, v_ofNatZero_1696_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v___x_1697_);
v___x_1699_ = v___x_1694_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec(v_a_1690_);
lean_dec(v_a_1688_);
v_a_1702_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1691_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1691_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
else
{
lean_dec(v_a_1688_);
return v___x_1689_;
}
}
else
{
return v___x_1687_;
}
}
else
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1712_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1711_);
lean_dec_ref(v___x_1710_);
v___x_1712_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_p_1673_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1714_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref(v___x_1712_);
v___x_1714_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1724_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1717_ = v___x_1714_;
v_isShared_1718_ = v_isSharedCheck_1724_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1714_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1724_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v_ofNatZero_1719_; lean_object* v___x_1720_; lean_object* v___x_1722_; 
v_ofNatZero_1719_ = lean_ctor_get(v_a_1715_, 18);
lean_inc_ref(v_ofNatZero_1719_);
lean_dec(v_a_1715_);
v___x_1720_ = l_Lean_mkAppB(v_a_1711_, v_a_1713_, v_ofNatZero_1719_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1720_);
v___x_1722_ = v___x_1717_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_dec(v_a_1713_);
lean_dec(v_a_1711_);
v_a_1725_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1714_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1714_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
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
lean_dec(v_a_1711_);
return v___x_1712_;
}
}
else
{
return v___x_1710_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_p_1733_, lean_object* v_strict_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
uint8_t v_strict_boxed_1747_; lean_object* v_res_1748_; 
v_strict_boxed_1747_ = lean_unbox(v_strict_1734_);
v_res_1748_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1733_, v_strict_boxed_1747_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec(v_p_1733_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(lean_object* v_c_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_p_1762_; uint8_t v_strict_1763_; lean_object* v___x_1764_; 
v_p_1762_ = lean_ctor_get(v_c_1749_, 0);
v_strict_1763_ = lean_ctor_get_uint8(v_c_1749_, sizeof(void*)*2);
v___x_1764_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1762_, v_strict_1763_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0___boxed(lean_object* v_c_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v_c_1765_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object* v_a_1779_, lean_object* v_x_1780_, lean_object* v_c_u2081_1781_, lean_object* v_b_1782_, lean_object* v_c_u2082_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v_cls_1796_; lean_object* v___x_1797_; lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1864_; 
v_cls_1796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_1797_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v_cls_1796_, v_a_1793_);
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1864_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1864_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v_p_1802_; lean_object* v_p_1803_; uint8_t v_strict_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v_p_1809_; uint8_t v___x_1816_; 
v_p_1802_ = lean_ctor_get(v_c_u2081_1781_, 0);
v_p_1803_ = lean_ctor_get(v_c_u2082_1783_, 0);
v_strict_1804_ = lean_ctor_get_uint8(v_c_u2082_1783_, sizeof(void*)*2);
v___x_1805_ = lean_nat_to_int(v_a_1779_);
lean_inc(v_p_1803_);
v___x_1806_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1803_, v___x_1805_);
lean_dec(v___x_1805_);
v___x_1807_ = lean_int_neg(v_b_1782_);
lean_inc(v_p_1802_);
v___x_1808_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1802_, v___x_1807_);
lean_dec(v___x_1807_);
v_p_1809_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1806_, v___x_1808_);
v___x_1816_ = lean_unbox(v_a_1798_);
lean_dec(v_a_1798_);
if (v___x_1816_ == 0)
{
goto v___jp_1810_;
}
else
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1780_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1819_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1818_);
lean_dec_ref(v___x_1817_);
v___x_1819_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_c_u2081_1781_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1821_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref(v___x_1819_);
v___x_1821_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_u2082_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref(v___x_1821_);
v___x_1823_ = l_Lean_MessageData_ofExpr(v_a_1818_);
v___x_1824_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1823_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = l_Lean_MessageData_ofExpr(v_a_1820_);
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1825_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
lean_ctor_set(v___x_1828_, 1, v___x_1824_);
v___x_1829_ = l_Lean_MessageData_ofExpr(v_a_1822_);
v___x_1830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1828_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_1796_, v___x_1830_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_dec_ref(v___x_1831_);
goto v___jp_1810_;
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec(v_p_1809_);
lean_del_object(v___x_1800_);
lean_dec_ref(v_c_u2082_1783_);
lean_dec_ref(v_c_u2081_1781_);
lean_dec(v_x_1780_);
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_dec(v_a_1820_);
lean_dec(v_a_1818_);
lean_dec(v_p_1809_);
lean_del_object(v___x_1800_);
lean_dec_ref(v_c_u2082_1783_);
lean_dec_ref(v_c_u2081_1781_);
lean_dec(v_x_1780_);
v_a_1840_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1821_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1821_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_dec(v_a_1818_);
lean_dec(v_p_1809_);
lean_del_object(v___x_1800_);
lean_dec_ref(v_c_u2082_1783_);
lean_dec_ref(v_c_u2081_1781_);
lean_dec(v_x_1780_);
v_a_1848_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1819_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1819_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
lean_dec(v_p_1809_);
lean_del_object(v___x_1800_);
lean_dec_ref(v_c_u2082_1783_);
lean_dec_ref(v_c_u2081_1781_);
lean_dec(v_x_1780_);
v_a_1856_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1817_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1817_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
v___jp_1810_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1811_ = lean_alloc_ctor(13, 3, 0);
lean_ctor_set(v___x_1811_, 0, v_x_1780_);
lean_ctor_set(v___x_1811_, 1, v_c_u2081_1781_);
lean_ctor_set(v___x_1811_, 2, v_c_u2082_1783_);
v___x_1812_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1812_, 0, v_p_1809_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
lean_ctor_set_uint8(v___x_1812_, sizeof(void*)*2, v_strict_1804_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1812_);
v___x_1814_ = v___x_1800_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object** _args){
lean_object* v_a_1865_ = _args[0];
lean_object* v_x_1866_ = _args[1];
lean_object* v_c_u2081_1867_ = _args[2];
lean_object* v_b_1868_ = _args[3];
lean_object* v_c_u2082_1869_ = _args[4];
lean_object* v_a_1870_ = _args[5];
lean_object* v_a_1871_ = _args[6];
lean_object* v_a_1872_ = _args[7];
lean_object* v_a_1873_ = _args[8];
lean_object* v_a_1874_ = _args[9];
lean_object* v_a_1875_ = _args[10];
lean_object* v_a_1876_ = _args[11];
lean_object* v_a_1877_ = _args[12];
lean_object* v_a_1878_ = _args[13];
lean_object* v_a_1879_ = _args[14];
lean_object* v_a_1880_ = _args[15];
lean_object* v_a_1881_ = _args[16];
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1865_, v_x_1866_, v_c_u2081_1867_, v_b_1868_, v_c_u2082_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec(v_a_1878_);
lean_dec_ref(v_a_1877_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
lean_dec(v_a_1874_);
lean_dec_ref(v_a_1873_);
lean_dec(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec(v_a_1870_);
lean_dec(v_b_1868_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1883_, lean_object* v_msg_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1884_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1898_, lean_object* v_msg_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1898_, v_msg_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec(v___y_1900_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(lean_object* v_a_1921_, lean_object* v_x_1922_, lean_object* v_c_u2081_1923_, lean_object* v_as_1924_, size_t v_sz_1925_, size_t v_i_1926_, lean_object* v_b_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
uint8_t v___x_1940_; 
v___x_1940_ = lean_usize_dec_lt(v_i_1926_, v_sz_1925_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; 
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v_c_u2081_1923_);
lean_dec(v_x_1922_);
lean_dec(v_a_1921_);
v___x_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1941_, 0, v_b_1927_);
return v___x_1941_;
}
else
{
lean_object* v_a_1942_; lean_object* v_fst_1943_; lean_object* v_snd_1944_; lean_object* v___x_1945_; 
lean_dec_ref(v_b_1927_);
v_a_1942_ = lean_array_uget_borrowed(v_as_1924_, v_i_1926_);
v_fst_1943_ = lean_ctor_get(v_a_1942_, 0);
v_snd_1944_ = lean_ctor_get(v_a_1942_, 1);
lean_inc(v_snd_1944_);
lean_inc_ref(v_c_u2081_1923_);
lean_inc(v_x_1922_);
lean_inc(v_a_1921_);
v___x_1945_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1921_, v_x_1922_, v_c_u2081_1923_, v_fst_1943_, v_snd_1944_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1947_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref(v___x_1945_);
lean_inc(v___y_1938_);
lean_inc_ref(v___y_1937_);
lean_inc(v___y_1936_);
lean_inc_ref(v___y_1935_);
lean_inc(v___y_1934_);
lean_inc_ref(v___y_1933_);
lean_inc(v___y_1932_);
lean_inc_ref(v___y_1931_);
lean_inc(v___y_1930_);
lean_inc(v___y_1929_);
lean_inc(v___y_1928_);
v___x_1947_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_a_1946_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v___x_1948_; 
lean_dec_ref(v___x_1947_);
v___x_1948_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1962_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1951_ = v___x_1948_;
v_isShared_1952_ = v_isSharedCheck_1962_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1962_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
uint8_t v___x_1953_; 
v___x_1953_ = lean_unbox(v_a_1949_);
lean_dec(v_a_1949_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; size_t v___x_1955_; size_t v___x_1956_; 
lean_del_object(v___x_1951_);
v___x_1954_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v___x_1955_ = ((size_t)1ULL);
v___x_1956_ = lean_usize_add(v_i_1926_, v___x_1955_);
v_i_1926_ = v___x_1956_;
v_b_1927_ = v___x_1954_;
goto _start;
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1960_; 
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v_c_u2081_1923_);
lean_dec(v_x_1922_);
lean_dec(v_a_1921_);
v___x_1958_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1958_);
v___x_1960_ = v___x_1951_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v_c_u2081_1923_);
lean_dec(v_x_1922_);
lean_dec(v_a_1921_);
v_a_1963_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1948_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1948_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v_c_u2081_1923_);
lean_dec(v_x_1922_);
lean_dec(v_a_1921_);
v_a_1971_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1947_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1947_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v_c_u2081_1923_);
lean_dec(v_x_1922_);
lean_dec(v_a_1921_);
v_a_1979_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1945_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1945_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___boxed(lean_object** _args){
lean_object* v_a_1987_ = _args[0];
lean_object* v_x_1988_ = _args[1];
lean_object* v_c_u2081_1989_ = _args[2];
lean_object* v_as_1990_ = _args[3];
lean_object* v_sz_1991_ = _args[4];
lean_object* v_i_1992_ = _args[5];
lean_object* v_b_1993_ = _args[6];
lean_object* v___y_1994_ = _args[7];
lean_object* v___y_1995_ = _args[8];
lean_object* v___y_1996_ = _args[9];
lean_object* v___y_1997_ = _args[10];
lean_object* v___y_1998_ = _args[11];
lean_object* v___y_1999_ = _args[12];
lean_object* v___y_2000_ = _args[13];
lean_object* v___y_2001_ = _args[14];
lean_object* v___y_2002_ = _args[15];
lean_object* v___y_2003_ = _args[16];
lean_object* v___y_2004_ = _args[17];
lean_object* v___y_2005_ = _args[18];
_start:
{
size_t v_sz_boxed_2006_; size_t v_i_boxed_2007_; lean_object* v_res_2008_; 
v_sz_boxed_2006_ = lean_unbox_usize(v_sz_1991_);
lean_dec(v_sz_1991_);
v_i_boxed_2007_ = lean_unbox_usize(v_i_1992_);
lean_dec(v_i_1992_);
v_res_2008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1987_, v_x_1988_, v_c_u2081_1989_, v_as_1990_, v_sz_boxed_2006_, v_i_boxed_2007_, v_b_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec_ref(v_as_1990_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(lean_object* v_a_2009_, lean_object* v_x_2010_, lean_object* v_c_u2081_2011_, lean_object* v_todo_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; size_t v_sz_2027_; size_t v___x_2028_; lean_object* v___x_2029_; 
v___x_2025_ = lean_box(0);
v___x_2026_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_2027_ = lean_array_size(v_todo_2012_);
v___x_2028_ = ((size_t)0ULL);
v___x_2029_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_2009_, v_x_2010_, v_c_u2081_2011_, v_todo_2012_, v_sz_2027_, v___x_2028_, v___x_2026_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2042_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2032_ = v___x_2029_;
v_isShared_2033_ = v_isSharedCheck_2042_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2029_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2042_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v_fst_2034_; 
v_fst_2034_ = lean_ctor_get(v_a_2030_, 0);
lean_inc(v_fst_2034_);
lean_dec(v_a_2030_);
if (lean_obj_tag(v_fst_2034_) == 0)
{
lean_object* v___x_2036_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v___x_2025_);
v___x_2036_ = v___x_2032_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2025_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
else
{
lean_object* v_val_2038_; lean_object* v___x_2040_; 
v_val_2038_ = lean_ctor_get(v_fst_2034_, 0);
lean_inc(v_val_2038_);
lean_dec_ref(v_fst_2034_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v_val_2038_);
v___x_2040_ = v___x_2032_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_val_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
v_a_2043_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2029_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2029_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object* v_a_2051_, lean_object* v_x_2052_, lean_object* v_c_u2081_2053_, lean_object* v_todo_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2051_, v_x_2052_, v_c_u2081_2053_, v_todo_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_);
lean_dec_ref(v_todo_2054_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_2068_, lean_object* v_as_2069_, size_t v_sz_2070_, size_t v_i_2071_, lean_object* v_b_2072_){
_start:
{
uint8_t v___x_2073_; 
v___x_2073_ = lean_usize_dec_lt(v_i_2071_, v_sz_2070_);
if (v___x_2073_ == 0)
{
return v_b_2072_;
}
else
{
lean_object* v_snd_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2107_; 
v_snd_2074_ = lean_ctor_get(v_b_2072_, 1);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_b_2072_);
if (v_isSharedCheck_2107_ == 0)
{
lean_object* v_unused_2108_; 
v_unused_2108_ = lean_ctor_get(v_b_2072_, 0);
lean_dec(v_unused_2108_);
v___x_2076_ = v_b_2072_;
v_isShared_2077_ = v_isSharedCheck_2107_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_snd_2074_);
lean_dec(v_b_2072_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2107_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v_fst_2078_; lean_object* v_snd_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2106_; 
v_fst_2078_ = lean_ctor_get(v_snd_2074_, 0);
v_snd_2079_ = lean_ctor_get(v_snd_2074_, 1);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_snd_2074_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2081_ = v_snd_2074_;
v_isShared_2082_ = v_isSharedCheck_2106_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_snd_2079_);
lean_inc(v_fst_2078_);
lean_dec(v_snd_2074_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2106_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v_a_2083_; lean_object* v_p_2084_; lean_object* v___x_2085_; lean_object* v_a_2087_; lean_object* v_b_2094_; lean_object* v___x_2095_; uint8_t v___x_2096_; 
v_a_2083_ = lean_array_uget_borrowed(v_as_2069_, v_i_2071_);
v_p_2084_ = lean_ctor_get(v_a_2083_, 0);
v___x_2085_ = lean_box(0);
v_b_2094_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2084_, v_x_2068_);
v___x_2095_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2096_ = lean_int_dec_eq(v_b_2094_, v___x_2095_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2098_; 
lean_inc(v_a_2083_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 1, v_a_2083_);
lean_ctor_set(v___x_2076_, 0, v_b_2094_);
v___x_2098_ = v___x_2076_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_b_2094_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_a_2083_);
v___x_2098_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v_todo_2099_; lean_object* v___x_2100_; 
v_todo_2099_ = lean_array_push(v_snd_2079_, v___x_2098_);
v___x_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2100_, 0, v_fst_2078_);
lean_ctor_set(v___x_2100_, 1, v_todo_2099_);
v_a_2087_ = v___x_2100_;
goto v___jp_2086_;
}
}
else
{
lean_object* v_cs_x27_2102_; lean_object* v___x_2104_; 
lean_dec(v_b_2094_);
lean_inc(v_a_2083_);
v_cs_x27_2102_ = l_Lean_PersistentArray_push___redArg(v_fst_2078_, v_a_2083_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 1, v_snd_2079_);
lean_ctor_set(v___x_2076_, 0, v_cs_x27_2102_);
v___x_2104_ = v___x_2076_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_cs_x27_2102_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v_snd_2079_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
v_a_2087_ = v___x_2104_;
goto v___jp_2086_;
}
}
v___jp_2086_:
{
lean_object* v___x_2089_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 1, v_a_2087_);
lean_ctor_set(v___x_2081_, 0, v___x_2085_);
v___x_2089_ = v___x_2081_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2085_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_a_2087_);
v___x_2089_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
size_t v___x_2090_; size_t v___x_2091_; 
v___x_2090_ = ((size_t)1ULL);
v___x_2091_ = lean_usize_add(v_i_2071_, v___x_2090_);
v_i_2071_ = v___x_2091_;
v_b_2072_ = v___x_2089_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_2109_, lean_object* v_as_2110_, lean_object* v_sz_2111_, lean_object* v_i_2112_, lean_object* v_b_2113_){
_start:
{
size_t v_sz_boxed_2114_; size_t v_i_boxed_2115_; lean_object* v_res_2116_; 
v_sz_boxed_2114_ = lean_unbox_usize(v_sz_2111_);
lean_dec(v_sz_2111_);
v_i_boxed_2115_ = lean_unbox_usize(v_i_2112_);
lean_dec(v_i_2112_);
v_res_2116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2109_, v_as_2110_, v_sz_boxed_2114_, v_i_boxed_2115_, v_b_2113_);
lean_dec_ref(v_as_2110_);
lean_dec(v_x_2109_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(lean_object* v_x_2117_, lean_object* v_as_2118_, size_t v_sz_2119_, size_t v_i_2120_, lean_object* v_b_2121_){
_start:
{
uint8_t v___x_2122_; 
v___x_2122_ = lean_usize_dec_lt(v_i_2120_, v_sz_2119_);
if (v___x_2122_ == 0)
{
return v_b_2121_;
}
else
{
lean_object* v_snd_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2156_; 
v_snd_2123_ = lean_ctor_get(v_b_2121_, 1);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_b_2121_);
if (v_isSharedCheck_2156_ == 0)
{
lean_object* v_unused_2157_; 
v_unused_2157_ = lean_ctor_get(v_b_2121_, 0);
lean_dec(v_unused_2157_);
v___x_2125_ = v_b_2121_;
v_isShared_2126_ = v_isSharedCheck_2156_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_snd_2123_);
lean_dec(v_b_2121_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2156_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v_fst_2127_; lean_object* v_snd_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2155_; 
v_fst_2127_ = lean_ctor_get(v_snd_2123_, 0);
v_snd_2128_ = lean_ctor_get(v_snd_2123_, 1);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_snd_2123_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2130_ = v_snd_2123_;
v_isShared_2131_ = v_isSharedCheck_2155_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_snd_2128_);
lean_inc(v_fst_2127_);
lean_dec(v_snd_2123_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2155_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v_a_2132_; lean_object* v_p_2133_; lean_object* v___x_2134_; lean_object* v_a_2136_; lean_object* v_b_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
v_a_2132_ = lean_array_uget_borrowed(v_as_2118_, v_i_2120_);
v_p_2133_ = lean_ctor_get(v_a_2132_, 0);
v___x_2134_ = lean_box(0);
v_b_2143_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2133_, v_x_2117_);
v___x_2144_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2145_ = lean_int_dec_eq(v_b_2143_, v___x_2144_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2147_; 
lean_inc(v_a_2132_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 1, v_a_2132_);
lean_ctor_set(v___x_2125_, 0, v_b_2143_);
v___x_2147_ = v___x_2125_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_b_2143_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v_a_2132_);
v___x_2147_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
lean_object* v_todo_2148_; lean_object* v___x_2149_; 
v_todo_2148_ = lean_array_push(v_snd_2128_, v___x_2147_);
v___x_2149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2149_, 0, v_fst_2127_);
lean_ctor_set(v___x_2149_, 1, v_todo_2148_);
v_a_2136_ = v___x_2149_;
goto v___jp_2135_;
}
}
else
{
lean_object* v_cs_x27_2151_; lean_object* v___x_2153_; 
lean_dec(v_b_2143_);
lean_inc(v_a_2132_);
v_cs_x27_2151_ = l_Lean_PersistentArray_push___redArg(v_fst_2127_, v_a_2132_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 1, v_snd_2128_);
lean_ctor_set(v___x_2125_, 0, v_cs_x27_2151_);
v___x_2153_ = v___x_2125_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_cs_x27_2151_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_snd_2128_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
v_a_2136_ = v___x_2153_;
goto v___jp_2135_;
}
}
v___jp_2135_:
{
lean_object* v___x_2138_; 
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 1, v_a_2136_);
lean_ctor_set(v___x_2130_, 0, v___x_2134_);
v___x_2138_ = v___x_2130_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2134_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_a_2136_);
v___x_2138_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
size_t v___x_2139_; size_t v___x_2140_; lean_object* v___x_2141_; 
v___x_2139_ = ((size_t)1ULL);
v___x_2140_ = lean_usize_add(v_i_2120_, v___x_2139_);
v___x_2141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2117_, v_as_2118_, v_sz_2119_, v___x_2140_, v___x_2138_);
return v___x_2141_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2158_, lean_object* v_as_2159_, lean_object* v_sz_2160_, lean_object* v_i_2161_, lean_object* v_b_2162_){
_start:
{
size_t v_sz_boxed_2163_; size_t v_i_boxed_2164_; lean_object* v_res_2165_; 
v_sz_boxed_2163_ = lean_unbox_usize(v_sz_2160_);
lean_dec(v_sz_2160_);
v_i_boxed_2164_ = lean_unbox_usize(v_i_2161_);
lean_dec(v_i_2161_);
v_res_2165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2158_, v_as_2159_, v_sz_boxed_2163_, v_i_boxed_2164_, v_b_2162_);
lean_dec_ref(v_as_2159_);
lean_dec(v_x_2158_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_2166_, lean_object* v_as_2167_, size_t v_sz_2168_, size_t v_i_2169_, lean_object* v_b_2170_){
_start:
{
uint8_t v___x_2171_; 
v___x_2171_ = lean_usize_dec_lt(v_i_2169_, v_sz_2168_);
if (v___x_2171_ == 0)
{
return v_b_2170_;
}
else
{
lean_object* v_snd_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2205_; 
v_snd_2172_ = lean_ctor_get(v_b_2170_, 1);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_b_2170_);
if (v_isSharedCheck_2205_ == 0)
{
lean_object* v_unused_2206_; 
v_unused_2206_ = lean_ctor_get(v_b_2170_, 0);
lean_dec(v_unused_2206_);
v___x_2174_ = v_b_2170_;
v_isShared_2175_ = v_isSharedCheck_2205_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_snd_2172_);
lean_dec(v_b_2170_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2205_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v_fst_2176_; lean_object* v_snd_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2204_; 
v_fst_2176_ = lean_ctor_get(v_snd_2172_, 0);
v_snd_2177_ = lean_ctor_get(v_snd_2172_, 1);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_snd_2172_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2179_ = v_snd_2172_;
v_isShared_2180_ = v_isSharedCheck_2204_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_snd_2177_);
lean_inc(v_fst_2176_);
lean_dec(v_snd_2172_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2204_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v_a_2181_; lean_object* v_p_2182_; lean_object* v___x_2183_; lean_object* v_a_2185_; lean_object* v_b_2192_; lean_object* v___x_2193_; uint8_t v___x_2194_; 
v_a_2181_ = lean_array_uget_borrowed(v_as_2167_, v_i_2169_);
v_p_2182_ = lean_ctor_get(v_a_2181_, 0);
v___x_2183_ = lean_box(0);
v_b_2192_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2182_, v_x_2166_);
v___x_2193_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2194_ = lean_int_dec_eq(v_b_2192_, v___x_2193_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2196_; 
lean_inc(v_a_2181_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 1, v_a_2181_);
lean_ctor_set(v___x_2174_, 0, v_b_2192_);
v___x_2196_ = v___x_2174_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_b_2192_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_a_2181_);
v___x_2196_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v_todo_2197_; lean_object* v___x_2198_; 
v_todo_2197_ = lean_array_push(v_snd_2177_, v___x_2196_);
v___x_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2198_, 0, v_fst_2176_);
lean_ctor_set(v___x_2198_, 1, v_todo_2197_);
v_a_2185_ = v___x_2198_;
goto v___jp_2184_;
}
}
else
{
lean_object* v_cs_x27_2200_; lean_object* v___x_2202_; 
lean_dec(v_b_2192_);
lean_inc(v_a_2181_);
v_cs_x27_2200_ = l_Lean_PersistentArray_push___redArg(v_fst_2176_, v_a_2181_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 1, v_snd_2177_);
lean_ctor_set(v___x_2174_, 0, v_cs_x27_2200_);
v___x_2202_ = v___x_2174_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_cs_x27_2200_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_snd_2177_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
v_a_2185_ = v___x_2202_;
goto v___jp_2184_;
}
}
v___jp_2184_:
{
lean_object* v___x_2187_; 
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 1, v_a_2185_);
lean_ctor_set(v___x_2179_, 0, v___x_2183_);
v___x_2187_ = v___x_2179_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2183_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_a_2185_);
v___x_2187_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
size_t v___x_2188_; size_t v___x_2189_; 
v___x_2188_ = ((size_t)1ULL);
v___x_2189_ = lean_usize_add(v_i_2169_, v___x_2188_);
v_i_2169_ = v___x_2189_;
v_b_2170_ = v___x_2187_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_2207_, lean_object* v_as_2208_, lean_object* v_sz_2209_, lean_object* v_i_2210_, lean_object* v_b_2211_){
_start:
{
size_t v_sz_boxed_2212_; size_t v_i_boxed_2213_; lean_object* v_res_2214_; 
v_sz_boxed_2212_ = lean_unbox_usize(v_sz_2209_);
lean_dec(v_sz_2209_);
v_i_boxed_2213_ = lean_unbox_usize(v_i_2210_);
lean_dec(v_i_2210_);
v_res_2214_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2207_, v_as_2208_, v_sz_boxed_2212_, v_i_boxed_2213_, v_b_2211_);
lean_dec_ref(v_as_2208_);
lean_dec(v_x_2207_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2215_, lean_object* v_as_2216_, size_t v_sz_2217_, size_t v_i_2218_, lean_object* v_b_2219_){
_start:
{
uint8_t v___x_2220_; 
v___x_2220_ = lean_usize_dec_lt(v_i_2218_, v_sz_2217_);
if (v___x_2220_ == 0)
{
return v_b_2219_;
}
else
{
lean_object* v_snd_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2254_; 
v_snd_2221_ = lean_ctor_get(v_b_2219_, 1);
v_isSharedCheck_2254_ = !lean_is_exclusive(v_b_2219_);
if (v_isSharedCheck_2254_ == 0)
{
lean_object* v_unused_2255_; 
v_unused_2255_ = lean_ctor_get(v_b_2219_, 0);
lean_dec(v_unused_2255_);
v___x_2223_ = v_b_2219_;
v_isShared_2224_ = v_isSharedCheck_2254_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_snd_2221_);
lean_dec(v_b_2219_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2254_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v_fst_2225_; lean_object* v_snd_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2253_; 
v_fst_2225_ = lean_ctor_get(v_snd_2221_, 0);
v_snd_2226_ = lean_ctor_get(v_snd_2221_, 1);
v_isSharedCheck_2253_ = !lean_is_exclusive(v_snd_2221_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2228_ = v_snd_2221_;
v_isShared_2229_ = v_isSharedCheck_2253_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_snd_2226_);
lean_inc(v_fst_2225_);
lean_dec(v_snd_2221_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2253_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v_a_2230_; lean_object* v_p_2231_; lean_object* v___x_2232_; lean_object* v_a_2234_; lean_object* v_b_2241_; lean_object* v___x_2242_; uint8_t v___x_2243_; 
v_a_2230_ = lean_array_uget_borrowed(v_as_2216_, v_i_2218_);
v_p_2231_ = lean_ctor_get(v_a_2230_, 0);
v___x_2232_ = lean_box(0);
v_b_2241_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2231_, v_x_2215_);
v___x_2242_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2243_ = lean_int_dec_eq(v_b_2241_, v___x_2242_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2245_; 
lean_inc(v_a_2230_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 1, v_a_2230_);
lean_ctor_set(v___x_2223_, 0, v_b_2241_);
v___x_2245_ = v___x_2223_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_b_2241_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_a_2230_);
v___x_2245_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
lean_object* v_todo_2246_; lean_object* v___x_2247_; 
v_todo_2246_ = lean_array_push(v_snd_2226_, v___x_2245_);
v___x_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2247_, 0, v_fst_2225_);
lean_ctor_set(v___x_2247_, 1, v_todo_2246_);
v_a_2234_ = v___x_2247_;
goto v___jp_2233_;
}
}
else
{
lean_object* v_cs_x27_2249_; lean_object* v___x_2251_; 
lean_dec(v_b_2241_);
lean_inc(v_a_2230_);
v_cs_x27_2249_ = l_Lean_PersistentArray_push___redArg(v_fst_2225_, v_a_2230_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 1, v_snd_2226_);
lean_ctor_set(v___x_2223_, 0, v_cs_x27_2249_);
v___x_2251_ = v___x_2223_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_cs_x27_2249_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_snd_2226_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
v_a_2234_ = v___x_2251_;
goto v___jp_2233_;
}
}
v___jp_2233_:
{
lean_object* v___x_2236_; 
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 1, v_a_2234_);
lean_ctor_set(v___x_2228_, 0, v___x_2232_);
v___x_2236_ = v___x_2228_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_a_2234_);
v___x_2236_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
size_t v___x_2237_; size_t v___x_2238_; lean_object* v___x_2239_; 
v___x_2237_ = ((size_t)1ULL);
v___x_2238_ = lean_usize_add(v_i_2218_, v___x_2237_);
v___x_2239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2215_, v_as_2216_, v_sz_2217_, v___x_2238_, v___x_2236_);
return v___x_2239_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_2256_, lean_object* v_as_2257_, lean_object* v_sz_2258_, lean_object* v_i_2259_, lean_object* v_b_2260_){
_start:
{
size_t v_sz_boxed_2261_; size_t v_i_boxed_2262_; lean_object* v_res_2263_; 
v_sz_boxed_2261_ = lean_unbox_usize(v_sz_2258_);
lean_dec(v_sz_2258_);
v_i_boxed_2262_ = lean_unbox_usize(v_i_2259_);
lean_dec(v_i_2259_);
v_res_2263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2256_, v_as_2257_, v_sz_boxed_2261_, v_i_boxed_2262_, v_b_2260_);
lean_dec_ref(v_as_2257_);
lean_dec(v_x_2256_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(lean_object* v_x_2264_, lean_object* v_inh_2265_, lean_object* v_n_2266_, lean_object* v_b_2267_){
_start:
{
if (lean_obj_tag(v_n_2266_) == 0)
{
lean_object* v_cs_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2283_; 
v_cs_2268_ = lean_ctor_get(v_n_2266_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v_n_2266_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2270_ = v_n_2266_;
v_isShared_2271_ = v_isSharedCheck_2283_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_cs_2268_);
lean_dec(v_n_2266_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2283_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; size_t v_sz_2274_; size_t v___x_2275_; lean_object* v___x_2276_; lean_object* v_fst_2277_; 
v___x_2272_ = lean_box(0);
v___x_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set(v___x_2273_, 1, v_b_2267_);
v_sz_2274_ = lean_array_size(v_cs_2268_);
v___x_2275_ = ((size_t)0ULL);
v___x_2276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_x_2264_, v_inh_2265_, v_cs_2268_, v_sz_2274_, v___x_2275_, v___x_2273_);
lean_dec_ref(v_cs_2268_);
v_fst_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_fst_2277_);
if (lean_obj_tag(v_fst_2277_) == 0)
{
lean_object* v_snd_2278_; lean_object* v___x_2280_; 
v_snd_2278_ = lean_ctor_get(v___x_2276_, 1);
lean_inc(v_snd_2278_);
lean_dec_ref(v___x_2276_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set_tag(v___x_2270_, 1);
lean_ctor_set(v___x_2270_, 0, v_snd_2278_);
v___x_2280_ = v___x_2270_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_snd_2278_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
else
{
lean_object* v_val_2282_; 
lean_dec_ref(v___x_2276_);
lean_del_object(v___x_2270_);
v_val_2282_ = lean_ctor_get(v_fst_2277_, 0);
lean_inc(v_val_2282_);
lean_dec_ref(v_fst_2277_);
return v_val_2282_;
}
}
}
else
{
lean_object* v_vs_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2299_; 
v_vs_2284_ = lean_ctor_get(v_n_2266_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v_n_2266_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2286_ = v_n_2266_;
v_isShared_2287_ = v_isSharedCheck_2299_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_vs_2284_);
lean_dec(v_n_2266_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2299_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; size_t v_sz_2290_; size_t v___x_2291_; lean_object* v___x_2292_; lean_object* v_fst_2293_; 
v___x_2288_ = lean_box(0);
v___x_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
lean_ctor_set(v___x_2289_, 1, v_b_2267_);
v_sz_2290_ = lean_array_size(v_vs_2284_);
v___x_2291_ = ((size_t)0ULL);
v___x_2292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2264_, v_vs_2284_, v_sz_2290_, v___x_2291_, v___x_2289_);
lean_dec_ref(v_vs_2284_);
v_fst_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_fst_2293_);
if (lean_obj_tag(v_fst_2293_) == 0)
{
lean_object* v_snd_2294_; lean_object* v___x_2296_; 
v_snd_2294_ = lean_ctor_get(v___x_2292_, 1);
lean_inc(v_snd_2294_);
lean_dec_ref(v___x_2292_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v_snd_2294_);
v___x_2296_ = v___x_2286_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_snd_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
else
{
lean_object* v_val_2298_; 
lean_dec_ref(v___x_2292_);
lean_del_object(v___x_2286_);
v_val_2298_ = lean_ctor_get(v_fst_2293_, 0);
lean_inc(v_val_2298_);
lean_dec_ref(v_fst_2293_);
return v_val_2298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2300_, lean_object* v_inh_2301_, lean_object* v_as_2302_, size_t v_sz_2303_, size_t v_i_2304_, lean_object* v_b_2305_){
_start:
{
uint8_t v___x_2306_; 
v___x_2306_ = lean_usize_dec_lt(v_i_2304_, v_sz_2303_);
if (v___x_2306_ == 0)
{
return v_b_2305_;
}
else
{
lean_object* v_snd_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2325_; 
v_snd_2307_ = lean_ctor_get(v_b_2305_, 1);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_b_2305_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; 
v_unused_2326_ = lean_ctor_get(v_b_2305_, 0);
lean_dec(v_unused_2326_);
v___x_2309_ = v_b_2305_;
v_isShared_2310_ = v_isSharedCheck_2325_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_snd_2307_);
lean_dec(v_b_2305_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2325_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v_a_2311_; lean_object* v___x_2312_; 
v_a_2311_ = lean_array_uget_borrowed(v_as_2302_, v_i_2304_);
lean_inc(v_snd_2307_);
lean_inc(v_a_2311_);
v___x_2312_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_x_2300_, v_inh_2301_, v_a_2311_, v_snd_2307_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v___x_2313_; lean_object* v___x_2315_; 
v___x_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v___x_2313_);
v___x_2315_ = v___x_2309_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2313_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_snd_2307_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2318_; lean_object* v___x_2320_; 
lean_dec(v_snd_2307_);
v_a_2317_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2317_);
lean_dec_ref(v___x_2312_);
v___x_2318_ = lean_box(0);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 1, v_a_2317_);
lean_ctor_set(v___x_2309_, 0, v___x_2318_);
v___x_2320_ = v___x_2309_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_a_2317_);
v___x_2320_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
size_t v___x_2321_; size_t v___x_2322_; 
v___x_2321_ = ((size_t)1ULL);
v___x_2322_ = lean_usize_add(v_i_2304_, v___x_2321_);
v_i_2304_ = v___x_2322_;
v_b_2305_ = v___x_2320_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_x_2327_, lean_object* v_inh_2328_, lean_object* v_as_2329_, lean_object* v_sz_2330_, lean_object* v_i_2331_, lean_object* v_b_2332_){
_start:
{
size_t v_sz_boxed_2333_; size_t v_i_boxed_2334_; lean_object* v_res_2335_; 
v_sz_boxed_2333_ = lean_unbox_usize(v_sz_2330_);
lean_dec(v_sz_2330_);
v_i_boxed_2334_ = lean_unbox_usize(v_i_2331_);
lean_dec(v_i_2331_);
v_res_2335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_x_2327_, v_inh_2328_, v_as_2329_, v_sz_boxed_2333_, v_i_boxed_2334_, v_b_2332_);
lean_dec_ref(v_as_2329_);
lean_dec_ref(v_inh_2328_);
lean_dec(v_x_2327_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object* v_x_2336_, lean_object* v_inh_2337_, lean_object* v_n_2338_, lean_object* v_b_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_x_2336_, v_inh_2337_, v_n_2338_, v_b_2339_);
lean_dec_ref(v_inh_2337_);
lean_dec(v_x_2336_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(lean_object* v_x_2341_, lean_object* v_t_2342_, lean_object* v_init_2343_){
_start:
{
lean_object* v_root_2344_; lean_object* v_tail_2345_; lean_object* v___x_2346_; 
v_root_2344_ = lean_ctor_get(v_t_2342_, 0);
lean_inc_ref(v_root_2344_);
v_tail_2345_ = lean_ctor_get(v_t_2342_, 1);
lean_inc_ref(v_tail_2345_);
lean_dec_ref(v_t_2342_);
lean_inc_ref(v_init_2343_);
v___x_2346_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_x_2341_, v_init_2343_, v_root_2344_, v_init_2343_);
lean_dec_ref(v_init_2343_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; 
lean_dec_ref(v_tail_2345_);
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref(v___x_2346_);
return v_a_2347_;
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; size_t v_sz_2351_; size_t v___x_2352_; lean_object* v___x_2353_; lean_object* v_fst_2354_; 
v_a_2348_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2348_);
lean_dec_ref(v___x_2346_);
v___x_2349_ = lean_box(0);
v___x_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
lean_ctor_set(v___x_2350_, 1, v_a_2348_);
v_sz_2351_ = lean_array_size(v_tail_2345_);
v___x_2352_ = ((size_t)0ULL);
v___x_2353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2341_, v_tail_2345_, v_sz_2351_, v___x_2352_, v___x_2350_);
lean_dec_ref(v_tail_2345_);
v_fst_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_fst_2354_);
if (lean_obj_tag(v_fst_2354_) == 0)
{
lean_object* v_snd_2355_; 
v_snd_2355_ = lean_ctor_get(v___x_2353_, 1);
lean_inc(v_snd_2355_);
lean_dec_ref(v___x_2353_);
return v_snd_2355_;
}
else
{
lean_object* v_val_2356_; 
lean_dec_ref(v___x_2353_);
v_val_2356_ = lean_ctor_get(v_fst_2354_, 0);
lean_inc(v_val_2356_);
lean_dec_ref(v_fst_2354_);
return v_val_2356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0___boxed(lean_object* v_x_2357_, lean_object* v_t_2358_, lean_object* v_init_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2357_, v_t_2358_, v_init_2359_);
lean_dec(v_x_2357_);
return v_res_2360_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2361_ = lean_unsigned_to_nat(32u);
v___x_2362_ = lean_mk_empty_array_with_capacity(v___x_2361_);
v___x_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
return v___x_2363_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1(void){
_start:
{
size_t v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v_cs_x27_2369_; 
v___x_2364_ = ((size_t)5ULL);
v___x_2365_ = lean_unsigned_to_nat(0u);
v___x_2366_ = lean_unsigned_to_nat(32u);
v___x_2367_ = lean_mk_empty_array_with_capacity(v___x_2366_);
v___x_2368_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0);
v_cs_x27_2369_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_2369_, 0, v___x_2368_);
lean_ctor_set(v_cs_x27_2369_, 1, v___x_2367_);
lean_ctor_set(v_cs_x27_2369_, 2, v___x_2365_);
lean_ctor_set(v_cs_x27_2369_, 3, v___x_2365_);
lean_ctor_set_usize(v_cs_x27_2369_, 4, v___x_2364_);
return v_cs_x27_2369_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_2372_; lean_object* v_cs_x27_2373_; lean_object* v___x_2374_; 
v_todo_2372_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2));
v_cs_x27_2373_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1);
v___x_2374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2374_, 0, v_cs_x27_2373_);
lean_ctor_set(v___x_2374_, 1, v_todo_2372_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(lean_object* v_x_2375_, lean_object* v_cs_2376_){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v_fst_2379_; lean_object* v_snd_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
v___x_2377_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3);
v___x_2378_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2375_, v_cs_2376_, v___x_2377_);
v_fst_2379_ = lean_ctor_get(v___x_2378_, 0);
v_snd_2380_ = lean_ctor_get(v___x_2378_, 1);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2378_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_snd_2380_);
lean_inc(v_fst_2379_);
lean_dec(v___x_2378_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_fst_2379_);
lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_snd_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___boxed(lean_object* v_x_2388_, lean_object* v_cs_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2388_, v_cs_2389_);
lean_dec(v_x_2388_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object* v_x_2391_, lean_object* v_cs_2392_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2391_, v_cs_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___boxed(lean_object* v_x_2394_, lean_object* v_cs_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(v_x_2394_, v_cs_2395_);
lean_dec(v_x_2394_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(lean_object* v_a_2397_, lean_object* v_y_2398_, lean_object* v_fst_2399_, lean_object* v_s_2400_){
_start:
{
lean_object* v_structs_2401_; lean_object* v_typeIdOf_2402_; lean_object* v_exprToStructId_2403_; lean_object* v_exprToStructIdEntries_2404_; lean_object* v_forbiddenNatModules_2405_; lean_object* v_natStructs_2406_; lean_object* v_natTypeIdOf_2407_; lean_object* v_exprToNatStructId_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; 
v_structs_2401_ = lean_ctor_get(v_s_2400_, 0);
v_typeIdOf_2402_ = lean_ctor_get(v_s_2400_, 1);
v_exprToStructId_2403_ = lean_ctor_get(v_s_2400_, 2);
v_exprToStructIdEntries_2404_ = lean_ctor_get(v_s_2400_, 3);
v_forbiddenNatModules_2405_ = lean_ctor_get(v_s_2400_, 4);
v_natStructs_2406_ = lean_ctor_get(v_s_2400_, 5);
v_natTypeIdOf_2407_ = lean_ctor_get(v_s_2400_, 6);
v_exprToNatStructId_2408_ = lean_ctor_get(v_s_2400_, 7);
v___x_2409_ = lean_array_get_size(v_structs_2401_);
v___x_2410_ = lean_nat_dec_lt(v_a_2397_, v___x_2409_);
if (v___x_2410_ == 0)
{
lean_dec_ref(v_fst_2399_);
return v_s_2400_;
}
else
{
lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2472_; 
lean_inc_ref(v_exprToNatStructId_2408_);
lean_inc_ref(v_natTypeIdOf_2407_);
lean_inc_ref(v_natStructs_2406_);
lean_inc_ref(v_forbiddenNatModules_2405_);
lean_inc_ref(v_exprToStructIdEntries_2404_);
lean_inc_ref(v_exprToStructId_2403_);
lean_inc_ref(v_typeIdOf_2402_);
lean_inc_ref(v_structs_2401_);
v_isSharedCheck_2472_ = !lean_is_exclusive(v_s_2400_);
if (v_isSharedCheck_2472_ == 0)
{
lean_object* v_unused_2473_; lean_object* v_unused_2474_; lean_object* v_unused_2475_; lean_object* v_unused_2476_; lean_object* v_unused_2477_; lean_object* v_unused_2478_; lean_object* v_unused_2479_; lean_object* v_unused_2480_; 
v_unused_2473_ = lean_ctor_get(v_s_2400_, 7);
lean_dec(v_unused_2473_);
v_unused_2474_ = lean_ctor_get(v_s_2400_, 6);
lean_dec(v_unused_2474_);
v_unused_2475_ = lean_ctor_get(v_s_2400_, 5);
lean_dec(v_unused_2475_);
v_unused_2476_ = lean_ctor_get(v_s_2400_, 4);
lean_dec(v_unused_2476_);
v_unused_2477_ = lean_ctor_get(v_s_2400_, 3);
lean_dec(v_unused_2477_);
v_unused_2478_ = lean_ctor_get(v_s_2400_, 2);
lean_dec(v_unused_2478_);
v_unused_2479_ = lean_ctor_get(v_s_2400_, 1);
lean_dec(v_unused_2479_);
v_unused_2480_ = lean_ctor_get(v_s_2400_, 0);
lean_dec(v_unused_2480_);
v___x_2412_ = v_s_2400_;
v_isShared_2413_ = v_isSharedCheck_2472_;
goto v_resetjp_2411_;
}
else
{
lean_dec(v_s_2400_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2472_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v_v_2414_; lean_object* v_id_2415_; lean_object* v_ringId_x3f_2416_; lean_object* v_type_2417_; lean_object* v_u_2418_; lean_object* v_intModuleInst_2419_; lean_object* v_leInst_x3f_2420_; lean_object* v_ltInst_x3f_2421_; lean_object* v_lawfulOrderLTInst_x3f_2422_; lean_object* v_isPreorderInst_x3f_2423_; lean_object* v_orderedAddInst_x3f_2424_; lean_object* v_isLinearInst_x3f_2425_; lean_object* v_noNatDivInst_x3f_2426_; lean_object* v_ringInst_x3f_2427_; lean_object* v_commRingInst_x3f_2428_; lean_object* v_orderedRingInst_x3f_2429_; lean_object* v_fieldInst_x3f_2430_; lean_object* v_charInst_x3f_2431_; lean_object* v_zero_2432_; lean_object* v_ofNatZero_2433_; lean_object* v_one_x3f_2434_; lean_object* v_leFn_x3f_2435_; lean_object* v_ltFn_x3f_2436_; lean_object* v_addFn_2437_; lean_object* v_zsmulFn_2438_; lean_object* v_nsmulFn_2439_; lean_object* v_zsmulFn_x3f_2440_; lean_object* v_nsmulFn_x3f_2441_; lean_object* v_homomulFn_x3f_2442_; lean_object* v_subFn_2443_; lean_object* v_negFn_2444_; lean_object* v_vars_2445_; lean_object* v_varMap_2446_; lean_object* v_lowers_2447_; lean_object* v_uppers_2448_; lean_object* v_diseqs_2449_; lean_object* v_assignment_2450_; uint8_t v_caseSplits_2451_; lean_object* v_conflict_x3f_2452_; lean_object* v_diseqSplits_2453_; lean_object* v_elimEqs_2454_; lean_object* v_elimStack_2455_; lean_object* v_occurs_2456_; lean_object* v_ignored_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2471_; 
v_v_2414_ = lean_array_fget(v_structs_2401_, v_a_2397_);
v_id_2415_ = lean_ctor_get(v_v_2414_, 0);
v_ringId_x3f_2416_ = lean_ctor_get(v_v_2414_, 1);
v_type_2417_ = lean_ctor_get(v_v_2414_, 2);
v_u_2418_ = lean_ctor_get(v_v_2414_, 3);
v_intModuleInst_2419_ = lean_ctor_get(v_v_2414_, 4);
v_leInst_x3f_2420_ = lean_ctor_get(v_v_2414_, 5);
v_ltInst_x3f_2421_ = lean_ctor_get(v_v_2414_, 6);
v_lawfulOrderLTInst_x3f_2422_ = lean_ctor_get(v_v_2414_, 7);
v_isPreorderInst_x3f_2423_ = lean_ctor_get(v_v_2414_, 8);
v_orderedAddInst_x3f_2424_ = lean_ctor_get(v_v_2414_, 9);
v_isLinearInst_x3f_2425_ = lean_ctor_get(v_v_2414_, 10);
v_noNatDivInst_x3f_2426_ = lean_ctor_get(v_v_2414_, 11);
v_ringInst_x3f_2427_ = lean_ctor_get(v_v_2414_, 12);
v_commRingInst_x3f_2428_ = lean_ctor_get(v_v_2414_, 13);
v_orderedRingInst_x3f_2429_ = lean_ctor_get(v_v_2414_, 14);
v_fieldInst_x3f_2430_ = lean_ctor_get(v_v_2414_, 15);
v_charInst_x3f_2431_ = lean_ctor_get(v_v_2414_, 16);
v_zero_2432_ = lean_ctor_get(v_v_2414_, 17);
v_ofNatZero_2433_ = lean_ctor_get(v_v_2414_, 18);
v_one_x3f_2434_ = lean_ctor_get(v_v_2414_, 19);
v_leFn_x3f_2435_ = lean_ctor_get(v_v_2414_, 20);
v_ltFn_x3f_2436_ = lean_ctor_get(v_v_2414_, 21);
v_addFn_2437_ = lean_ctor_get(v_v_2414_, 22);
v_zsmulFn_2438_ = lean_ctor_get(v_v_2414_, 23);
v_nsmulFn_2439_ = lean_ctor_get(v_v_2414_, 24);
v_zsmulFn_x3f_2440_ = lean_ctor_get(v_v_2414_, 25);
v_nsmulFn_x3f_2441_ = lean_ctor_get(v_v_2414_, 26);
v_homomulFn_x3f_2442_ = lean_ctor_get(v_v_2414_, 27);
v_subFn_2443_ = lean_ctor_get(v_v_2414_, 28);
v_negFn_2444_ = lean_ctor_get(v_v_2414_, 29);
v_vars_2445_ = lean_ctor_get(v_v_2414_, 30);
v_varMap_2446_ = lean_ctor_get(v_v_2414_, 31);
v_lowers_2447_ = lean_ctor_get(v_v_2414_, 32);
v_uppers_2448_ = lean_ctor_get(v_v_2414_, 33);
v_diseqs_2449_ = lean_ctor_get(v_v_2414_, 34);
v_assignment_2450_ = lean_ctor_get(v_v_2414_, 35);
v_caseSplits_2451_ = lean_ctor_get_uint8(v_v_2414_, sizeof(void*)*42);
v_conflict_x3f_2452_ = lean_ctor_get(v_v_2414_, 36);
v_diseqSplits_2453_ = lean_ctor_get(v_v_2414_, 37);
v_elimEqs_2454_ = lean_ctor_get(v_v_2414_, 38);
v_elimStack_2455_ = lean_ctor_get(v_v_2414_, 39);
v_occurs_2456_ = lean_ctor_get(v_v_2414_, 40);
v_ignored_2457_ = lean_ctor_get(v_v_2414_, 41);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_v_2414_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2459_ = v_v_2414_;
v_isShared_2460_ = v_isSharedCheck_2471_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_ignored_2457_);
lean_inc(v_occurs_2456_);
lean_inc(v_elimStack_2455_);
lean_inc(v_elimEqs_2454_);
lean_inc(v_diseqSplits_2453_);
lean_inc(v_conflict_x3f_2452_);
lean_inc(v_assignment_2450_);
lean_inc(v_diseqs_2449_);
lean_inc(v_uppers_2448_);
lean_inc(v_lowers_2447_);
lean_inc(v_varMap_2446_);
lean_inc(v_vars_2445_);
lean_inc(v_negFn_2444_);
lean_inc(v_subFn_2443_);
lean_inc(v_homomulFn_x3f_2442_);
lean_inc(v_nsmulFn_x3f_2441_);
lean_inc(v_zsmulFn_x3f_2440_);
lean_inc(v_nsmulFn_2439_);
lean_inc(v_zsmulFn_2438_);
lean_inc(v_addFn_2437_);
lean_inc(v_ltFn_x3f_2436_);
lean_inc(v_leFn_x3f_2435_);
lean_inc(v_one_x3f_2434_);
lean_inc(v_ofNatZero_2433_);
lean_inc(v_zero_2432_);
lean_inc(v_charInst_x3f_2431_);
lean_inc(v_fieldInst_x3f_2430_);
lean_inc(v_orderedRingInst_x3f_2429_);
lean_inc(v_commRingInst_x3f_2428_);
lean_inc(v_ringInst_x3f_2427_);
lean_inc(v_noNatDivInst_x3f_2426_);
lean_inc(v_isLinearInst_x3f_2425_);
lean_inc(v_orderedAddInst_x3f_2424_);
lean_inc(v_isPreorderInst_x3f_2423_);
lean_inc(v_lawfulOrderLTInst_x3f_2422_);
lean_inc(v_ltInst_x3f_2421_);
lean_inc(v_leInst_x3f_2420_);
lean_inc(v_intModuleInst_2419_);
lean_inc(v_u_2418_);
lean_inc(v_type_2417_);
lean_inc(v_ringId_x3f_2416_);
lean_inc(v_id_2415_);
lean_dec(v_v_2414_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2471_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2461_; lean_object* v_xs_x27_2462_; lean_object* v___x_2463_; lean_object* v___x_2465_; 
v___x_2461_ = lean_box(0);
v_xs_x27_2462_ = lean_array_fset(v_structs_2401_, v_a_2397_, v___x_2461_);
v___x_2463_ = l_Lean_PersistentArray_set___redArg(v_lowers_2447_, v_y_2398_, v_fst_2399_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 32, v___x_2463_);
v___x_2465_ = v___x_2459_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_id_2415_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v_ringId_x3f_2416_);
lean_ctor_set(v_reuseFailAlloc_2470_, 2, v_type_2417_);
lean_ctor_set(v_reuseFailAlloc_2470_, 3, v_u_2418_);
lean_ctor_set(v_reuseFailAlloc_2470_, 4, v_intModuleInst_2419_);
lean_ctor_set(v_reuseFailAlloc_2470_, 5, v_leInst_x3f_2420_);
lean_ctor_set(v_reuseFailAlloc_2470_, 6, v_ltInst_x3f_2421_);
lean_ctor_set(v_reuseFailAlloc_2470_, 7, v_lawfulOrderLTInst_x3f_2422_);
lean_ctor_set(v_reuseFailAlloc_2470_, 8, v_isPreorderInst_x3f_2423_);
lean_ctor_set(v_reuseFailAlloc_2470_, 9, v_orderedAddInst_x3f_2424_);
lean_ctor_set(v_reuseFailAlloc_2470_, 10, v_isLinearInst_x3f_2425_);
lean_ctor_set(v_reuseFailAlloc_2470_, 11, v_noNatDivInst_x3f_2426_);
lean_ctor_set(v_reuseFailAlloc_2470_, 12, v_ringInst_x3f_2427_);
lean_ctor_set(v_reuseFailAlloc_2470_, 13, v_commRingInst_x3f_2428_);
lean_ctor_set(v_reuseFailAlloc_2470_, 14, v_orderedRingInst_x3f_2429_);
lean_ctor_set(v_reuseFailAlloc_2470_, 15, v_fieldInst_x3f_2430_);
lean_ctor_set(v_reuseFailAlloc_2470_, 16, v_charInst_x3f_2431_);
lean_ctor_set(v_reuseFailAlloc_2470_, 17, v_zero_2432_);
lean_ctor_set(v_reuseFailAlloc_2470_, 18, v_ofNatZero_2433_);
lean_ctor_set(v_reuseFailAlloc_2470_, 19, v_one_x3f_2434_);
lean_ctor_set(v_reuseFailAlloc_2470_, 20, v_leFn_x3f_2435_);
lean_ctor_set(v_reuseFailAlloc_2470_, 21, v_ltFn_x3f_2436_);
lean_ctor_set(v_reuseFailAlloc_2470_, 22, v_addFn_2437_);
lean_ctor_set(v_reuseFailAlloc_2470_, 23, v_zsmulFn_2438_);
lean_ctor_set(v_reuseFailAlloc_2470_, 24, v_nsmulFn_2439_);
lean_ctor_set(v_reuseFailAlloc_2470_, 25, v_zsmulFn_x3f_2440_);
lean_ctor_set(v_reuseFailAlloc_2470_, 26, v_nsmulFn_x3f_2441_);
lean_ctor_set(v_reuseFailAlloc_2470_, 27, v_homomulFn_x3f_2442_);
lean_ctor_set(v_reuseFailAlloc_2470_, 28, v_subFn_2443_);
lean_ctor_set(v_reuseFailAlloc_2470_, 29, v_negFn_2444_);
lean_ctor_set(v_reuseFailAlloc_2470_, 30, v_vars_2445_);
lean_ctor_set(v_reuseFailAlloc_2470_, 31, v_varMap_2446_);
lean_ctor_set(v_reuseFailAlloc_2470_, 32, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2470_, 33, v_uppers_2448_);
lean_ctor_set(v_reuseFailAlloc_2470_, 34, v_diseqs_2449_);
lean_ctor_set(v_reuseFailAlloc_2470_, 35, v_assignment_2450_);
lean_ctor_set(v_reuseFailAlloc_2470_, 36, v_conflict_x3f_2452_);
lean_ctor_set(v_reuseFailAlloc_2470_, 37, v_diseqSplits_2453_);
lean_ctor_set(v_reuseFailAlloc_2470_, 38, v_elimEqs_2454_);
lean_ctor_set(v_reuseFailAlloc_2470_, 39, v_elimStack_2455_);
lean_ctor_set(v_reuseFailAlloc_2470_, 40, v_occurs_2456_);
lean_ctor_set(v_reuseFailAlloc_2470_, 41, v_ignored_2457_);
lean_ctor_set_uint8(v_reuseFailAlloc_2470_, sizeof(void*)*42, v_caseSplits_2451_);
v___x_2465_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
lean_object* v___x_2466_; lean_object* v___x_2468_; 
v___x_2466_ = lean_array_fset(v_xs_x27_2462_, v_a_2397_, v___x_2465_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2466_);
v___x_2468_ = v___x_2412_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v_typeIdOf_2402_);
lean_ctor_set(v_reuseFailAlloc_2469_, 2, v_exprToStructId_2403_);
lean_ctor_set(v_reuseFailAlloc_2469_, 3, v_exprToStructIdEntries_2404_);
lean_ctor_set(v_reuseFailAlloc_2469_, 4, v_forbiddenNatModules_2405_);
lean_ctor_set(v_reuseFailAlloc_2469_, 5, v_natStructs_2406_);
lean_ctor_set(v_reuseFailAlloc_2469_, 6, v_natTypeIdOf_2407_);
lean_ctor_set(v_reuseFailAlloc_2469_, 7, v_exprToNatStructId_2408_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed(lean_object* v_a_2481_, lean_object* v_y_2482_, lean_object* v_fst_2483_, lean_object* v_s_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(v_a_2481_, v_y_2482_, v_fst_2483_, v_s_2484_);
lean_dec(v_y_2482_);
lean_dec(v_a_2481_);
return v_res_2485_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0(void){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object* v_a_2487_, lean_object* v_x_2488_, lean_object* v_c_2489_, lean_object* v_y_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2538_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2506_ = v___x_2503_;
v_isShared_2507_ = v_isSharedCheck_2538_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2503_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2538_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
uint8_t v___x_2508_; 
v___x_2508_ = lean_unbox(v_a_2504_);
lean_dec(v_a_2504_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; 
lean_del_object(v___x_2506_);
v___x_2509_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v___y_2512_; lean_object* v_lowers_2520_; lean_object* v_size_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_a_2510_);
lean_dec_ref(v___x_2509_);
v_lowers_2520_ = lean_ctor_get(v_a_2510_, 32);
lean_inc_ref(v_lowers_2520_);
lean_dec(v_a_2510_);
v_size_2521_ = lean_ctor_get(v_lowers_2520_, 2);
v___x_2522_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2523_ = lean_nat_dec_lt(v_y_2490_, v_size_2521_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; 
lean_dec_ref(v_lowers_2520_);
v___x_2524_ = l_outOfBounds___redArg(v___x_2522_);
v___y_2512_ = v___x_2524_;
goto v___jp_2511_;
}
else
{
lean_object* v___x_2525_; 
v___x_2525_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2522_, v_lowers_2520_, v_y_2490_);
v___y_2512_ = v___x_2525_;
goto v___jp_2511_;
}
v___jp_2511_:
{
lean_object* v___x_2513_; lean_object* v_fst_2514_; lean_object* v_snd_2515_; lean_object* v___f_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2513_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2488_, v___y_2512_);
v_fst_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_fst_2514_);
v_snd_2515_ = lean_ctor_get(v___x_2513_, 1);
lean_inc(v_snd_2515_);
lean_dec_ref(v___x_2513_);
lean_inc(v_a_2491_);
v___f_2516_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2516_, 0, v_a_2491_);
lean_closure_set(v___f_2516_, 1, v_y_2490_);
lean_closure_set(v___f_2516_, 2, v_fst_2514_);
v___x_2517_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2518_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2517_, v___f_2516_, v_a_2492_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v___x_2519_; 
lean_dec_ref(v___x_2518_);
v___x_2519_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2487_, v_x_2488_, v_c_2489_, v_snd_2515_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
lean_dec(v_snd_2515_);
return v___x_2519_;
}
else
{
lean_dec(v_snd_2515_);
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec_ref(v_c_2489_);
lean_dec(v_x_2488_);
lean_dec(v_a_2487_);
return v___x_2518_;
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec(v_y_2490_);
lean_dec_ref(v_c_2489_);
lean_dec(v_x_2488_);
lean_dec(v_a_2487_);
v_a_2526_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2509_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2509_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
else
{
lean_object* v___x_2534_; lean_object* v___x_2536_; 
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec(v_y_2490_);
lean_dec_ref(v_c_2489_);
lean_dec(v_x_2488_);
lean_dec(v_a_2487_);
v___x_2534_ = lean_box(0);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v___x_2534_);
v___x_2536_ = v___x_2506_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2534_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec(v_y_2490_);
lean_dec_ref(v_c_2489_);
lean_dec(v_x_2488_);
lean_dec(v_a_2487_);
v_a_2539_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2503_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2503_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object* v_a_2547_, lean_object* v_x_2548_, lean_object* v_c_2549_, lean_object* v_y_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_2547_, v_x_2548_, v_c_2549_, v_y_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(lean_object* v_a_2564_, lean_object* v_y_2565_, lean_object* v_fst_2566_, lean_object* v_s_2567_){
_start:
{
lean_object* v_structs_2568_; lean_object* v_typeIdOf_2569_; lean_object* v_exprToStructId_2570_; lean_object* v_exprToStructIdEntries_2571_; lean_object* v_forbiddenNatModules_2572_; lean_object* v_natStructs_2573_; lean_object* v_natTypeIdOf_2574_; lean_object* v_exprToNatStructId_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; 
v_structs_2568_ = lean_ctor_get(v_s_2567_, 0);
v_typeIdOf_2569_ = lean_ctor_get(v_s_2567_, 1);
v_exprToStructId_2570_ = lean_ctor_get(v_s_2567_, 2);
v_exprToStructIdEntries_2571_ = lean_ctor_get(v_s_2567_, 3);
v_forbiddenNatModules_2572_ = lean_ctor_get(v_s_2567_, 4);
v_natStructs_2573_ = lean_ctor_get(v_s_2567_, 5);
v_natTypeIdOf_2574_ = lean_ctor_get(v_s_2567_, 6);
v_exprToNatStructId_2575_ = lean_ctor_get(v_s_2567_, 7);
v___x_2576_ = lean_array_get_size(v_structs_2568_);
v___x_2577_ = lean_nat_dec_lt(v_a_2564_, v___x_2576_);
if (v___x_2577_ == 0)
{
lean_dec_ref(v_fst_2566_);
return v_s_2567_;
}
else
{
lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2639_; 
lean_inc_ref(v_exprToNatStructId_2575_);
lean_inc_ref(v_natTypeIdOf_2574_);
lean_inc_ref(v_natStructs_2573_);
lean_inc_ref(v_forbiddenNatModules_2572_);
lean_inc_ref(v_exprToStructIdEntries_2571_);
lean_inc_ref(v_exprToStructId_2570_);
lean_inc_ref(v_typeIdOf_2569_);
lean_inc_ref(v_structs_2568_);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_s_2567_);
if (v_isSharedCheck_2639_ == 0)
{
lean_object* v_unused_2640_; lean_object* v_unused_2641_; lean_object* v_unused_2642_; lean_object* v_unused_2643_; lean_object* v_unused_2644_; lean_object* v_unused_2645_; lean_object* v_unused_2646_; lean_object* v_unused_2647_; 
v_unused_2640_ = lean_ctor_get(v_s_2567_, 7);
lean_dec(v_unused_2640_);
v_unused_2641_ = lean_ctor_get(v_s_2567_, 6);
lean_dec(v_unused_2641_);
v_unused_2642_ = lean_ctor_get(v_s_2567_, 5);
lean_dec(v_unused_2642_);
v_unused_2643_ = lean_ctor_get(v_s_2567_, 4);
lean_dec(v_unused_2643_);
v_unused_2644_ = lean_ctor_get(v_s_2567_, 3);
lean_dec(v_unused_2644_);
v_unused_2645_ = lean_ctor_get(v_s_2567_, 2);
lean_dec(v_unused_2645_);
v_unused_2646_ = lean_ctor_get(v_s_2567_, 1);
lean_dec(v_unused_2646_);
v_unused_2647_ = lean_ctor_get(v_s_2567_, 0);
lean_dec(v_unused_2647_);
v___x_2579_ = v_s_2567_;
v_isShared_2580_ = v_isSharedCheck_2639_;
goto v_resetjp_2578_;
}
else
{
lean_dec(v_s_2567_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2639_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v_v_2581_; lean_object* v_id_2582_; lean_object* v_ringId_x3f_2583_; lean_object* v_type_2584_; lean_object* v_u_2585_; lean_object* v_intModuleInst_2586_; lean_object* v_leInst_x3f_2587_; lean_object* v_ltInst_x3f_2588_; lean_object* v_lawfulOrderLTInst_x3f_2589_; lean_object* v_isPreorderInst_x3f_2590_; lean_object* v_orderedAddInst_x3f_2591_; lean_object* v_isLinearInst_x3f_2592_; lean_object* v_noNatDivInst_x3f_2593_; lean_object* v_ringInst_x3f_2594_; lean_object* v_commRingInst_x3f_2595_; lean_object* v_orderedRingInst_x3f_2596_; lean_object* v_fieldInst_x3f_2597_; lean_object* v_charInst_x3f_2598_; lean_object* v_zero_2599_; lean_object* v_ofNatZero_2600_; lean_object* v_one_x3f_2601_; lean_object* v_leFn_x3f_2602_; lean_object* v_ltFn_x3f_2603_; lean_object* v_addFn_2604_; lean_object* v_zsmulFn_2605_; lean_object* v_nsmulFn_2606_; lean_object* v_zsmulFn_x3f_2607_; lean_object* v_nsmulFn_x3f_2608_; lean_object* v_homomulFn_x3f_2609_; lean_object* v_subFn_2610_; lean_object* v_negFn_2611_; lean_object* v_vars_2612_; lean_object* v_varMap_2613_; lean_object* v_lowers_2614_; lean_object* v_uppers_2615_; lean_object* v_diseqs_2616_; lean_object* v_assignment_2617_; uint8_t v_caseSplits_2618_; lean_object* v_conflict_x3f_2619_; lean_object* v_diseqSplits_2620_; lean_object* v_elimEqs_2621_; lean_object* v_elimStack_2622_; lean_object* v_occurs_2623_; lean_object* v_ignored_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2638_; 
v_v_2581_ = lean_array_fget(v_structs_2568_, v_a_2564_);
v_id_2582_ = lean_ctor_get(v_v_2581_, 0);
v_ringId_x3f_2583_ = lean_ctor_get(v_v_2581_, 1);
v_type_2584_ = lean_ctor_get(v_v_2581_, 2);
v_u_2585_ = lean_ctor_get(v_v_2581_, 3);
v_intModuleInst_2586_ = lean_ctor_get(v_v_2581_, 4);
v_leInst_x3f_2587_ = lean_ctor_get(v_v_2581_, 5);
v_ltInst_x3f_2588_ = lean_ctor_get(v_v_2581_, 6);
v_lawfulOrderLTInst_x3f_2589_ = lean_ctor_get(v_v_2581_, 7);
v_isPreorderInst_x3f_2590_ = lean_ctor_get(v_v_2581_, 8);
v_orderedAddInst_x3f_2591_ = lean_ctor_get(v_v_2581_, 9);
v_isLinearInst_x3f_2592_ = lean_ctor_get(v_v_2581_, 10);
v_noNatDivInst_x3f_2593_ = lean_ctor_get(v_v_2581_, 11);
v_ringInst_x3f_2594_ = lean_ctor_get(v_v_2581_, 12);
v_commRingInst_x3f_2595_ = lean_ctor_get(v_v_2581_, 13);
v_orderedRingInst_x3f_2596_ = lean_ctor_get(v_v_2581_, 14);
v_fieldInst_x3f_2597_ = lean_ctor_get(v_v_2581_, 15);
v_charInst_x3f_2598_ = lean_ctor_get(v_v_2581_, 16);
v_zero_2599_ = lean_ctor_get(v_v_2581_, 17);
v_ofNatZero_2600_ = lean_ctor_get(v_v_2581_, 18);
v_one_x3f_2601_ = lean_ctor_get(v_v_2581_, 19);
v_leFn_x3f_2602_ = lean_ctor_get(v_v_2581_, 20);
v_ltFn_x3f_2603_ = lean_ctor_get(v_v_2581_, 21);
v_addFn_2604_ = lean_ctor_get(v_v_2581_, 22);
v_zsmulFn_2605_ = lean_ctor_get(v_v_2581_, 23);
v_nsmulFn_2606_ = lean_ctor_get(v_v_2581_, 24);
v_zsmulFn_x3f_2607_ = lean_ctor_get(v_v_2581_, 25);
v_nsmulFn_x3f_2608_ = lean_ctor_get(v_v_2581_, 26);
v_homomulFn_x3f_2609_ = lean_ctor_get(v_v_2581_, 27);
v_subFn_2610_ = lean_ctor_get(v_v_2581_, 28);
v_negFn_2611_ = lean_ctor_get(v_v_2581_, 29);
v_vars_2612_ = lean_ctor_get(v_v_2581_, 30);
v_varMap_2613_ = lean_ctor_get(v_v_2581_, 31);
v_lowers_2614_ = lean_ctor_get(v_v_2581_, 32);
v_uppers_2615_ = lean_ctor_get(v_v_2581_, 33);
v_diseqs_2616_ = lean_ctor_get(v_v_2581_, 34);
v_assignment_2617_ = lean_ctor_get(v_v_2581_, 35);
v_caseSplits_2618_ = lean_ctor_get_uint8(v_v_2581_, sizeof(void*)*42);
v_conflict_x3f_2619_ = lean_ctor_get(v_v_2581_, 36);
v_diseqSplits_2620_ = lean_ctor_get(v_v_2581_, 37);
v_elimEqs_2621_ = lean_ctor_get(v_v_2581_, 38);
v_elimStack_2622_ = lean_ctor_get(v_v_2581_, 39);
v_occurs_2623_ = lean_ctor_get(v_v_2581_, 40);
v_ignored_2624_ = lean_ctor_get(v_v_2581_, 41);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_v_2581_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2626_ = v_v_2581_;
v_isShared_2627_ = v_isSharedCheck_2638_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_ignored_2624_);
lean_inc(v_occurs_2623_);
lean_inc(v_elimStack_2622_);
lean_inc(v_elimEqs_2621_);
lean_inc(v_diseqSplits_2620_);
lean_inc(v_conflict_x3f_2619_);
lean_inc(v_assignment_2617_);
lean_inc(v_diseqs_2616_);
lean_inc(v_uppers_2615_);
lean_inc(v_lowers_2614_);
lean_inc(v_varMap_2613_);
lean_inc(v_vars_2612_);
lean_inc(v_negFn_2611_);
lean_inc(v_subFn_2610_);
lean_inc(v_homomulFn_x3f_2609_);
lean_inc(v_nsmulFn_x3f_2608_);
lean_inc(v_zsmulFn_x3f_2607_);
lean_inc(v_nsmulFn_2606_);
lean_inc(v_zsmulFn_2605_);
lean_inc(v_addFn_2604_);
lean_inc(v_ltFn_x3f_2603_);
lean_inc(v_leFn_x3f_2602_);
lean_inc(v_one_x3f_2601_);
lean_inc(v_ofNatZero_2600_);
lean_inc(v_zero_2599_);
lean_inc(v_charInst_x3f_2598_);
lean_inc(v_fieldInst_x3f_2597_);
lean_inc(v_orderedRingInst_x3f_2596_);
lean_inc(v_commRingInst_x3f_2595_);
lean_inc(v_ringInst_x3f_2594_);
lean_inc(v_noNatDivInst_x3f_2593_);
lean_inc(v_isLinearInst_x3f_2592_);
lean_inc(v_orderedAddInst_x3f_2591_);
lean_inc(v_isPreorderInst_x3f_2590_);
lean_inc(v_lawfulOrderLTInst_x3f_2589_);
lean_inc(v_ltInst_x3f_2588_);
lean_inc(v_leInst_x3f_2587_);
lean_inc(v_intModuleInst_2586_);
lean_inc(v_u_2585_);
lean_inc(v_type_2584_);
lean_inc(v_ringId_x3f_2583_);
lean_inc(v_id_2582_);
lean_dec(v_v_2581_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2638_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2628_; lean_object* v_xs_x27_2629_; lean_object* v___x_2630_; lean_object* v___x_2632_; 
v___x_2628_ = lean_box(0);
v_xs_x27_2629_ = lean_array_fset(v_structs_2568_, v_a_2564_, v___x_2628_);
v___x_2630_ = l_Lean_PersistentArray_set___redArg(v_uppers_2615_, v_y_2565_, v_fst_2566_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 33, v___x_2630_);
v___x_2632_ = v___x_2626_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_id_2582_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_ringId_x3f_2583_);
lean_ctor_set(v_reuseFailAlloc_2637_, 2, v_type_2584_);
lean_ctor_set(v_reuseFailAlloc_2637_, 3, v_u_2585_);
lean_ctor_set(v_reuseFailAlloc_2637_, 4, v_intModuleInst_2586_);
lean_ctor_set(v_reuseFailAlloc_2637_, 5, v_leInst_x3f_2587_);
lean_ctor_set(v_reuseFailAlloc_2637_, 6, v_ltInst_x3f_2588_);
lean_ctor_set(v_reuseFailAlloc_2637_, 7, v_lawfulOrderLTInst_x3f_2589_);
lean_ctor_set(v_reuseFailAlloc_2637_, 8, v_isPreorderInst_x3f_2590_);
lean_ctor_set(v_reuseFailAlloc_2637_, 9, v_orderedAddInst_x3f_2591_);
lean_ctor_set(v_reuseFailAlloc_2637_, 10, v_isLinearInst_x3f_2592_);
lean_ctor_set(v_reuseFailAlloc_2637_, 11, v_noNatDivInst_x3f_2593_);
lean_ctor_set(v_reuseFailAlloc_2637_, 12, v_ringInst_x3f_2594_);
lean_ctor_set(v_reuseFailAlloc_2637_, 13, v_commRingInst_x3f_2595_);
lean_ctor_set(v_reuseFailAlloc_2637_, 14, v_orderedRingInst_x3f_2596_);
lean_ctor_set(v_reuseFailAlloc_2637_, 15, v_fieldInst_x3f_2597_);
lean_ctor_set(v_reuseFailAlloc_2637_, 16, v_charInst_x3f_2598_);
lean_ctor_set(v_reuseFailAlloc_2637_, 17, v_zero_2599_);
lean_ctor_set(v_reuseFailAlloc_2637_, 18, v_ofNatZero_2600_);
lean_ctor_set(v_reuseFailAlloc_2637_, 19, v_one_x3f_2601_);
lean_ctor_set(v_reuseFailAlloc_2637_, 20, v_leFn_x3f_2602_);
lean_ctor_set(v_reuseFailAlloc_2637_, 21, v_ltFn_x3f_2603_);
lean_ctor_set(v_reuseFailAlloc_2637_, 22, v_addFn_2604_);
lean_ctor_set(v_reuseFailAlloc_2637_, 23, v_zsmulFn_2605_);
lean_ctor_set(v_reuseFailAlloc_2637_, 24, v_nsmulFn_2606_);
lean_ctor_set(v_reuseFailAlloc_2637_, 25, v_zsmulFn_x3f_2607_);
lean_ctor_set(v_reuseFailAlloc_2637_, 26, v_nsmulFn_x3f_2608_);
lean_ctor_set(v_reuseFailAlloc_2637_, 27, v_homomulFn_x3f_2609_);
lean_ctor_set(v_reuseFailAlloc_2637_, 28, v_subFn_2610_);
lean_ctor_set(v_reuseFailAlloc_2637_, 29, v_negFn_2611_);
lean_ctor_set(v_reuseFailAlloc_2637_, 30, v_vars_2612_);
lean_ctor_set(v_reuseFailAlloc_2637_, 31, v_varMap_2613_);
lean_ctor_set(v_reuseFailAlloc_2637_, 32, v_lowers_2614_);
lean_ctor_set(v_reuseFailAlloc_2637_, 33, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2637_, 34, v_diseqs_2616_);
lean_ctor_set(v_reuseFailAlloc_2637_, 35, v_assignment_2617_);
lean_ctor_set(v_reuseFailAlloc_2637_, 36, v_conflict_x3f_2619_);
lean_ctor_set(v_reuseFailAlloc_2637_, 37, v_diseqSplits_2620_);
lean_ctor_set(v_reuseFailAlloc_2637_, 38, v_elimEqs_2621_);
lean_ctor_set(v_reuseFailAlloc_2637_, 39, v_elimStack_2622_);
lean_ctor_set(v_reuseFailAlloc_2637_, 40, v_occurs_2623_);
lean_ctor_set(v_reuseFailAlloc_2637_, 41, v_ignored_2624_);
lean_ctor_set_uint8(v_reuseFailAlloc_2637_, sizeof(void*)*42, v_caseSplits_2618_);
v___x_2632_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
lean_object* v___x_2633_; lean_object* v___x_2635_; 
v___x_2633_ = lean_array_fset(v_xs_x27_2629_, v_a_2564_, v___x_2632_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___x_2633_);
v___x_2635_ = v___x_2579_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_typeIdOf_2569_);
lean_ctor_set(v_reuseFailAlloc_2636_, 2, v_exprToStructId_2570_);
lean_ctor_set(v_reuseFailAlloc_2636_, 3, v_exprToStructIdEntries_2571_);
lean_ctor_set(v_reuseFailAlloc_2636_, 4, v_forbiddenNatModules_2572_);
lean_ctor_set(v_reuseFailAlloc_2636_, 5, v_natStructs_2573_);
lean_ctor_set(v_reuseFailAlloc_2636_, 6, v_natTypeIdOf_2574_);
lean_ctor_set(v_reuseFailAlloc_2636_, 7, v_exprToNatStructId_2575_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed(lean_object* v_a_2648_, lean_object* v_y_2649_, lean_object* v_fst_2650_, lean_object* v_s_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(v_a_2648_, v_y_2649_, v_fst_2650_, v_s_2651_);
lean_dec(v_y_2649_);
lean_dec(v_a_2648_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object* v_a_2653_, lean_object* v_x_2654_, lean_object* v_c_2655_, lean_object* v_y_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2704_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2672_ = v___x_2669_;
v_isShared_2673_ = v_isSharedCheck_2704_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2669_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2704_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
uint8_t v___x_2674_; 
v___x_2674_ = lean_unbox(v_a_2670_);
lean_dec(v_a_2670_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2675_; 
lean_del_object(v___x_2672_);
v___x_2675_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___y_2678_; lean_object* v_uppers_2686_; lean_object* v_size_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref(v___x_2675_);
v_uppers_2686_ = lean_ctor_get(v_a_2676_, 33);
lean_inc_ref(v_uppers_2686_);
lean_dec(v_a_2676_);
v_size_2687_ = lean_ctor_get(v_uppers_2686_, 2);
v___x_2688_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2689_ = lean_nat_dec_lt(v_y_2656_, v_size_2687_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; 
lean_dec_ref(v_uppers_2686_);
v___x_2690_ = l_outOfBounds___redArg(v___x_2688_);
v___y_2678_ = v___x_2690_;
goto v___jp_2677_;
}
else
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2688_, v_uppers_2686_, v_y_2656_);
v___y_2678_ = v___x_2691_;
goto v___jp_2677_;
}
v___jp_2677_:
{
lean_object* v___x_2679_; lean_object* v_fst_2680_; lean_object* v_snd_2681_; lean_object* v___f_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2679_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2654_, v___y_2678_);
v_fst_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_fst_2680_);
v_snd_2681_ = lean_ctor_get(v___x_2679_, 1);
lean_inc(v_snd_2681_);
lean_dec_ref(v___x_2679_);
lean_inc(v_a_2657_);
v___f_2682_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2682_, 0, v_a_2657_);
lean_closure_set(v___f_2682_, 1, v_y_2656_);
lean_closure_set(v___f_2682_, 2, v_fst_2680_);
v___x_2683_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2684_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2683_, v___f_2682_, v_a_2658_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v___x_2685_; 
lean_dec_ref(v___x_2684_);
v___x_2685_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2653_, v_x_2654_, v_c_2655_, v_snd_2681_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
lean_dec(v_snd_2681_);
return v___x_2685_;
}
else
{
lean_dec(v_snd_2681_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec_ref(v_c_2655_);
lean_dec(v_x_2654_);
lean_dec(v_a_2653_);
return v___x_2684_;
}
}
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec(v_y_2656_);
lean_dec_ref(v_c_2655_);
lean_dec(v_x_2654_);
lean_dec(v_a_2653_);
v_a_2692_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2675_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2675_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
else
{
lean_object* v___x_2700_; lean_object* v___x_2702_; 
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec(v_y_2656_);
lean_dec_ref(v_c_2655_);
lean_dec(v_x_2654_);
lean_dec(v_a_2653_);
v___x_2700_ = lean_box(0);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 0, v___x_2700_);
v___x_2702_ = v___x_2672_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec(v_y_2656_);
lean_dec_ref(v_c_2655_);
lean_dec(v_x_2654_);
lean_dec(v_a_2653_);
v_a_2705_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2669_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2669_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object* v_a_2713_, lean_object* v_x_2714_, lean_object* v_c_2715_, lean_object* v_y_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_2713_, v_x_2714_, v_c_2715_, v_y_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(lean_object* v___y_2730_, lean_object* v_a_2731_, lean_object* v_s_2732_){
_start:
{
lean_object* v_structs_2733_; lean_object* v_typeIdOf_2734_; lean_object* v_exprToStructId_2735_; lean_object* v_exprToStructIdEntries_2736_; lean_object* v_forbiddenNatModules_2737_; lean_object* v_natStructs_2738_; lean_object* v_natTypeIdOf_2739_; lean_object* v_exprToNatStructId_2740_; lean_object* v___x_2741_; uint8_t v___x_2742_; 
v_structs_2733_ = lean_ctor_get(v_s_2732_, 0);
v_typeIdOf_2734_ = lean_ctor_get(v_s_2732_, 1);
v_exprToStructId_2735_ = lean_ctor_get(v_s_2732_, 2);
v_exprToStructIdEntries_2736_ = lean_ctor_get(v_s_2732_, 3);
v_forbiddenNatModules_2737_ = lean_ctor_get(v_s_2732_, 4);
v_natStructs_2738_ = lean_ctor_get(v_s_2732_, 5);
v_natTypeIdOf_2739_ = lean_ctor_get(v_s_2732_, 6);
v_exprToNatStructId_2740_ = lean_ctor_get(v_s_2732_, 7);
v___x_2741_ = lean_array_get_size(v_structs_2733_);
v___x_2742_ = lean_nat_dec_lt(v___y_2730_, v___x_2741_);
if (v___x_2742_ == 0)
{
lean_dec_ref(v_a_2731_);
return v_s_2732_;
}
else
{
lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2804_; 
lean_inc_ref(v_exprToNatStructId_2740_);
lean_inc_ref(v_natTypeIdOf_2739_);
lean_inc_ref(v_natStructs_2738_);
lean_inc_ref(v_forbiddenNatModules_2737_);
lean_inc_ref(v_exprToStructIdEntries_2736_);
lean_inc_ref(v_exprToStructId_2735_);
lean_inc_ref(v_typeIdOf_2734_);
lean_inc_ref(v_structs_2733_);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_s_2732_);
if (v_isSharedCheck_2804_ == 0)
{
lean_object* v_unused_2805_; lean_object* v_unused_2806_; lean_object* v_unused_2807_; lean_object* v_unused_2808_; lean_object* v_unused_2809_; lean_object* v_unused_2810_; lean_object* v_unused_2811_; lean_object* v_unused_2812_; 
v_unused_2805_ = lean_ctor_get(v_s_2732_, 7);
lean_dec(v_unused_2805_);
v_unused_2806_ = lean_ctor_get(v_s_2732_, 6);
lean_dec(v_unused_2806_);
v_unused_2807_ = lean_ctor_get(v_s_2732_, 5);
lean_dec(v_unused_2807_);
v_unused_2808_ = lean_ctor_get(v_s_2732_, 4);
lean_dec(v_unused_2808_);
v_unused_2809_ = lean_ctor_get(v_s_2732_, 3);
lean_dec(v_unused_2809_);
v_unused_2810_ = lean_ctor_get(v_s_2732_, 2);
lean_dec(v_unused_2810_);
v_unused_2811_ = lean_ctor_get(v_s_2732_, 1);
lean_dec(v_unused_2811_);
v_unused_2812_ = lean_ctor_get(v_s_2732_, 0);
lean_dec(v_unused_2812_);
v___x_2744_ = v_s_2732_;
v_isShared_2745_ = v_isSharedCheck_2804_;
goto v_resetjp_2743_;
}
else
{
lean_dec(v_s_2732_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2804_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v_v_2746_; lean_object* v_id_2747_; lean_object* v_ringId_x3f_2748_; lean_object* v_type_2749_; lean_object* v_u_2750_; lean_object* v_intModuleInst_2751_; lean_object* v_leInst_x3f_2752_; lean_object* v_ltInst_x3f_2753_; lean_object* v_lawfulOrderLTInst_x3f_2754_; lean_object* v_isPreorderInst_x3f_2755_; lean_object* v_orderedAddInst_x3f_2756_; lean_object* v_isLinearInst_x3f_2757_; lean_object* v_noNatDivInst_x3f_2758_; lean_object* v_ringInst_x3f_2759_; lean_object* v_commRingInst_x3f_2760_; lean_object* v_orderedRingInst_x3f_2761_; lean_object* v_fieldInst_x3f_2762_; lean_object* v_charInst_x3f_2763_; lean_object* v_zero_2764_; lean_object* v_ofNatZero_2765_; lean_object* v_one_x3f_2766_; lean_object* v_leFn_x3f_2767_; lean_object* v_ltFn_x3f_2768_; lean_object* v_addFn_2769_; lean_object* v_zsmulFn_2770_; lean_object* v_nsmulFn_2771_; lean_object* v_zsmulFn_x3f_2772_; lean_object* v_nsmulFn_x3f_2773_; lean_object* v_homomulFn_x3f_2774_; lean_object* v_subFn_2775_; lean_object* v_negFn_2776_; lean_object* v_vars_2777_; lean_object* v_varMap_2778_; lean_object* v_lowers_2779_; lean_object* v_uppers_2780_; lean_object* v_diseqs_2781_; lean_object* v_assignment_2782_; uint8_t v_caseSplits_2783_; lean_object* v_conflict_x3f_2784_; lean_object* v_diseqSplits_2785_; lean_object* v_elimEqs_2786_; lean_object* v_elimStack_2787_; lean_object* v_occurs_2788_; lean_object* v_ignored_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2803_; 
v_v_2746_ = lean_array_fget(v_structs_2733_, v___y_2730_);
v_id_2747_ = lean_ctor_get(v_v_2746_, 0);
v_ringId_x3f_2748_ = lean_ctor_get(v_v_2746_, 1);
v_type_2749_ = lean_ctor_get(v_v_2746_, 2);
v_u_2750_ = lean_ctor_get(v_v_2746_, 3);
v_intModuleInst_2751_ = lean_ctor_get(v_v_2746_, 4);
v_leInst_x3f_2752_ = lean_ctor_get(v_v_2746_, 5);
v_ltInst_x3f_2753_ = lean_ctor_get(v_v_2746_, 6);
v_lawfulOrderLTInst_x3f_2754_ = lean_ctor_get(v_v_2746_, 7);
v_isPreorderInst_x3f_2755_ = lean_ctor_get(v_v_2746_, 8);
v_orderedAddInst_x3f_2756_ = lean_ctor_get(v_v_2746_, 9);
v_isLinearInst_x3f_2757_ = lean_ctor_get(v_v_2746_, 10);
v_noNatDivInst_x3f_2758_ = lean_ctor_get(v_v_2746_, 11);
v_ringInst_x3f_2759_ = lean_ctor_get(v_v_2746_, 12);
v_commRingInst_x3f_2760_ = lean_ctor_get(v_v_2746_, 13);
v_orderedRingInst_x3f_2761_ = lean_ctor_get(v_v_2746_, 14);
v_fieldInst_x3f_2762_ = lean_ctor_get(v_v_2746_, 15);
v_charInst_x3f_2763_ = lean_ctor_get(v_v_2746_, 16);
v_zero_2764_ = lean_ctor_get(v_v_2746_, 17);
v_ofNatZero_2765_ = lean_ctor_get(v_v_2746_, 18);
v_one_x3f_2766_ = lean_ctor_get(v_v_2746_, 19);
v_leFn_x3f_2767_ = lean_ctor_get(v_v_2746_, 20);
v_ltFn_x3f_2768_ = lean_ctor_get(v_v_2746_, 21);
v_addFn_2769_ = lean_ctor_get(v_v_2746_, 22);
v_zsmulFn_2770_ = lean_ctor_get(v_v_2746_, 23);
v_nsmulFn_2771_ = lean_ctor_get(v_v_2746_, 24);
v_zsmulFn_x3f_2772_ = lean_ctor_get(v_v_2746_, 25);
v_nsmulFn_x3f_2773_ = lean_ctor_get(v_v_2746_, 26);
v_homomulFn_x3f_2774_ = lean_ctor_get(v_v_2746_, 27);
v_subFn_2775_ = lean_ctor_get(v_v_2746_, 28);
v_negFn_2776_ = lean_ctor_get(v_v_2746_, 29);
v_vars_2777_ = lean_ctor_get(v_v_2746_, 30);
v_varMap_2778_ = lean_ctor_get(v_v_2746_, 31);
v_lowers_2779_ = lean_ctor_get(v_v_2746_, 32);
v_uppers_2780_ = lean_ctor_get(v_v_2746_, 33);
v_diseqs_2781_ = lean_ctor_get(v_v_2746_, 34);
v_assignment_2782_ = lean_ctor_get(v_v_2746_, 35);
v_caseSplits_2783_ = lean_ctor_get_uint8(v_v_2746_, sizeof(void*)*42);
v_conflict_x3f_2784_ = lean_ctor_get(v_v_2746_, 36);
v_diseqSplits_2785_ = lean_ctor_get(v_v_2746_, 37);
v_elimEqs_2786_ = lean_ctor_get(v_v_2746_, 38);
v_elimStack_2787_ = lean_ctor_get(v_v_2746_, 39);
v_occurs_2788_ = lean_ctor_get(v_v_2746_, 40);
v_ignored_2789_ = lean_ctor_get(v_v_2746_, 41);
v_isSharedCheck_2803_ = !lean_is_exclusive(v_v_2746_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2791_ = v_v_2746_;
v_isShared_2792_ = v_isSharedCheck_2803_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_ignored_2789_);
lean_inc(v_occurs_2788_);
lean_inc(v_elimStack_2787_);
lean_inc(v_elimEqs_2786_);
lean_inc(v_diseqSplits_2785_);
lean_inc(v_conflict_x3f_2784_);
lean_inc(v_assignment_2782_);
lean_inc(v_diseqs_2781_);
lean_inc(v_uppers_2780_);
lean_inc(v_lowers_2779_);
lean_inc(v_varMap_2778_);
lean_inc(v_vars_2777_);
lean_inc(v_negFn_2776_);
lean_inc(v_subFn_2775_);
lean_inc(v_homomulFn_x3f_2774_);
lean_inc(v_nsmulFn_x3f_2773_);
lean_inc(v_zsmulFn_x3f_2772_);
lean_inc(v_nsmulFn_2771_);
lean_inc(v_zsmulFn_2770_);
lean_inc(v_addFn_2769_);
lean_inc(v_ltFn_x3f_2768_);
lean_inc(v_leFn_x3f_2767_);
lean_inc(v_one_x3f_2766_);
lean_inc(v_ofNatZero_2765_);
lean_inc(v_zero_2764_);
lean_inc(v_charInst_x3f_2763_);
lean_inc(v_fieldInst_x3f_2762_);
lean_inc(v_orderedRingInst_x3f_2761_);
lean_inc(v_commRingInst_x3f_2760_);
lean_inc(v_ringInst_x3f_2759_);
lean_inc(v_noNatDivInst_x3f_2758_);
lean_inc(v_isLinearInst_x3f_2757_);
lean_inc(v_orderedAddInst_x3f_2756_);
lean_inc(v_isPreorderInst_x3f_2755_);
lean_inc(v_lawfulOrderLTInst_x3f_2754_);
lean_inc(v_ltInst_x3f_2753_);
lean_inc(v_leInst_x3f_2752_);
lean_inc(v_intModuleInst_2751_);
lean_inc(v_u_2750_);
lean_inc(v_type_2749_);
lean_inc(v_ringId_x3f_2748_);
lean_inc(v_id_2747_);
lean_dec(v_v_2746_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2803_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2793_; lean_object* v_xs_x27_2794_; lean_object* v___x_2795_; lean_object* v___x_2797_; 
v___x_2793_ = lean_box(0);
v_xs_x27_2794_ = lean_array_fset(v_structs_2733_, v___y_2730_, v___x_2793_);
v___x_2795_ = l_Lean_PersistentArray_push___redArg(v_ignored_2789_, v_a_2731_);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 41, v___x_2795_);
v___x_2797_ = v___x_2791_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_id_2747_);
lean_ctor_set(v_reuseFailAlloc_2802_, 1, v_ringId_x3f_2748_);
lean_ctor_set(v_reuseFailAlloc_2802_, 2, v_type_2749_);
lean_ctor_set(v_reuseFailAlloc_2802_, 3, v_u_2750_);
lean_ctor_set(v_reuseFailAlloc_2802_, 4, v_intModuleInst_2751_);
lean_ctor_set(v_reuseFailAlloc_2802_, 5, v_leInst_x3f_2752_);
lean_ctor_set(v_reuseFailAlloc_2802_, 6, v_ltInst_x3f_2753_);
lean_ctor_set(v_reuseFailAlloc_2802_, 7, v_lawfulOrderLTInst_x3f_2754_);
lean_ctor_set(v_reuseFailAlloc_2802_, 8, v_isPreorderInst_x3f_2755_);
lean_ctor_set(v_reuseFailAlloc_2802_, 9, v_orderedAddInst_x3f_2756_);
lean_ctor_set(v_reuseFailAlloc_2802_, 10, v_isLinearInst_x3f_2757_);
lean_ctor_set(v_reuseFailAlloc_2802_, 11, v_noNatDivInst_x3f_2758_);
lean_ctor_set(v_reuseFailAlloc_2802_, 12, v_ringInst_x3f_2759_);
lean_ctor_set(v_reuseFailAlloc_2802_, 13, v_commRingInst_x3f_2760_);
lean_ctor_set(v_reuseFailAlloc_2802_, 14, v_orderedRingInst_x3f_2761_);
lean_ctor_set(v_reuseFailAlloc_2802_, 15, v_fieldInst_x3f_2762_);
lean_ctor_set(v_reuseFailAlloc_2802_, 16, v_charInst_x3f_2763_);
lean_ctor_set(v_reuseFailAlloc_2802_, 17, v_zero_2764_);
lean_ctor_set(v_reuseFailAlloc_2802_, 18, v_ofNatZero_2765_);
lean_ctor_set(v_reuseFailAlloc_2802_, 19, v_one_x3f_2766_);
lean_ctor_set(v_reuseFailAlloc_2802_, 20, v_leFn_x3f_2767_);
lean_ctor_set(v_reuseFailAlloc_2802_, 21, v_ltFn_x3f_2768_);
lean_ctor_set(v_reuseFailAlloc_2802_, 22, v_addFn_2769_);
lean_ctor_set(v_reuseFailAlloc_2802_, 23, v_zsmulFn_2770_);
lean_ctor_set(v_reuseFailAlloc_2802_, 24, v_nsmulFn_2771_);
lean_ctor_set(v_reuseFailAlloc_2802_, 25, v_zsmulFn_x3f_2772_);
lean_ctor_set(v_reuseFailAlloc_2802_, 26, v_nsmulFn_x3f_2773_);
lean_ctor_set(v_reuseFailAlloc_2802_, 27, v_homomulFn_x3f_2774_);
lean_ctor_set(v_reuseFailAlloc_2802_, 28, v_subFn_2775_);
lean_ctor_set(v_reuseFailAlloc_2802_, 29, v_negFn_2776_);
lean_ctor_set(v_reuseFailAlloc_2802_, 30, v_vars_2777_);
lean_ctor_set(v_reuseFailAlloc_2802_, 31, v_varMap_2778_);
lean_ctor_set(v_reuseFailAlloc_2802_, 32, v_lowers_2779_);
lean_ctor_set(v_reuseFailAlloc_2802_, 33, v_uppers_2780_);
lean_ctor_set(v_reuseFailAlloc_2802_, 34, v_diseqs_2781_);
lean_ctor_set(v_reuseFailAlloc_2802_, 35, v_assignment_2782_);
lean_ctor_set(v_reuseFailAlloc_2802_, 36, v_conflict_x3f_2784_);
lean_ctor_set(v_reuseFailAlloc_2802_, 37, v_diseqSplits_2785_);
lean_ctor_set(v_reuseFailAlloc_2802_, 38, v_elimEqs_2786_);
lean_ctor_set(v_reuseFailAlloc_2802_, 39, v_elimStack_2787_);
lean_ctor_set(v_reuseFailAlloc_2802_, 40, v_occurs_2788_);
lean_ctor_set(v_reuseFailAlloc_2802_, 41, v___x_2795_);
lean_ctor_set_uint8(v_reuseFailAlloc_2802_, sizeof(void*)*42, v_caseSplits_2783_);
v___x_2797_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
lean_object* v___x_2798_; lean_object* v___x_2800_; 
v___x_2798_ = lean_array_fset(v_xs_x27_2794_, v___y_2730_, v___x_2797_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 0, v___x_2798_);
v___x_2800_ = v___x_2744_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2798_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_typeIdOf_2734_);
lean_ctor_set(v_reuseFailAlloc_2801_, 2, v_exprToStructId_2735_);
lean_ctor_set(v_reuseFailAlloc_2801_, 3, v_exprToStructIdEntries_2736_);
lean_ctor_set(v_reuseFailAlloc_2801_, 4, v_forbiddenNatModules_2737_);
lean_ctor_set(v_reuseFailAlloc_2801_, 5, v_natStructs_2738_);
lean_ctor_set(v_reuseFailAlloc_2801_, 6, v_natTypeIdOf_2739_);
lean_ctor_set(v_reuseFailAlloc_2801_, 7, v_exprToNatStructId_2740_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed(lean_object* v___y_2813_, lean_object* v_a_2814_, lean_object* v_s_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(v___y_2813_, v_a_2814_, v_s_2815_);
lean_dec(v___y_2813_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object* v_c_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_){
_start:
{
lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v_cls_2862_; lean_object* v___x_2863_; lean_object* v_a_2864_; uint8_t v___x_2865_; 
v_cls_2862_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2863_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v_cls_2862_, v_a_2834_);
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref(v___x_2863_);
v___x_2865_ = lean_unbox(v_a_2864_);
lean_dec(v_a_2864_);
if (v___x_2865_ == 0)
{
v___y_2838_ = v_a_2825_;
v___y_2839_ = v_a_2826_;
v___y_2840_ = v_a_2827_;
v___y_2841_ = v_a_2828_;
v___y_2842_ = v_a_2829_;
v___y_2843_ = v_a_2830_;
v___y_2844_ = v_a_2831_;
v___y_2845_ = v_a_2832_;
v___y_2846_ = v_a_2833_;
v___y_2847_ = v_a_2834_;
v___y_2848_ = v_a_2835_;
goto v___jp_2837_;
}
else
{
lean_object* v___x_2866_; 
v___x_2866_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref(v___x_2866_);
v___x_2868_ = l_Lean_MessageData_ofExpr(v_a_2867_);
v___x_2869_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_2862_, v___x_2868_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_dec_ref(v___x_2869_);
v___y_2838_ = v_a_2825_;
v___y_2839_ = v_a_2826_;
v___y_2840_ = v_a_2827_;
v___y_2841_ = v_a_2828_;
v___y_2842_ = v_a_2829_;
v___y_2843_ = v_a_2830_;
v___y_2844_ = v_a_2831_;
v___y_2845_ = v_a_2832_;
v___y_2846_ = v_a_2833_;
v___y_2847_ = v_a_2834_;
v___y_2848_ = v_a_2835_;
goto v___jp_2837_;
}
else
{
lean_dec(v_a_2825_);
return v___x_2869_;
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec(v_a_2825_);
v_a_2870_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2866_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2866_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
v___jp_2837_:
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2824_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___f_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref(v___x_2849_);
v___f_2851_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2851_, 0, v___y_2838_);
lean_closure_set(v___f_2851_, 1, v_a_2850_);
v___x_2852_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2853_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2852_, v___f_2851_, v___y_2839_);
return v___x_2853_;
}
else
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
lean_dec(v___y_2838_);
v_a_2854_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2849_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2849_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object* v_c_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
lean_dec(v_a_2889_);
lean_dec_ref(v_a_2888_);
lean_dec(v_a_2887_);
lean_dec_ref(v_a_2886_);
lean_dec(v_a_2885_);
lean_dec_ref(v_a_2884_);
lean_dec(v_a_2883_);
lean_dec_ref(v_a_2882_);
lean_dec(v_a_2881_);
lean_dec(v_a_2880_);
lean_dec_ref(v_c_2878_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object* v_c_u2082_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v_fileName_2905_; lean_object* v_fileMap_2906_; lean_object* v_options_2907_; lean_object* v_currRecDepth_2908_; lean_object* v_maxRecDepth_2909_; lean_object* v_ref_2910_; lean_object* v_currNamespace_2911_; lean_object* v_openDecls_2912_; lean_object* v_initHeartbeats_2913_; lean_object* v_maxHeartbeats_2914_; lean_object* v_quotContext_2915_; lean_object* v_currMacroScope_2916_; uint8_t v_diag_2917_; lean_object* v_cancelTk_x3f_2918_; uint8_t v_suppressElabErrors_2919_; lean_object* v_inheritedTraceOptions_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2979_; 
v_fileName_2905_ = lean_ctor_get(v_a_2902_, 0);
v_fileMap_2906_ = lean_ctor_get(v_a_2902_, 1);
v_options_2907_ = lean_ctor_get(v_a_2902_, 2);
v_currRecDepth_2908_ = lean_ctor_get(v_a_2902_, 3);
v_maxRecDepth_2909_ = lean_ctor_get(v_a_2902_, 4);
v_ref_2910_ = lean_ctor_get(v_a_2902_, 5);
v_currNamespace_2911_ = lean_ctor_get(v_a_2902_, 6);
v_openDecls_2912_ = lean_ctor_get(v_a_2902_, 7);
v_initHeartbeats_2913_ = lean_ctor_get(v_a_2902_, 8);
v_maxHeartbeats_2914_ = lean_ctor_get(v_a_2902_, 9);
v_quotContext_2915_ = lean_ctor_get(v_a_2902_, 10);
v_currMacroScope_2916_ = lean_ctor_get(v_a_2902_, 11);
v_diag_2917_ = lean_ctor_get_uint8(v_a_2902_, sizeof(void*)*14);
v_cancelTk_x3f_2918_ = lean_ctor_get(v_a_2902_, 12);
v_suppressElabErrors_2919_ = lean_ctor_get_uint8(v_a_2902_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2920_ = lean_ctor_get(v_a_2902_, 13);
v_isSharedCheck_2979_ = !lean_is_exclusive(v_a_2902_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2922_ = v_a_2902_;
v_isShared_2923_ = v_isSharedCheck_2979_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_inheritedTraceOptions_2920_);
lean_inc(v_cancelTk_x3f_2918_);
lean_inc(v_currMacroScope_2916_);
lean_inc(v_quotContext_2915_);
lean_inc(v_maxHeartbeats_2914_);
lean_inc(v_initHeartbeats_2913_);
lean_inc(v_openDecls_2912_);
lean_inc(v_currNamespace_2911_);
lean_inc(v_ref_2910_);
lean_inc(v_maxRecDepth_2909_);
lean_inc(v_currRecDepth_2908_);
lean_inc(v_options_2907_);
lean_inc(v_fileMap_2906_);
lean_inc(v_fileName_2905_);
lean_dec(v_a_2902_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2979_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
uint8_t v___x_2924_; 
v___x_2924_ = lean_nat_dec_eq(v_currRecDepth_2908_, v_maxRecDepth_2909_);
if (v___x_2924_ == 0)
{
lean_object* v_p_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2929_; 
v_p_2925_ = lean_ctor_get(v_c_u2082_2892_, 0);
v___x_2926_ = lean_unsigned_to_nat(1u);
v___x_2927_ = lean_nat_add(v_currRecDepth_2908_, v___x_2926_);
lean_dec(v_currRecDepth_2908_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 3, v___x_2927_);
v___x_2929_ = v___x_2922_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_fileName_2905_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_fileMap_2906_);
lean_ctor_set(v_reuseFailAlloc_2977_, 2, v_options_2907_);
lean_ctor_set(v_reuseFailAlloc_2977_, 3, v___x_2927_);
lean_ctor_set(v_reuseFailAlloc_2977_, 4, v_maxRecDepth_2909_);
lean_ctor_set(v_reuseFailAlloc_2977_, 5, v_ref_2910_);
lean_ctor_set(v_reuseFailAlloc_2977_, 6, v_currNamespace_2911_);
lean_ctor_set(v_reuseFailAlloc_2977_, 7, v_openDecls_2912_);
lean_ctor_set(v_reuseFailAlloc_2977_, 8, v_initHeartbeats_2913_);
lean_ctor_set(v_reuseFailAlloc_2977_, 9, v_maxHeartbeats_2914_);
lean_ctor_set(v_reuseFailAlloc_2977_, 10, v_quotContext_2915_);
lean_ctor_set(v_reuseFailAlloc_2977_, 11, v_currMacroScope_2916_);
lean_ctor_set(v_reuseFailAlloc_2977_, 12, v_cancelTk_x3f_2918_);
lean_ctor_set(v_reuseFailAlloc_2977_, 13, v_inheritedTraceOptions_2920_);
lean_ctor_set_uint8(v_reuseFailAlloc_2977_, sizeof(void*)*14, v_diag_2917_);
lean_ctor_set_uint8(v_reuseFailAlloc_2977_, sizeof(void*)*14 + 1, v_suppressElabErrors_2919_);
v___x_2929_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
lean_object* v___x_2930_; 
v___x_2930_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2925_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v___x_2929_, v_a_2903_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2968_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2933_ = v___x_2930_;
v_isShared_2934_ = v_isSharedCheck_2968_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2930_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2968_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
if (lean_obj_tag(v_a_2931_) == 1)
{
lean_object* v_val_2935_; lean_object* v_snd_2936_; lean_object* v_snd_2937_; lean_object* v_fst_2938_; lean_object* v_fst_2939_; lean_object* v_p_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
lean_del_object(v___x_2933_);
v_val_2935_ = lean_ctor_get(v_a_2931_, 0);
lean_inc(v_val_2935_);
lean_dec_ref(v_a_2931_);
v_snd_2936_ = lean_ctor_get(v_val_2935_, 1);
lean_inc(v_snd_2936_);
v_snd_2937_ = lean_ctor_get(v_snd_2936_, 1);
lean_inc(v_snd_2937_);
v_fst_2938_ = lean_ctor_get(v_val_2935_, 0);
lean_inc(v_fst_2938_);
lean_dec(v_val_2935_);
v_fst_2939_ = lean_ctor_get(v_snd_2936_, 0);
lean_inc(v_fst_2939_);
lean_dec(v_snd_2936_);
v_p_2940_ = lean_ctor_get(v_snd_2937_, 0);
v___x_2941_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2940_, v_fst_2939_);
lean_inc_ref(v_c_u2082_2892_);
v___x_2942_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v___x_2941_, v_fst_2939_, v_snd_2937_, v_fst_2938_, v_c_u2082_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v___x_2929_, v_a_2903_);
lean_dec(v_fst_2939_);
lean_dec(v___x_2941_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
lean_dec_ref(v___x_2942_);
if (lean_obj_tag(v_a_2943_) == 1)
{
lean_object* v_val_2944_; 
lean_dec_ref(v_c_u2082_2892_);
v_val_2944_ = lean_ctor_get(v_a_2943_, 0);
lean_inc(v_val_2944_);
lean_dec_ref(v_a_2943_);
v_c_u2082_2892_ = v_val_2944_;
v_a_2902_ = v___x_2929_;
goto _start;
}
else
{
lean_object* v___x_2946_; 
lean_dec(v_a_2943_);
v___x_2946_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_u2082_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v___x_2929_, v_a_2903_);
lean_dec_ref(v___x_2929_);
lean_dec_ref(v_c_u2082_2892_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2954_; 
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2954_ == 0)
{
lean_object* v_unused_2955_; 
v_unused_2955_ = lean_ctor_get(v___x_2946_, 0);
lean_dec(v_unused_2955_);
v___x_2948_ = v___x_2946_;
v_isShared_2949_ = v_isSharedCheck_2954_;
goto v_resetjp_2947_;
}
else
{
lean_dec(v___x_2946_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2954_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2950_; lean_object* v___x_2952_; 
v___x_2950_ = lean_box(0);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 0, v___x_2950_);
v___x_2952_ = v___x_2948_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2950_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
v_a_2956_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2946_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2946_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2929_);
lean_dec(v_a_2893_);
lean_dec_ref(v_c_u2082_2892_);
return v___x_2942_;
}
}
else
{
lean_object* v___x_2964_; lean_object* v___x_2966_; 
lean_dec(v_a_2931_);
lean_dec_ref(v___x_2929_);
lean_dec(v_a_2893_);
v___x_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2964_, 0, v_c_u2082_2892_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 0, v___x_2964_);
v___x_2966_ = v___x_2933_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2964_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
else
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
lean_dec_ref(v___x_2929_);
lean_dec(v_a_2893_);
lean_dec_ref(v_c_u2082_2892_);
v_a_2969_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v___x_2930_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2930_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
}
else
{
lean_object* v___x_2978_; 
lean_del_object(v___x_2922_);
lean_dec_ref(v_inheritedTraceOptions_2920_);
lean_dec(v_cancelTk_x3f_2918_);
lean_dec(v_currMacroScope_2916_);
lean_dec(v_quotContext_2915_);
lean_dec(v_maxHeartbeats_2914_);
lean_dec(v_initHeartbeats_2913_);
lean_dec(v_openDecls_2912_);
lean_dec(v_currNamespace_2911_);
lean_dec(v_maxRecDepth_2909_);
lean_dec(v_currRecDepth_2908_);
lean_dec_ref(v_options_2907_);
lean_dec_ref(v_fileMap_2906_);
lean_dec_ref(v_fileName_2905_);
lean_dec(v_a_2893_);
lean_dec_ref(v_c_u2082_2892_);
v___x_2978_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_2910_);
return v___x_2978_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object* v_c_u2082_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_u2082_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_);
lean_dec(v_a_2991_);
lean_dec(v_a_2989_);
lean_dec_ref(v_a_2988_);
lean_dec(v_a_2987_);
lean_dec_ref(v_a_2986_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec(v_a_2982_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(lean_object* v_val_2994_, lean_object* v_x_2995_, size_t v_x_2996_, size_t v_x_2997_){
_start:
{
if (lean_obj_tag(v_x_2995_) == 0)
{
lean_object* v_cs_2998_; size_t v_j_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; uint8_t v___x_3002_; 
v_cs_2998_ = lean_ctor_get(v_x_2995_, 0);
v_j_2999_ = lean_usize_shift_right(v_x_2996_, v_x_2997_);
v___x_3000_ = lean_usize_to_nat(v_j_2999_);
v___x_3001_ = lean_array_get_size(v_cs_2998_);
v___x_3002_ = lean_nat_dec_lt(v___x_3000_, v___x_3001_);
if (v___x_3002_ == 0)
{
lean_dec(v___x_3000_);
lean_dec_ref(v_val_2994_);
return v_x_2995_;
}
else
{
lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3020_; 
lean_inc_ref(v_cs_2998_);
v_isSharedCheck_3020_ = !lean_is_exclusive(v_x_2995_);
if (v_isSharedCheck_3020_ == 0)
{
lean_object* v_unused_3021_; 
v_unused_3021_ = lean_ctor_get(v_x_2995_, 0);
lean_dec(v_unused_3021_);
v___x_3004_ = v_x_2995_;
v_isShared_3005_ = v_isSharedCheck_3020_;
goto v_resetjp_3003_;
}
else
{
lean_dec(v_x_2995_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3020_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
size_t v___x_3006_; size_t v___x_3007_; size_t v___x_3008_; size_t v_i_3009_; size_t v___x_3010_; size_t v_shift_3011_; lean_object* v_v_3012_; lean_object* v___x_3013_; lean_object* v_xs_x27_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3018_; 
v___x_3006_ = ((size_t)1ULL);
v___x_3007_ = lean_usize_shift_left(v___x_3006_, v_x_2997_);
v___x_3008_ = lean_usize_sub(v___x_3007_, v___x_3006_);
v_i_3009_ = lean_usize_land(v_x_2996_, v___x_3008_);
v___x_3010_ = ((size_t)5ULL);
v_shift_3011_ = lean_usize_sub(v_x_2997_, v___x_3010_);
v_v_3012_ = lean_array_fget(v_cs_2998_, v___x_3000_);
v___x_3013_ = lean_box(0);
v_xs_x27_3014_ = lean_array_fset(v_cs_2998_, v___x_3000_, v___x_3013_);
v___x_3015_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(v_val_2994_, v_v_3012_, v_i_3009_, v_shift_3011_);
v___x_3016_ = lean_array_fset(v_xs_x27_3014_, v___x_3000_, v___x_3015_);
lean_dec(v___x_3000_);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 0, v___x_3016_);
v___x_3018_ = v___x_3004_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3016_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
else
{
lean_object* v_vs_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; 
v_vs_3022_ = lean_ctor_get(v_x_2995_, 0);
v___x_3023_ = lean_usize_to_nat(v_x_2996_);
v___x_3024_ = lean_array_get_size(v_vs_3022_);
v___x_3025_ = lean_nat_dec_lt(v___x_3023_, v___x_3024_);
if (v___x_3025_ == 0)
{
lean_dec(v___x_3023_);
lean_dec_ref(v_val_2994_);
return v_x_2995_;
}
else
{
lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3037_; 
lean_inc_ref(v_vs_3022_);
v_isSharedCheck_3037_ = !lean_is_exclusive(v_x_2995_);
if (v_isSharedCheck_3037_ == 0)
{
lean_object* v_unused_3038_; 
v_unused_3038_ = lean_ctor_get(v_x_2995_, 0);
lean_dec(v_unused_3038_);
v___x_3027_ = v_x_2995_;
v_isShared_3028_ = v_isSharedCheck_3037_;
goto v_resetjp_3026_;
}
else
{
lean_dec(v_x_2995_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3037_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v_v_3029_; lean_object* v___x_3030_; lean_object* v_xs_x27_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
v_v_3029_ = lean_array_fget(v_vs_3022_, v___x_3023_);
v___x_3030_ = lean_box(0);
v_xs_x27_3031_ = lean_array_fset(v_vs_3022_, v___x_3023_, v___x_3030_);
v___x_3032_ = l_Lean_PersistentArray_push___redArg(v_v_3029_, v_val_2994_);
v___x_3033_ = lean_array_fset(v_xs_x27_3031_, v___x_3023_, v___x_3032_);
lean_dec(v___x_3023_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3033_);
v___x_3035_ = v___x_3027_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg___boxed(lean_object* v_val_3039_, lean_object* v_x_3040_, lean_object* v_x_3041_, lean_object* v_x_3042_){
_start:
{
size_t v_x_38838__boxed_3043_; size_t v_x_38839__boxed_3044_; lean_object* v_res_3045_; 
v_x_38838__boxed_3043_ = lean_unbox_usize(v_x_3041_);
lean_dec(v_x_3041_);
v_x_38839__boxed_3044_ = lean_unbox_usize(v_x_3042_);
lean_dec(v_x_3042_);
v_res_3045_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(v_val_3039_, v_x_3040_, v_x_38838__boxed_3043_, v_x_38839__boxed_3044_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object* v_val_3046_, lean_object* v_inst_3047_, lean_object* v_t_3048_, lean_object* v_i_3049_){
_start:
{
lean_object* v_root_3050_; lean_object* v_tail_3051_; lean_object* v_size_3052_; size_t v_shift_3053_; lean_object* v_tailOff_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3078_; 
v_root_3050_ = lean_ctor_get(v_t_3048_, 0);
v_tail_3051_ = lean_ctor_get(v_t_3048_, 1);
v_size_3052_ = lean_ctor_get(v_t_3048_, 2);
v_shift_3053_ = lean_ctor_get_usize(v_t_3048_, 4);
v_tailOff_3054_ = lean_ctor_get(v_t_3048_, 3);
v_isSharedCheck_3078_ = !lean_is_exclusive(v_t_3048_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3056_ = v_t_3048_;
v_isShared_3057_ = v_isSharedCheck_3078_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_tailOff_3054_);
lean_inc(v_size_3052_);
lean_inc(v_tail_3051_);
lean_inc(v_root_3050_);
lean_dec(v_t_3048_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3078_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
uint8_t v___x_3058_; 
v___x_3058_ = lean_nat_dec_le(v_tailOff_3054_, v_i_3049_);
if (v___x_3058_ == 0)
{
size_t v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3062_; 
v___x_3059_ = lean_usize_of_nat(v_i_3049_);
v___x_3060_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(v_val_3046_, v_root_3050_, v___x_3059_, v_shift_3053_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 0, v___x_3060_);
v___x_3062_ = v___x_3056_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3060_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v_tail_3051_);
lean_ctor_set(v_reuseFailAlloc_3063_, 2, v_size_3052_);
lean_ctor_set(v_reuseFailAlloc_3063_, 3, v_tailOff_3054_);
lean_ctor_set_usize(v_reuseFailAlloc_3063_, 4, v_shift_3053_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
else
{
lean_object* v___x_3064_; lean_object* v___x_3065_; uint8_t v___x_3066_; 
v___x_3064_ = lean_nat_sub(v_i_3049_, v_tailOff_3054_);
v___x_3065_ = lean_array_get_size(v_tail_3051_);
v___x_3066_ = lean_nat_dec_lt(v___x_3064_, v___x_3065_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3068_; 
lean_dec(v___x_3064_);
lean_dec_ref(v_val_3046_);
if (v_isShared_3057_ == 0)
{
v___x_3068_ = v___x_3056_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_root_3050_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v_tail_3051_);
lean_ctor_set(v_reuseFailAlloc_3069_, 2, v_size_3052_);
lean_ctor_set(v_reuseFailAlloc_3069_, 3, v_tailOff_3054_);
lean_ctor_set_usize(v_reuseFailAlloc_3069_, 4, v_shift_3053_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
else
{
lean_object* v_v_3070_; lean_object* v___x_3071_; lean_object* v_xs_x27_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3076_; 
v_v_3070_ = lean_array_fget(v_tail_3051_, v___x_3064_);
v___x_3071_ = lean_box(0);
v_xs_x27_3072_ = lean_array_fset(v_tail_3051_, v___x_3064_, v___x_3071_);
v___x_3073_ = l_Lean_PersistentArray_push___redArg(v_v_3070_, v_val_3046_);
v___x_3074_ = lean_array_fset(v_xs_x27_3072_, v___x_3064_, v___x_3073_);
lean_dec(v___x_3064_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 1, v___x_3074_);
v___x_3076_ = v___x_3056_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_root_3050_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v___x_3074_);
lean_ctor_set(v_reuseFailAlloc_3077_, 2, v_size_3052_);
lean_ctor_set(v_reuseFailAlloc_3077_, 3, v_tailOff_3054_);
lean_ctor_set_usize(v_reuseFailAlloc_3077_, 4, v_shift_3053_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object* v_val_3079_, lean_object* v_inst_3080_, lean_object* v_t_3081_, lean_object* v_i_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3079_, v_inst_3080_, v_t_3081_, v_i_3082_);
lean_dec(v_i_3082_);
lean_dec_ref(v_inst_3080_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(lean_object* v___y_3084_, lean_object* v_val_3085_, lean_object* v___x_3086_, lean_object* v_v_3087_, lean_object* v_s_3088_){
_start:
{
lean_object* v_structs_3089_; lean_object* v_typeIdOf_3090_; lean_object* v_exprToStructId_3091_; lean_object* v_exprToStructIdEntries_3092_; lean_object* v_forbiddenNatModules_3093_; lean_object* v_natStructs_3094_; lean_object* v_natTypeIdOf_3095_; lean_object* v_exprToNatStructId_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; 
v_structs_3089_ = lean_ctor_get(v_s_3088_, 0);
v_typeIdOf_3090_ = lean_ctor_get(v_s_3088_, 1);
v_exprToStructId_3091_ = lean_ctor_get(v_s_3088_, 2);
v_exprToStructIdEntries_3092_ = lean_ctor_get(v_s_3088_, 3);
v_forbiddenNatModules_3093_ = lean_ctor_get(v_s_3088_, 4);
v_natStructs_3094_ = lean_ctor_get(v_s_3088_, 5);
v_natTypeIdOf_3095_ = lean_ctor_get(v_s_3088_, 6);
v_exprToNatStructId_3096_ = lean_ctor_get(v_s_3088_, 7);
v___x_3097_ = lean_array_get_size(v_structs_3089_);
v___x_3098_ = lean_nat_dec_lt(v___y_3084_, v___x_3097_);
if (v___x_3098_ == 0)
{
lean_dec_ref(v_val_3085_);
return v_s_3088_;
}
else
{
lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3160_; 
lean_inc_ref(v_exprToNatStructId_3096_);
lean_inc_ref(v_natTypeIdOf_3095_);
lean_inc_ref(v_natStructs_3094_);
lean_inc_ref(v_forbiddenNatModules_3093_);
lean_inc_ref(v_exprToStructIdEntries_3092_);
lean_inc_ref(v_exprToStructId_3091_);
lean_inc_ref(v_typeIdOf_3090_);
lean_inc_ref(v_structs_3089_);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_s_3088_);
if (v_isSharedCheck_3160_ == 0)
{
lean_object* v_unused_3161_; lean_object* v_unused_3162_; lean_object* v_unused_3163_; lean_object* v_unused_3164_; lean_object* v_unused_3165_; lean_object* v_unused_3166_; lean_object* v_unused_3167_; lean_object* v_unused_3168_; 
v_unused_3161_ = lean_ctor_get(v_s_3088_, 7);
lean_dec(v_unused_3161_);
v_unused_3162_ = lean_ctor_get(v_s_3088_, 6);
lean_dec(v_unused_3162_);
v_unused_3163_ = lean_ctor_get(v_s_3088_, 5);
lean_dec(v_unused_3163_);
v_unused_3164_ = lean_ctor_get(v_s_3088_, 4);
lean_dec(v_unused_3164_);
v_unused_3165_ = lean_ctor_get(v_s_3088_, 3);
lean_dec(v_unused_3165_);
v_unused_3166_ = lean_ctor_get(v_s_3088_, 2);
lean_dec(v_unused_3166_);
v_unused_3167_ = lean_ctor_get(v_s_3088_, 1);
lean_dec(v_unused_3167_);
v_unused_3168_ = lean_ctor_get(v_s_3088_, 0);
lean_dec(v_unused_3168_);
v___x_3100_ = v_s_3088_;
v_isShared_3101_ = v_isSharedCheck_3160_;
goto v_resetjp_3099_;
}
else
{
lean_dec(v_s_3088_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3160_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v_v_3102_; lean_object* v_id_3103_; lean_object* v_ringId_x3f_3104_; lean_object* v_type_3105_; lean_object* v_u_3106_; lean_object* v_intModuleInst_3107_; lean_object* v_leInst_x3f_3108_; lean_object* v_ltInst_x3f_3109_; lean_object* v_lawfulOrderLTInst_x3f_3110_; lean_object* v_isPreorderInst_x3f_3111_; lean_object* v_orderedAddInst_x3f_3112_; lean_object* v_isLinearInst_x3f_3113_; lean_object* v_noNatDivInst_x3f_3114_; lean_object* v_ringInst_x3f_3115_; lean_object* v_commRingInst_x3f_3116_; lean_object* v_orderedRingInst_x3f_3117_; lean_object* v_fieldInst_x3f_3118_; lean_object* v_charInst_x3f_3119_; lean_object* v_zero_3120_; lean_object* v_ofNatZero_3121_; lean_object* v_one_x3f_3122_; lean_object* v_leFn_x3f_3123_; lean_object* v_ltFn_x3f_3124_; lean_object* v_addFn_3125_; lean_object* v_zsmulFn_3126_; lean_object* v_nsmulFn_3127_; lean_object* v_zsmulFn_x3f_3128_; lean_object* v_nsmulFn_x3f_3129_; lean_object* v_homomulFn_x3f_3130_; lean_object* v_subFn_3131_; lean_object* v_negFn_3132_; lean_object* v_vars_3133_; lean_object* v_varMap_3134_; lean_object* v_lowers_3135_; lean_object* v_uppers_3136_; lean_object* v_diseqs_3137_; lean_object* v_assignment_3138_; uint8_t v_caseSplits_3139_; lean_object* v_conflict_x3f_3140_; lean_object* v_diseqSplits_3141_; lean_object* v_elimEqs_3142_; lean_object* v_elimStack_3143_; lean_object* v_occurs_3144_; lean_object* v_ignored_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3159_; 
v_v_3102_ = lean_array_fget(v_structs_3089_, v___y_3084_);
v_id_3103_ = lean_ctor_get(v_v_3102_, 0);
v_ringId_x3f_3104_ = lean_ctor_get(v_v_3102_, 1);
v_type_3105_ = lean_ctor_get(v_v_3102_, 2);
v_u_3106_ = lean_ctor_get(v_v_3102_, 3);
v_intModuleInst_3107_ = lean_ctor_get(v_v_3102_, 4);
v_leInst_x3f_3108_ = lean_ctor_get(v_v_3102_, 5);
v_ltInst_x3f_3109_ = lean_ctor_get(v_v_3102_, 6);
v_lawfulOrderLTInst_x3f_3110_ = lean_ctor_get(v_v_3102_, 7);
v_isPreorderInst_x3f_3111_ = lean_ctor_get(v_v_3102_, 8);
v_orderedAddInst_x3f_3112_ = lean_ctor_get(v_v_3102_, 9);
v_isLinearInst_x3f_3113_ = lean_ctor_get(v_v_3102_, 10);
v_noNatDivInst_x3f_3114_ = lean_ctor_get(v_v_3102_, 11);
v_ringInst_x3f_3115_ = lean_ctor_get(v_v_3102_, 12);
v_commRingInst_x3f_3116_ = lean_ctor_get(v_v_3102_, 13);
v_orderedRingInst_x3f_3117_ = lean_ctor_get(v_v_3102_, 14);
v_fieldInst_x3f_3118_ = lean_ctor_get(v_v_3102_, 15);
v_charInst_x3f_3119_ = lean_ctor_get(v_v_3102_, 16);
v_zero_3120_ = lean_ctor_get(v_v_3102_, 17);
v_ofNatZero_3121_ = lean_ctor_get(v_v_3102_, 18);
v_one_x3f_3122_ = lean_ctor_get(v_v_3102_, 19);
v_leFn_x3f_3123_ = lean_ctor_get(v_v_3102_, 20);
v_ltFn_x3f_3124_ = lean_ctor_get(v_v_3102_, 21);
v_addFn_3125_ = lean_ctor_get(v_v_3102_, 22);
v_zsmulFn_3126_ = lean_ctor_get(v_v_3102_, 23);
v_nsmulFn_3127_ = lean_ctor_get(v_v_3102_, 24);
v_zsmulFn_x3f_3128_ = lean_ctor_get(v_v_3102_, 25);
v_nsmulFn_x3f_3129_ = lean_ctor_get(v_v_3102_, 26);
v_homomulFn_x3f_3130_ = lean_ctor_get(v_v_3102_, 27);
v_subFn_3131_ = lean_ctor_get(v_v_3102_, 28);
v_negFn_3132_ = lean_ctor_get(v_v_3102_, 29);
v_vars_3133_ = lean_ctor_get(v_v_3102_, 30);
v_varMap_3134_ = lean_ctor_get(v_v_3102_, 31);
v_lowers_3135_ = lean_ctor_get(v_v_3102_, 32);
v_uppers_3136_ = lean_ctor_get(v_v_3102_, 33);
v_diseqs_3137_ = lean_ctor_get(v_v_3102_, 34);
v_assignment_3138_ = lean_ctor_get(v_v_3102_, 35);
v_caseSplits_3139_ = lean_ctor_get_uint8(v_v_3102_, sizeof(void*)*42);
v_conflict_x3f_3140_ = lean_ctor_get(v_v_3102_, 36);
v_diseqSplits_3141_ = lean_ctor_get(v_v_3102_, 37);
v_elimEqs_3142_ = lean_ctor_get(v_v_3102_, 38);
v_elimStack_3143_ = lean_ctor_get(v_v_3102_, 39);
v_occurs_3144_ = lean_ctor_get(v_v_3102_, 40);
v_ignored_3145_ = lean_ctor_get(v_v_3102_, 41);
v_isSharedCheck_3159_ = !lean_is_exclusive(v_v_3102_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3147_ = v_v_3102_;
v_isShared_3148_ = v_isSharedCheck_3159_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_ignored_3145_);
lean_inc(v_occurs_3144_);
lean_inc(v_elimStack_3143_);
lean_inc(v_elimEqs_3142_);
lean_inc(v_diseqSplits_3141_);
lean_inc(v_conflict_x3f_3140_);
lean_inc(v_assignment_3138_);
lean_inc(v_diseqs_3137_);
lean_inc(v_uppers_3136_);
lean_inc(v_lowers_3135_);
lean_inc(v_varMap_3134_);
lean_inc(v_vars_3133_);
lean_inc(v_negFn_3132_);
lean_inc(v_subFn_3131_);
lean_inc(v_homomulFn_x3f_3130_);
lean_inc(v_nsmulFn_x3f_3129_);
lean_inc(v_zsmulFn_x3f_3128_);
lean_inc(v_nsmulFn_3127_);
lean_inc(v_zsmulFn_3126_);
lean_inc(v_addFn_3125_);
lean_inc(v_ltFn_x3f_3124_);
lean_inc(v_leFn_x3f_3123_);
lean_inc(v_one_x3f_3122_);
lean_inc(v_ofNatZero_3121_);
lean_inc(v_zero_3120_);
lean_inc(v_charInst_x3f_3119_);
lean_inc(v_fieldInst_x3f_3118_);
lean_inc(v_orderedRingInst_x3f_3117_);
lean_inc(v_commRingInst_x3f_3116_);
lean_inc(v_ringInst_x3f_3115_);
lean_inc(v_noNatDivInst_x3f_3114_);
lean_inc(v_isLinearInst_x3f_3113_);
lean_inc(v_orderedAddInst_x3f_3112_);
lean_inc(v_isPreorderInst_x3f_3111_);
lean_inc(v_lawfulOrderLTInst_x3f_3110_);
lean_inc(v_ltInst_x3f_3109_);
lean_inc(v_leInst_x3f_3108_);
lean_inc(v_intModuleInst_3107_);
lean_inc(v_u_3106_);
lean_inc(v_type_3105_);
lean_inc(v_ringId_x3f_3104_);
lean_inc(v_id_3103_);
lean_dec(v_v_3102_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3159_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3149_; lean_object* v_xs_x27_3150_; lean_object* v___x_3151_; lean_object* v___x_3153_; 
v___x_3149_ = lean_box(0);
v_xs_x27_3150_ = lean_array_fset(v_structs_3089_, v___y_3084_, v___x_3149_);
v___x_3151_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3085_, v___x_3086_, v_diseqs_3137_, v_v_3087_);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 34, v___x_3151_);
v___x_3153_ = v___x_3147_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_id_3103_);
lean_ctor_set(v_reuseFailAlloc_3158_, 1, v_ringId_x3f_3104_);
lean_ctor_set(v_reuseFailAlloc_3158_, 2, v_type_3105_);
lean_ctor_set(v_reuseFailAlloc_3158_, 3, v_u_3106_);
lean_ctor_set(v_reuseFailAlloc_3158_, 4, v_intModuleInst_3107_);
lean_ctor_set(v_reuseFailAlloc_3158_, 5, v_leInst_x3f_3108_);
lean_ctor_set(v_reuseFailAlloc_3158_, 6, v_ltInst_x3f_3109_);
lean_ctor_set(v_reuseFailAlloc_3158_, 7, v_lawfulOrderLTInst_x3f_3110_);
lean_ctor_set(v_reuseFailAlloc_3158_, 8, v_isPreorderInst_x3f_3111_);
lean_ctor_set(v_reuseFailAlloc_3158_, 9, v_orderedAddInst_x3f_3112_);
lean_ctor_set(v_reuseFailAlloc_3158_, 10, v_isLinearInst_x3f_3113_);
lean_ctor_set(v_reuseFailAlloc_3158_, 11, v_noNatDivInst_x3f_3114_);
lean_ctor_set(v_reuseFailAlloc_3158_, 12, v_ringInst_x3f_3115_);
lean_ctor_set(v_reuseFailAlloc_3158_, 13, v_commRingInst_x3f_3116_);
lean_ctor_set(v_reuseFailAlloc_3158_, 14, v_orderedRingInst_x3f_3117_);
lean_ctor_set(v_reuseFailAlloc_3158_, 15, v_fieldInst_x3f_3118_);
lean_ctor_set(v_reuseFailAlloc_3158_, 16, v_charInst_x3f_3119_);
lean_ctor_set(v_reuseFailAlloc_3158_, 17, v_zero_3120_);
lean_ctor_set(v_reuseFailAlloc_3158_, 18, v_ofNatZero_3121_);
lean_ctor_set(v_reuseFailAlloc_3158_, 19, v_one_x3f_3122_);
lean_ctor_set(v_reuseFailAlloc_3158_, 20, v_leFn_x3f_3123_);
lean_ctor_set(v_reuseFailAlloc_3158_, 21, v_ltFn_x3f_3124_);
lean_ctor_set(v_reuseFailAlloc_3158_, 22, v_addFn_3125_);
lean_ctor_set(v_reuseFailAlloc_3158_, 23, v_zsmulFn_3126_);
lean_ctor_set(v_reuseFailAlloc_3158_, 24, v_nsmulFn_3127_);
lean_ctor_set(v_reuseFailAlloc_3158_, 25, v_zsmulFn_x3f_3128_);
lean_ctor_set(v_reuseFailAlloc_3158_, 26, v_nsmulFn_x3f_3129_);
lean_ctor_set(v_reuseFailAlloc_3158_, 27, v_homomulFn_x3f_3130_);
lean_ctor_set(v_reuseFailAlloc_3158_, 28, v_subFn_3131_);
lean_ctor_set(v_reuseFailAlloc_3158_, 29, v_negFn_3132_);
lean_ctor_set(v_reuseFailAlloc_3158_, 30, v_vars_3133_);
lean_ctor_set(v_reuseFailAlloc_3158_, 31, v_varMap_3134_);
lean_ctor_set(v_reuseFailAlloc_3158_, 32, v_lowers_3135_);
lean_ctor_set(v_reuseFailAlloc_3158_, 33, v_uppers_3136_);
lean_ctor_set(v_reuseFailAlloc_3158_, 34, v___x_3151_);
lean_ctor_set(v_reuseFailAlloc_3158_, 35, v_assignment_3138_);
lean_ctor_set(v_reuseFailAlloc_3158_, 36, v_conflict_x3f_3140_);
lean_ctor_set(v_reuseFailAlloc_3158_, 37, v_diseqSplits_3141_);
lean_ctor_set(v_reuseFailAlloc_3158_, 38, v_elimEqs_3142_);
lean_ctor_set(v_reuseFailAlloc_3158_, 39, v_elimStack_3143_);
lean_ctor_set(v_reuseFailAlloc_3158_, 40, v_occurs_3144_);
lean_ctor_set(v_reuseFailAlloc_3158_, 41, v_ignored_3145_);
lean_ctor_set_uint8(v_reuseFailAlloc_3158_, sizeof(void*)*42, v_caseSplits_3139_);
v___x_3153_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
lean_object* v___x_3154_; lean_object* v___x_3156_; 
v___x_3154_ = lean_array_fset(v_xs_x27_3150_, v___y_3084_, v___x_3153_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 0, v___x_3154_);
v___x_3156_ = v___x_3100_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3154_);
lean_ctor_set(v_reuseFailAlloc_3157_, 1, v_typeIdOf_3090_);
lean_ctor_set(v_reuseFailAlloc_3157_, 2, v_exprToStructId_3091_);
lean_ctor_set(v_reuseFailAlloc_3157_, 3, v_exprToStructIdEntries_3092_);
lean_ctor_set(v_reuseFailAlloc_3157_, 4, v_forbiddenNatModules_3093_);
lean_ctor_set(v_reuseFailAlloc_3157_, 5, v_natStructs_3094_);
lean_ctor_set(v_reuseFailAlloc_3157_, 6, v_natTypeIdOf_3095_);
lean_ctor_set(v_reuseFailAlloc_3157_, 7, v_exprToNatStructId_3096_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed(lean_object* v___y_3169_, lean_object* v_val_3170_, lean_object* v___x_3171_, lean_object* v_v_3172_, lean_object* v_s_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(v___y_3169_, v_val_3170_, v___x_3171_, v_v_3172_, v_s_3173_);
lean_dec(v_v_3172_);
lean_dec_ref(v___x_3171_);
lean_dec(v___y_3169_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object* v_c_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_){
_start:
{
lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v_cls_3218_; lean_object* v___x_3219_; lean_object* v_a_3220_; lean_object* v___x_3221_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; uint8_t v___x_3330_; 
v_cls_3218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0));
v___x_3219_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v_cls_3218_, v_a_3200_);
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref(v___x_3219_);
v___x_3221_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_3330_ = lean_unbox(v_a_3220_);
lean_dec(v_a_3220_);
if (v___x_3330_ == 0)
{
v___y_3266_ = v_a_3191_;
v___y_3267_ = v_a_3192_;
v___y_3268_ = v_a_3193_;
v___y_3269_ = v_a_3194_;
v___y_3270_ = v_a_3195_;
v___y_3271_ = v_a_3196_;
v___y_3272_ = v_a_3197_;
v___y_3273_ = v_a_3198_;
v___y_3274_ = v_a_3199_;
v___y_3275_ = v_a_3200_;
v___y_3276_ = v_a_3201_;
goto v___jp_3265_;
}
else
{
lean_object* v___x_3331_; 
v___x_3331_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_object* v_a_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
lean_inc(v_a_3332_);
lean_dec_ref(v___x_3331_);
v___x_3333_ = l_Lean_MessageData_ofExpr(v_a_3332_);
v___x_3334_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_3218_, v___x_3333_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_dec_ref(v___x_3334_);
v___y_3266_ = v_a_3191_;
v___y_3267_ = v_a_3192_;
v___y_3268_ = v_a_3193_;
v___y_3269_ = v_a_3194_;
v___y_3270_ = v_a_3195_;
v___y_3271_ = v_a_3196_;
v___y_3272_ = v_a_3197_;
v___y_3273_ = v_a_3198_;
v___y_3274_ = v_a_3199_;
v___y_3275_ = v_a_3200_;
v___y_3276_ = v_a_3201_;
goto v___jp_3265_;
}
else
{
lean_dec(v_a_3201_);
lean_dec_ref(v_a_3200_);
lean_dec(v_a_3199_);
lean_dec_ref(v_a_3198_);
lean_dec(v_a_3197_);
lean_dec_ref(v_a_3196_);
lean_dec(v_a_3195_);
lean_dec_ref(v_a_3194_);
lean_dec(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec(v_a_3191_);
lean_dec_ref(v_c_3190_);
return v___x_3334_;
}
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
lean_dec(v_a_3201_);
lean_dec_ref(v_a_3200_);
lean_dec(v_a_3199_);
lean_dec_ref(v_a_3198_);
lean_dec(v_a_3197_);
lean_dec_ref(v_a_3196_);
lean_dec(v_a_3195_);
lean_dec_ref(v_a_3194_);
lean_dec(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec(v_a_3191_);
lean_dec_ref(v_c_3190_);
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
v___jp_3203_:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3216_, 0, v___y_3204_);
v___x_3217_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(v___x_3216_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
return v___x_3217_;
}
v___jp_3222_:
{
lean_object* v___x_3239_; 
lean_inc(v___y_3228_);
v___x_3239_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v___f_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
lean_dec_ref(v___x_3239_);
lean_inc(v___y_3228_);
v___f_3240_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3240_, 0, v___y_3228_);
lean_closure_set(v___f_3240_, 1, v___y_3224_);
lean_closure_set(v___f_3240_, 2, v___x_3221_);
lean_closure_set(v___f_3240_, 3, v___y_3223_);
v___x_3241_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3242_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3241_, v___f_3240_, v___y_3229_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v___x_3243_; 
lean_dec_ref(v___x_3242_);
v___x_3243_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v___y_3226_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3256_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3246_ = v___x_3243_;
v_isShared_3247_ = v_isSharedCheck_3256_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3243_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3256_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
uint8_t v___x_3248_; uint8_t v___x_3249_; uint8_t v___x_3250_; 
v___x_3248_ = 0;
v___x_3249_ = lean_unbox(v_a_3244_);
lean_dec(v_a_3244_);
v___x_3250_ = l_Lean_instBEqLBool_beq(v___x_3249_, v___x_3248_);
if (v___x_3250_ == 0)
{
lean_object* v___x_3251_; lean_object* v___x_3253_; 
lean_dec(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec(v___y_3225_);
v___x_3251_ = lean_box(0);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 0, v___x_3251_);
v___x_3253_ = v___x_3246_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3251_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
else
{
lean_object* v___x_3255_; 
lean_del_object(v___x_3246_);
v___x_3255_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_3225_, v___y_3228_, v___y_3229_);
lean_dec(v___y_3229_);
return v___x_3255_;
}
}
}
else
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
lean_dec(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec(v___y_3225_);
v_a_3257_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v___x_3243_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3243_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
else
{
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
return v___x_3242_;
}
}
else
{
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
return v___x_3239_;
}
}
v___jp_3265_:
{
lean_object* v___x_3277_; 
lean_inc_ref(v___y_3275_);
lean_inc(v___y_3266_);
v___x_3277_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_3190_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3321_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3280_ = v___x_3277_;
v_isShared_3281_ = v_isSharedCheck_3321_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3277_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3321_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
if (lean_obj_tag(v_a_3278_) == 1)
{
lean_object* v_val_3282_; lean_object* v_p_3283_; 
lean_del_object(v___x_3280_);
v_val_3282_ = lean_ctor_get(v_a_3278_, 0);
lean_inc(v_val_3282_);
lean_dec_ref(v_a_3278_);
v_p_3283_ = lean_ctor_get(v_val_3282_, 0);
if (lean_obj_tag(v_p_3283_) == 0)
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v_a_3286_; uint8_t v___x_3287_; 
v___x_3284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2));
v___x_3285_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_3284_, v___y_3275_);
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3286_);
lean_dec_ref(v___x_3285_);
v___x_3287_ = lean_unbox(v_a_3286_);
lean_dec(v_a_3286_);
if (v___x_3287_ == 0)
{
v___y_3204_ = v_val_3282_;
v___y_3205_ = v___y_3266_;
v___y_3206_ = v___y_3267_;
v___y_3207_ = v___y_3268_;
v___y_3208_ = v___y_3269_;
v___y_3209_ = v___y_3270_;
v___y_3210_ = v___y_3271_;
v___y_3211_ = v___y_3272_;
v___y_3212_ = v___y_3273_;
v___y_3213_ = v___y_3274_;
v___y_3214_ = v___y_3275_;
v___y_3215_ = v___y_3276_;
goto v___jp_3203_;
}
else
{
lean_object* v___x_3288_; 
v___x_3288_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3282_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3289_);
lean_dec_ref(v___x_3288_);
v___x_3290_ = l_Lean_MessageData_ofExpr(v_a_3289_);
v___x_3291_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_3284_, v___x_3290_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_dec_ref(v___x_3291_);
v___y_3204_ = v_val_3282_;
v___y_3205_ = v___y_3266_;
v___y_3206_ = v___y_3267_;
v___y_3207_ = v___y_3268_;
v___y_3208_ = v___y_3269_;
v___y_3209_ = v___y_3270_;
v___y_3210_ = v___y_3271_;
v___y_3211_ = v___y_3272_;
v___y_3212_ = v___y_3273_;
v___y_3213_ = v___y_3274_;
v___y_3214_ = v___y_3275_;
v___y_3215_ = v___y_3276_;
goto v___jp_3203_;
}
else
{
lean_dec(v_val_3282_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec(v___y_3266_);
return v___x_3291_;
}
}
else
{
lean_object* v_a_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3299_; 
lean_dec(v_val_3282_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec(v___y_3266_);
v_a_3292_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3294_ = v___x_3288_;
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_a_3292_);
lean_dec(v___x_3288_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3297_; 
if (v_isShared_3295_ == 0)
{
v___x_3297_ = v___x_3294_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_a_3292_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
}
}
else
{
lean_object* v_v_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v_a_3303_; uint8_t v___x_3304_; 
lean_inc_ref(v_p_3283_);
v_v_3300_ = lean_ctor_get(v_p_3283_, 1);
lean_inc(v_v_3300_);
v___x_3301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3302_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_3301_, v___y_3275_);
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_a_3303_);
lean_dec_ref(v___x_3302_);
v___x_3304_ = lean_unbox(v_a_3303_);
lean_dec(v_a_3303_);
if (v___x_3304_ == 0)
{
lean_inc(v_val_3282_);
lean_inc(v_v_3300_);
v___y_3223_ = v_v_3300_;
v___y_3224_ = v_val_3282_;
v___y_3225_ = v_v_3300_;
v___y_3226_ = v_val_3282_;
v___y_3227_ = v_p_3283_;
v___y_3228_ = v___y_3266_;
v___y_3229_ = v___y_3267_;
v___y_3230_ = v___y_3268_;
v___y_3231_ = v___y_3269_;
v___y_3232_ = v___y_3270_;
v___y_3233_ = v___y_3271_;
v___y_3234_ = v___y_3272_;
v___y_3235_ = v___y_3273_;
v___y_3236_ = v___y_3274_;
v___y_3237_ = v___y_3275_;
v___y_3238_ = v___y_3276_;
goto v___jp_3222_;
}
else
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3282_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_a_3306_);
lean_dec_ref(v___x_3305_);
v___x_3307_ = l_Lean_MessageData_ofExpr(v_a_3306_);
v___x_3308_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_3301_, v___x_3307_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_dec_ref(v___x_3308_);
lean_inc(v_val_3282_);
lean_inc(v_v_3300_);
v___y_3223_ = v_v_3300_;
v___y_3224_ = v_val_3282_;
v___y_3225_ = v_v_3300_;
v___y_3226_ = v_val_3282_;
v___y_3227_ = v_p_3283_;
v___y_3228_ = v___y_3266_;
v___y_3229_ = v___y_3267_;
v___y_3230_ = v___y_3268_;
v___y_3231_ = v___y_3269_;
v___y_3232_ = v___y_3270_;
v___y_3233_ = v___y_3271_;
v___y_3234_ = v___y_3272_;
v___y_3235_ = v___y_3273_;
v___y_3236_ = v___y_3274_;
v___y_3237_ = v___y_3275_;
v___y_3238_ = v___y_3276_;
goto v___jp_3222_;
}
else
{
lean_dec(v_v_3300_);
lean_dec_ref(v_p_3283_);
lean_dec(v_val_3282_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec(v___y_3266_);
return v___x_3308_;
}
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_dec_ref(v_p_3283_);
lean_dec(v_v_3300_);
lean_dec(v_val_3282_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec(v___y_3266_);
v_a_3309_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3305_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3305_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
}
}
else
{
lean_object* v___x_3317_; lean_object* v___x_3319_; 
lean_dec(v_a_3278_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec(v___y_3266_);
v___x_3317_ = lean_box(0);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 0, v___x_3317_);
v___x_3319_ = v___x_3280_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3317_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec(v___y_3266_);
v_a_3322_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v___x_3277_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3277_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___boxed(lean_object* v_c_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_c_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object* v_val_3357_, lean_object* v_inst_3358_, lean_object* v_x_3359_, size_t v_x_3360_, size_t v_x_3361_){
_start:
{
lean_object* v___x_3362_; 
v___x_3362_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___redArg(v_val_3357_, v_x_3359_, v_x_3360_, v_x_3361_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_val_3363_, lean_object* v_inst_3364_, lean_object* v_x_3365_, lean_object* v_x_3366_, lean_object* v_x_3367_){
_start:
{
size_t v_x_39415__boxed_3368_; size_t v_x_39416__boxed_3369_; lean_object* v_res_3370_; 
v_x_39415__boxed_3368_ = lean_unbox_usize(v_x_3366_);
lean_dec(v_x_3366_);
v_x_39416__boxed_3369_ = lean_unbox_usize(v_x_3367_);
lean_dec(v_x_3367_);
v_res_3370_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_3363_, v_inst_3364_, v_x_3365_, v_x_39415__boxed_3368_, v_x_39416__boxed_3369_);
lean_dec_ref(v_inst_3364_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_3371_, lean_object* v_as_3372_, size_t v_sz_3373_, size_t v_i_3374_, lean_object* v_b_3375_){
_start:
{
uint8_t v___x_3376_; 
v___x_3376_ = lean_usize_dec_lt(v_i_3374_, v_sz_3373_);
if (v___x_3376_ == 0)
{
return v_b_3375_;
}
else
{
lean_object* v_snd_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3418_; 
v_snd_3377_ = lean_ctor_get(v_b_3375_, 1);
v_isSharedCheck_3418_ = !lean_is_exclusive(v_b_3375_);
if (v_isSharedCheck_3418_ == 0)
{
lean_object* v_unused_3419_; 
v_unused_3419_ = lean_ctor_get(v_b_3375_, 0);
lean_dec(v_unused_3419_);
v___x_3379_ = v_b_3375_;
v_isShared_3380_ = v_isSharedCheck_3418_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_snd_3377_);
lean_dec(v_b_3375_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3418_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v_fst_3381_; lean_object* v_snd_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3417_; 
v_fst_3381_ = lean_ctor_get(v_snd_3377_, 0);
v_snd_3382_ = lean_ctor_get(v_snd_3377_, 1);
v_isSharedCheck_3417_ = !lean_is_exclusive(v_snd_3377_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3384_ = v_snd_3377_;
v_isShared_3385_ = v_isSharedCheck_3417_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_snd_3382_);
lean_inc(v_fst_3381_);
lean_dec(v_snd_3377_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3417_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v_a_3386_; lean_object* v_p_3387_; lean_object* v___x_3388_; lean_object* v_a_3390_; lean_object* v_b_3397_; lean_object* v___x_3398_; uint8_t v___x_3399_; 
v_a_3386_ = lean_array_uget(v_as_3372_, v_i_3374_);
v_p_3387_ = lean_ctor_get(v_a_3386_, 0);
v___x_3388_ = lean_box(0);
v_b_3397_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3387_, v_x_3371_);
v___x_3398_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3399_ = lean_int_dec_eq(v_b_3397_, v___x_3398_);
if (v___x_3399_ == 0)
{
lean_object* v___x_3401_; 
lean_inc(v_a_3386_);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 1, v_a_3386_);
lean_ctor_set(v___x_3379_, 0, v_b_3397_);
v___x_3401_ = v___x_3379_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_b_3397_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_a_3386_);
v___x_3401_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3409_; 
v_isSharedCheck_3409_ = !lean_is_exclusive(v_a_3386_);
if (v_isSharedCheck_3409_ == 0)
{
lean_object* v_unused_3410_; lean_object* v_unused_3411_; 
v_unused_3410_ = lean_ctor_get(v_a_3386_, 1);
lean_dec(v_unused_3410_);
v_unused_3411_ = lean_ctor_get(v_a_3386_, 0);
lean_dec(v_unused_3411_);
v___x_3403_ = v_a_3386_;
v_isShared_3404_ = v_isSharedCheck_3409_;
goto v_resetjp_3402_;
}
else
{
lean_dec(v_a_3386_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3409_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v_todo_3405_; lean_object* v___x_3407_; 
v_todo_3405_ = lean_array_push(v_snd_3382_, v___x_3401_);
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 1, v_todo_3405_);
lean_ctor_set(v___x_3403_, 0, v_fst_3381_);
v___x_3407_ = v___x_3403_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_fst_3381_);
lean_ctor_set(v_reuseFailAlloc_3408_, 1, v_todo_3405_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
v_a_3390_ = v___x_3407_;
goto v___jp_3389_;
}
}
}
}
else
{
lean_object* v_cs_x27_3413_; lean_object* v___x_3415_; 
lean_dec(v_b_3397_);
v_cs_x27_3413_ = l_Lean_PersistentArray_push___redArg(v_fst_3381_, v_a_3386_);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 1, v_snd_3382_);
lean_ctor_set(v___x_3379_, 0, v_cs_x27_3413_);
v___x_3415_ = v___x_3379_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_cs_x27_3413_);
lean_ctor_set(v_reuseFailAlloc_3416_, 1, v_snd_3382_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
v_a_3390_ = v___x_3415_;
goto v___jp_3389_;
}
}
v___jp_3389_:
{
lean_object* v___x_3392_; 
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 1, v_a_3390_);
lean_ctor_set(v___x_3384_, 0, v___x_3388_);
v___x_3392_ = v___x_3384_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3388_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v_a_3390_);
v___x_3392_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
size_t v___x_3393_; size_t v___x_3394_; 
v___x_3393_ = ((size_t)1ULL);
v___x_3394_ = lean_usize_add(v_i_3374_, v___x_3393_);
v_i_3374_ = v___x_3394_;
v_b_3375_ = v___x_3392_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_3420_, lean_object* v_as_3421_, lean_object* v_sz_3422_, lean_object* v_i_3423_, lean_object* v_b_3424_){
_start:
{
size_t v_sz_boxed_3425_; size_t v_i_boxed_3426_; lean_object* v_res_3427_; 
v_sz_boxed_3425_ = lean_unbox_usize(v_sz_3422_);
lean_dec(v_sz_3422_);
v_i_boxed_3426_ = lean_unbox_usize(v_i_3423_);
lean_dec(v_i_3423_);
v_res_3427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3420_, v_as_3421_, v_sz_boxed_3425_, v_i_boxed_3426_, v_b_3424_);
lean_dec_ref(v_as_3421_);
lean_dec(v_x_3420_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(lean_object* v_x_3428_, lean_object* v_as_3429_, size_t v_sz_3430_, size_t v_i_3431_, lean_object* v_b_3432_){
_start:
{
uint8_t v___x_3433_; 
v___x_3433_ = lean_usize_dec_lt(v_i_3431_, v_sz_3430_);
if (v___x_3433_ == 0)
{
return v_b_3432_;
}
else
{
lean_object* v_snd_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3475_; 
v_snd_3434_ = lean_ctor_get(v_b_3432_, 1);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_b_3432_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; 
v_unused_3476_ = lean_ctor_get(v_b_3432_, 0);
lean_dec(v_unused_3476_);
v___x_3436_ = v_b_3432_;
v_isShared_3437_ = v_isSharedCheck_3475_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_snd_3434_);
lean_dec(v_b_3432_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3475_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v_fst_3438_; lean_object* v_snd_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3474_; 
v_fst_3438_ = lean_ctor_get(v_snd_3434_, 0);
v_snd_3439_ = lean_ctor_get(v_snd_3434_, 1);
v_isSharedCheck_3474_ = !lean_is_exclusive(v_snd_3434_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3441_ = v_snd_3434_;
v_isShared_3442_ = v_isSharedCheck_3474_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_snd_3439_);
lean_inc(v_fst_3438_);
lean_dec(v_snd_3434_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3474_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v_a_3443_; lean_object* v_p_3444_; lean_object* v___x_3445_; lean_object* v_a_3447_; lean_object* v_b_3454_; lean_object* v___x_3455_; uint8_t v___x_3456_; 
v_a_3443_ = lean_array_uget(v_as_3429_, v_i_3431_);
v_p_3444_ = lean_ctor_get(v_a_3443_, 0);
v___x_3445_ = lean_box(0);
v_b_3454_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3444_, v_x_3428_);
v___x_3455_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3456_ = lean_int_dec_eq(v_b_3454_, v___x_3455_);
if (v___x_3456_ == 0)
{
lean_object* v___x_3458_; 
lean_inc(v_a_3443_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 1, v_a_3443_);
lean_ctor_set(v___x_3436_, 0, v_b_3454_);
v___x_3458_ = v___x_3436_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_b_3454_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_a_3443_);
v___x_3458_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3466_; 
v_isSharedCheck_3466_ = !lean_is_exclusive(v_a_3443_);
if (v_isSharedCheck_3466_ == 0)
{
lean_object* v_unused_3467_; lean_object* v_unused_3468_; 
v_unused_3467_ = lean_ctor_get(v_a_3443_, 1);
lean_dec(v_unused_3467_);
v_unused_3468_ = lean_ctor_get(v_a_3443_, 0);
lean_dec(v_unused_3468_);
v___x_3460_ = v_a_3443_;
v_isShared_3461_ = v_isSharedCheck_3466_;
goto v_resetjp_3459_;
}
else
{
lean_dec(v_a_3443_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3466_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v_todo_3462_; lean_object* v___x_3464_; 
v_todo_3462_ = lean_array_push(v_snd_3439_, v___x_3458_);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 1, v_todo_3462_);
lean_ctor_set(v___x_3460_, 0, v_fst_3438_);
v___x_3464_ = v___x_3460_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_fst_3438_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_todo_3462_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
v_a_3447_ = v___x_3464_;
goto v___jp_3446_;
}
}
}
}
else
{
lean_object* v_cs_x27_3470_; lean_object* v___x_3472_; 
lean_dec(v_b_3454_);
v_cs_x27_3470_ = l_Lean_PersistentArray_push___redArg(v_fst_3438_, v_a_3443_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 1, v_snd_3439_);
lean_ctor_set(v___x_3436_, 0, v_cs_x27_3470_);
v___x_3472_ = v___x_3436_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_cs_x27_3470_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v_snd_3439_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
v_a_3447_ = v___x_3472_;
goto v___jp_3446_;
}
}
v___jp_3446_:
{
lean_object* v___x_3449_; 
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 1, v_a_3447_);
lean_ctor_set(v___x_3441_, 0, v___x_3445_);
v___x_3449_ = v___x_3441_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3445_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_a_3447_);
v___x_3449_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
size_t v___x_3450_; size_t v___x_3451_; lean_object* v___x_3452_; 
v___x_3450_ = ((size_t)1ULL);
v___x_3451_ = lean_usize_add(v_i_3431_, v___x_3450_);
v___x_3452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3428_, v_as_3429_, v_sz_3430_, v___x_3451_, v___x_3449_);
return v___x_3452_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_3477_, lean_object* v_as_3478_, lean_object* v_sz_3479_, lean_object* v_i_3480_, lean_object* v_b_3481_){
_start:
{
size_t v_sz_boxed_3482_; size_t v_i_boxed_3483_; lean_object* v_res_3484_; 
v_sz_boxed_3482_ = lean_unbox_usize(v_sz_3479_);
lean_dec(v_sz_3479_);
v_i_boxed_3483_ = lean_unbox_usize(v_i_3480_);
lean_dec(v_i_3480_);
v_res_3484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3477_, v_as_3478_, v_sz_boxed_3482_, v_i_boxed_3483_, v_b_3481_);
lean_dec_ref(v_as_3478_);
lean_dec(v_x_3477_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_3485_, lean_object* v_as_3486_, size_t v_sz_3487_, size_t v_i_3488_, lean_object* v_b_3489_){
_start:
{
uint8_t v___x_3490_; 
v___x_3490_ = lean_usize_dec_lt(v_i_3488_, v_sz_3487_);
if (v___x_3490_ == 0)
{
return v_b_3489_;
}
else
{
lean_object* v_snd_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3532_; 
v_snd_3491_ = lean_ctor_get(v_b_3489_, 1);
v_isSharedCheck_3532_ = !lean_is_exclusive(v_b_3489_);
if (v_isSharedCheck_3532_ == 0)
{
lean_object* v_unused_3533_; 
v_unused_3533_ = lean_ctor_get(v_b_3489_, 0);
lean_dec(v_unused_3533_);
v___x_3493_ = v_b_3489_;
v_isShared_3494_ = v_isSharedCheck_3532_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_snd_3491_);
lean_dec(v_b_3489_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3532_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v_fst_3495_; lean_object* v_snd_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3531_; 
v_fst_3495_ = lean_ctor_get(v_snd_3491_, 0);
v_snd_3496_ = lean_ctor_get(v_snd_3491_, 1);
v_isSharedCheck_3531_ = !lean_is_exclusive(v_snd_3491_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3498_ = v_snd_3491_;
v_isShared_3499_ = v_isSharedCheck_3531_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_snd_3496_);
lean_inc(v_fst_3495_);
lean_dec(v_snd_3491_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3531_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v_a_3500_; lean_object* v_p_3501_; lean_object* v___x_3502_; lean_object* v_a_3504_; lean_object* v_b_3511_; lean_object* v___x_3512_; uint8_t v___x_3513_; 
v_a_3500_ = lean_array_uget(v_as_3486_, v_i_3488_);
v_p_3501_ = lean_ctor_get(v_a_3500_, 0);
v___x_3502_ = lean_box(0);
v_b_3511_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3501_, v_x_3485_);
v___x_3512_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3513_ = lean_int_dec_eq(v_b_3511_, v___x_3512_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3515_; 
lean_inc(v_a_3500_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 1, v_a_3500_);
lean_ctor_set(v___x_3493_, 0, v_b_3511_);
v___x_3515_ = v___x_3493_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_b_3511_);
lean_ctor_set(v_reuseFailAlloc_3526_, 1, v_a_3500_);
v___x_3515_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3523_; 
v_isSharedCheck_3523_ = !lean_is_exclusive(v_a_3500_);
if (v_isSharedCheck_3523_ == 0)
{
lean_object* v_unused_3524_; lean_object* v_unused_3525_; 
v_unused_3524_ = lean_ctor_get(v_a_3500_, 1);
lean_dec(v_unused_3524_);
v_unused_3525_ = lean_ctor_get(v_a_3500_, 0);
lean_dec(v_unused_3525_);
v___x_3517_ = v_a_3500_;
v_isShared_3518_ = v_isSharedCheck_3523_;
goto v_resetjp_3516_;
}
else
{
lean_dec(v_a_3500_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3523_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v_todo_3519_; lean_object* v___x_3521_; 
v_todo_3519_ = lean_array_push(v_snd_3496_, v___x_3515_);
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 1, v_todo_3519_);
lean_ctor_set(v___x_3517_, 0, v_fst_3495_);
v___x_3521_ = v___x_3517_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_fst_3495_);
lean_ctor_set(v_reuseFailAlloc_3522_, 1, v_todo_3519_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
v_a_3504_ = v___x_3521_;
goto v___jp_3503_;
}
}
}
}
else
{
lean_object* v_cs_x27_3527_; lean_object* v___x_3529_; 
lean_dec(v_b_3511_);
v_cs_x27_3527_ = l_Lean_PersistentArray_push___redArg(v_fst_3495_, v_a_3500_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 1, v_snd_3496_);
lean_ctor_set(v___x_3493_, 0, v_cs_x27_3527_);
v___x_3529_ = v___x_3493_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_cs_x27_3527_);
lean_ctor_set(v_reuseFailAlloc_3530_, 1, v_snd_3496_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
v_a_3504_ = v___x_3529_;
goto v___jp_3503_;
}
}
v___jp_3503_:
{
lean_object* v___x_3506_; 
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 1, v_a_3504_);
lean_ctor_set(v___x_3498_, 0, v___x_3502_);
v___x_3506_ = v___x_3498_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3502_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v_a_3504_);
v___x_3506_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
size_t v___x_3507_; size_t v___x_3508_; 
v___x_3507_ = ((size_t)1ULL);
v___x_3508_ = lean_usize_add(v_i_3488_, v___x_3507_);
v_i_3488_ = v___x_3508_;
v_b_3489_ = v___x_3506_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3534_, lean_object* v_as_3535_, lean_object* v_sz_3536_, lean_object* v_i_3537_, lean_object* v_b_3538_){
_start:
{
size_t v_sz_boxed_3539_; size_t v_i_boxed_3540_; lean_object* v_res_3541_; 
v_sz_boxed_3539_ = lean_unbox_usize(v_sz_3536_);
lean_dec(v_sz_3536_);
v_i_boxed_3540_ = lean_unbox_usize(v_i_3537_);
lean_dec(v_i_3537_);
v_res_3541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3534_, v_as_3535_, v_sz_boxed_3539_, v_i_boxed_3540_, v_b_3538_);
lean_dec_ref(v_as_3535_);
lean_dec(v_x_3534_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_3542_, lean_object* v_as_3543_, size_t v_sz_3544_, size_t v_i_3545_, lean_object* v_b_3546_){
_start:
{
uint8_t v___x_3547_; 
v___x_3547_ = lean_usize_dec_lt(v_i_3545_, v_sz_3544_);
if (v___x_3547_ == 0)
{
return v_b_3546_;
}
else
{
lean_object* v_snd_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3589_; 
v_snd_3548_ = lean_ctor_get(v_b_3546_, 1);
v_isSharedCheck_3589_ = !lean_is_exclusive(v_b_3546_);
if (v_isSharedCheck_3589_ == 0)
{
lean_object* v_unused_3590_; 
v_unused_3590_ = lean_ctor_get(v_b_3546_, 0);
lean_dec(v_unused_3590_);
v___x_3550_ = v_b_3546_;
v_isShared_3551_ = v_isSharedCheck_3589_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_snd_3548_);
lean_dec(v_b_3546_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3589_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v_fst_3552_; lean_object* v_snd_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3588_; 
v_fst_3552_ = lean_ctor_get(v_snd_3548_, 0);
v_snd_3553_ = lean_ctor_get(v_snd_3548_, 1);
v_isSharedCheck_3588_ = !lean_is_exclusive(v_snd_3548_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3555_ = v_snd_3548_;
v_isShared_3556_ = v_isSharedCheck_3588_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_snd_3553_);
lean_inc(v_fst_3552_);
lean_dec(v_snd_3548_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3588_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v_a_3557_; lean_object* v_p_3558_; lean_object* v___x_3559_; lean_object* v_a_3561_; lean_object* v_b_3568_; lean_object* v___x_3569_; uint8_t v___x_3570_; 
v_a_3557_ = lean_array_uget(v_as_3543_, v_i_3545_);
v_p_3558_ = lean_ctor_get(v_a_3557_, 0);
v___x_3559_ = lean_box(0);
v_b_3568_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3558_, v_x_3542_);
v___x_3569_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3570_ = lean_int_dec_eq(v_b_3568_, v___x_3569_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3572_; 
lean_inc(v_a_3557_);
if (v_isShared_3551_ == 0)
{
lean_ctor_set(v___x_3550_, 1, v_a_3557_);
lean_ctor_set(v___x_3550_, 0, v_b_3568_);
v___x_3572_ = v___x_3550_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_b_3568_);
lean_ctor_set(v_reuseFailAlloc_3583_, 1, v_a_3557_);
v___x_3572_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3580_; 
v_isSharedCheck_3580_ = !lean_is_exclusive(v_a_3557_);
if (v_isSharedCheck_3580_ == 0)
{
lean_object* v_unused_3581_; lean_object* v_unused_3582_; 
v_unused_3581_ = lean_ctor_get(v_a_3557_, 1);
lean_dec(v_unused_3581_);
v_unused_3582_ = lean_ctor_get(v_a_3557_, 0);
lean_dec(v_unused_3582_);
v___x_3574_ = v_a_3557_;
v_isShared_3575_ = v_isSharedCheck_3580_;
goto v_resetjp_3573_;
}
else
{
lean_dec(v_a_3557_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3580_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v_todo_3576_; lean_object* v___x_3578_; 
v_todo_3576_ = lean_array_push(v_snd_3553_, v___x_3572_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 1, v_todo_3576_);
lean_ctor_set(v___x_3574_, 0, v_fst_3552_);
v___x_3578_ = v___x_3574_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_fst_3552_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_todo_3576_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
v_a_3561_ = v___x_3578_;
goto v___jp_3560_;
}
}
}
}
else
{
lean_object* v_cs_x27_3584_; lean_object* v___x_3586_; 
lean_dec(v_b_3568_);
v_cs_x27_3584_ = l_Lean_PersistentArray_push___redArg(v_fst_3552_, v_a_3557_);
if (v_isShared_3551_ == 0)
{
lean_ctor_set(v___x_3550_, 1, v_snd_3553_);
lean_ctor_set(v___x_3550_, 0, v_cs_x27_3584_);
v___x_3586_ = v___x_3550_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_cs_x27_3584_);
lean_ctor_set(v_reuseFailAlloc_3587_, 1, v_snd_3553_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
v_a_3561_ = v___x_3586_;
goto v___jp_3560_;
}
}
v___jp_3560_:
{
lean_object* v___x_3563_; 
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 1, v_a_3561_);
lean_ctor_set(v___x_3555_, 0, v___x_3559_);
v___x_3563_ = v___x_3555_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3559_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v_a_3561_);
v___x_3563_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
size_t v___x_3564_; size_t v___x_3565_; lean_object* v___x_3566_; 
v___x_3564_ = ((size_t)1ULL);
v___x_3565_ = lean_usize_add(v_i_3545_, v___x_3564_);
v___x_3566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3542_, v_as_3543_, v_sz_3544_, v___x_3565_, v___x_3563_);
return v___x_3566_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_3591_, lean_object* v_as_3592_, lean_object* v_sz_3593_, lean_object* v_i_3594_, lean_object* v_b_3595_){
_start:
{
size_t v_sz_boxed_3596_; size_t v_i_boxed_3597_; lean_object* v_res_3598_; 
v_sz_boxed_3596_ = lean_unbox_usize(v_sz_3593_);
lean_dec(v_sz_3593_);
v_i_boxed_3597_ = lean_unbox_usize(v_i_3594_);
lean_dec(v_i_3594_);
v_res_3598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3591_, v_as_3592_, v_sz_boxed_3596_, v_i_boxed_3597_, v_b_3595_);
lean_dec_ref(v_as_3592_);
lean_dec(v_x_3591_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(lean_object* v_x_3599_, lean_object* v_inh_3600_, lean_object* v_n_3601_, lean_object* v_b_3602_){
_start:
{
if (lean_obj_tag(v_n_3601_) == 0)
{
lean_object* v_cs_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3618_; 
v_cs_3603_ = lean_ctor_get(v_n_3601_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v_n_3601_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3605_ = v_n_3601_;
v_isShared_3606_ = v_isSharedCheck_3618_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_cs_3603_);
lean_dec(v_n_3601_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3618_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; size_t v_sz_3609_; size_t v___x_3610_; lean_object* v___x_3611_; lean_object* v_fst_3612_; 
v___x_3607_ = lean_box(0);
v___x_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
lean_ctor_set(v___x_3608_, 1, v_b_3602_);
v_sz_3609_ = lean_array_size(v_cs_3603_);
v___x_3610_ = ((size_t)0ULL);
v___x_3611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_x_3599_, v_inh_3600_, v_cs_3603_, v_sz_3609_, v___x_3610_, v___x_3608_);
lean_dec_ref(v_cs_3603_);
v_fst_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_fst_3612_);
if (lean_obj_tag(v_fst_3612_) == 0)
{
lean_object* v_snd_3613_; lean_object* v___x_3615_; 
v_snd_3613_ = lean_ctor_get(v___x_3611_, 1);
lean_inc(v_snd_3613_);
lean_dec_ref(v___x_3611_);
if (v_isShared_3606_ == 0)
{
lean_ctor_set_tag(v___x_3605_, 1);
lean_ctor_set(v___x_3605_, 0, v_snd_3613_);
v___x_3615_ = v___x_3605_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_snd_3613_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
else
{
lean_object* v_val_3617_; 
lean_dec_ref(v___x_3611_);
lean_del_object(v___x_3605_);
v_val_3617_ = lean_ctor_get(v_fst_3612_, 0);
lean_inc(v_val_3617_);
lean_dec_ref(v_fst_3612_);
return v_val_3617_;
}
}
}
else
{
lean_object* v_vs_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3634_; 
v_vs_3619_ = lean_ctor_get(v_n_3601_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v_n_3601_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3621_ = v_n_3601_;
v_isShared_3622_ = v_isSharedCheck_3634_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_vs_3619_);
lean_dec(v_n_3601_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3634_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; size_t v_sz_3625_; size_t v___x_3626_; lean_object* v___x_3627_; lean_object* v_fst_3628_; 
v___x_3623_ = lean_box(0);
v___x_3624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3623_);
lean_ctor_set(v___x_3624_, 1, v_b_3602_);
v_sz_3625_ = lean_array_size(v_vs_3619_);
v___x_3626_ = ((size_t)0ULL);
v___x_3627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3599_, v_vs_3619_, v_sz_3625_, v___x_3626_, v___x_3624_);
lean_dec_ref(v_vs_3619_);
v_fst_3628_ = lean_ctor_get(v___x_3627_, 0);
lean_inc(v_fst_3628_);
if (lean_obj_tag(v_fst_3628_) == 0)
{
lean_object* v_snd_3629_; lean_object* v___x_3631_; 
v_snd_3629_ = lean_ctor_get(v___x_3627_, 1);
lean_inc(v_snd_3629_);
lean_dec_ref(v___x_3627_);
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 0, v_snd_3629_);
v___x_3631_ = v___x_3621_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_snd_3629_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
else
{
lean_object* v_val_3633_; 
lean_dec_ref(v___x_3627_);
lean_del_object(v___x_3621_);
v_val_3633_ = lean_ctor_get(v_fst_3628_, 0);
lean_inc(v_val_3633_);
lean_dec_ref(v_fst_3628_);
return v_val_3633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_3635_, lean_object* v_inh_3636_, lean_object* v_as_3637_, size_t v_sz_3638_, size_t v_i_3639_, lean_object* v_b_3640_){
_start:
{
uint8_t v___x_3641_; 
v___x_3641_ = lean_usize_dec_lt(v_i_3639_, v_sz_3638_);
if (v___x_3641_ == 0)
{
return v_b_3640_;
}
else
{
lean_object* v_snd_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3660_; 
v_snd_3642_ = lean_ctor_get(v_b_3640_, 1);
v_isSharedCheck_3660_ = !lean_is_exclusive(v_b_3640_);
if (v_isSharedCheck_3660_ == 0)
{
lean_object* v_unused_3661_; 
v_unused_3661_ = lean_ctor_get(v_b_3640_, 0);
lean_dec(v_unused_3661_);
v___x_3644_ = v_b_3640_;
v_isShared_3645_ = v_isSharedCheck_3660_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_snd_3642_);
lean_dec(v_b_3640_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3660_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v_a_3646_; lean_object* v___x_3647_; 
v_a_3646_ = lean_array_uget_borrowed(v_as_3637_, v_i_3639_);
lean_inc(v_snd_3642_);
lean_inc(v_a_3646_);
v___x_3647_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_x_3635_, v_inh_3636_, v_a_3646_, v_snd_3642_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v___x_3648_; lean_object* v___x_3650_; 
v___x_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3647_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v___x_3648_);
v___x_3650_ = v___x_3644_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3648_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v_snd_3642_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
else
{
lean_object* v_a_3652_; lean_object* v___x_3653_; lean_object* v___x_3655_; 
lean_dec(v_snd_3642_);
v_a_3652_ = lean_ctor_get(v___x_3647_, 0);
lean_inc(v_a_3652_);
lean_dec_ref(v___x_3647_);
v___x_3653_ = lean_box(0);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 1, v_a_3652_);
lean_ctor_set(v___x_3644_, 0, v___x_3653_);
v___x_3655_ = v___x_3644_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3653_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v_a_3652_);
v___x_3655_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
size_t v___x_3656_; size_t v___x_3657_; 
v___x_3656_ = ((size_t)1ULL);
v___x_3657_ = lean_usize_add(v_i_3639_, v___x_3656_);
v_i_3639_ = v___x_3657_;
v_b_3640_ = v___x_3655_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_x_3662_, lean_object* v_inh_3663_, lean_object* v_as_3664_, lean_object* v_sz_3665_, lean_object* v_i_3666_, lean_object* v_b_3667_){
_start:
{
size_t v_sz_boxed_3668_; size_t v_i_boxed_3669_; lean_object* v_res_3670_; 
v_sz_boxed_3668_ = lean_unbox_usize(v_sz_3665_);
lean_dec(v_sz_3665_);
v_i_boxed_3669_ = lean_unbox_usize(v_i_3666_);
lean_dec(v_i_3666_);
v_res_3670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_x_3662_, v_inh_3663_, v_as_3664_, v_sz_boxed_3668_, v_i_boxed_3669_, v_b_3667_);
lean_dec_ref(v_as_3664_);
lean_dec_ref(v_inh_3663_);
lean_dec(v_x_3662_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3671_, lean_object* v_inh_3672_, lean_object* v_n_3673_, lean_object* v_b_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_x_3671_, v_inh_3672_, v_n_3673_, v_b_3674_);
lean_dec_ref(v_inh_3672_);
lean_dec(v_x_3671_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object* v_x_3676_, lean_object* v_t_3677_, lean_object* v_init_3678_){
_start:
{
lean_object* v_root_3679_; lean_object* v_tail_3680_; lean_object* v___x_3681_; 
v_root_3679_ = lean_ctor_get(v_t_3677_, 0);
lean_inc_ref(v_root_3679_);
v_tail_3680_ = lean_ctor_get(v_t_3677_, 1);
lean_inc_ref(v_tail_3680_);
lean_dec_ref(v_t_3677_);
lean_inc_ref(v_init_3678_);
v___x_3681_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_x_3676_, v_init_3678_, v_root_3679_, v_init_3678_);
lean_dec_ref(v_init_3678_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v_a_3682_; 
lean_dec_ref(v_tail_3680_);
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_a_3682_);
lean_dec_ref(v___x_3681_);
return v_a_3682_;
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; size_t v_sz_3686_; size_t v___x_3687_; lean_object* v___x_3688_; lean_object* v_fst_3689_; 
v_a_3683_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_a_3683_);
lean_dec_ref(v___x_3681_);
v___x_3684_ = lean_box(0);
v___x_3685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3684_);
lean_ctor_set(v___x_3685_, 1, v_a_3683_);
v_sz_3686_ = lean_array_size(v_tail_3680_);
v___x_3687_ = ((size_t)0ULL);
v___x_3688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3676_, v_tail_3680_, v_sz_3686_, v___x_3687_, v___x_3685_);
lean_dec_ref(v_tail_3680_);
v_fst_3689_ = lean_ctor_get(v___x_3688_, 0);
lean_inc(v_fst_3689_);
if (lean_obj_tag(v_fst_3689_) == 0)
{
lean_object* v_snd_3690_; 
v_snd_3690_ = lean_ctor_get(v___x_3688_, 1);
lean_inc(v_snd_3690_);
lean_dec_ref(v___x_3688_);
return v_snd_3690_;
}
else
{
lean_object* v_val_3691_; 
lean_dec_ref(v___x_3688_);
v_val_3691_ = lean_ctor_get(v_fst_3689_, 0);
lean_inc(v_val_3691_);
lean_dec_ref(v_fst_3689_);
return v_val_3691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object* v_x_3692_, lean_object* v_t_3693_, lean_object* v_init_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3692_, v_t_3693_, v_init_3694_);
lean_dec(v_x_3692_);
return v_res_3695_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3696_ = lean_unsigned_to_nat(32u);
v___x_3697_ = lean_mk_empty_array_with_capacity(v___x_3696_);
v___x_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3697_);
return v___x_3698_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1(void){
_start:
{
size_t v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v_cs_x27_3704_; 
v___x_3699_ = ((size_t)5ULL);
v___x_3700_ = lean_unsigned_to_nat(0u);
v___x_3701_ = lean_unsigned_to_nat(32u);
v___x_3702_ = lean_mk_empty_array_with_capacity(v___x_3701_);
v___x_3703_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0);
v_cs_x27_3704_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_3704_, 0, v___x_3703_);
lean_ctor_set(v_cs_x27_3704_, 1, v___x_3702_);
lean_ctor_set(v_cs_x27_3704_, 2, v___x_3700_);
lean_ctor_set(v_cs_x27_3704_, 3, v___x_3700_);
lean_ctor_set_usize(v_cs_x27_3704_, 4, v___x_3699_);
return v_cs_x27_3704_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_3707_; lean_object* v_cs_x27_3708_; lean_object* v___x_3709_; 
v_todo_3707_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2));
v_cs_x27_3708_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1);
v___x_3709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3709_, 0, v_cs_x27_3708_);
lean_ctor_set(v___x_3709_, 1, v_todo_3707_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object* v_x_3710_, lean_object* v_cs_3711_){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v_fst_3714_; lean_object* v_snd_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
v___x_3712_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3);
v___x_3713_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3710_, v_cs_3711_, v___x_3712_);
v_fst_3714_ = lean_ctor_get(v___x_3713_, 0);
v_snd_3715_ = lean_ctor_get(v___x_3713_, 1);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3713_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_snd_3715_);
lean_inc(v_fst_3714_);
lean_dec(v___x_3713_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_fst_3714_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v_snd_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object* v_x_3723_, lean_object* v_cs_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3723_, v_cs_3724_);
lean_dec(v_x_3723_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object* v_x_3726_, lean_object* v_cs_3727_){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3726_, v_cs_3727_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object* v_x_3729_, lean_object* v_cs_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(v_x_3729_, v_cs_3730_);
lean_dec(v_x_3729_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(lean_object* v_a_3732_, lean_object* v_y_3733_, lean_object* v_fst_3734_, lean_object* v_s_3735_){
_start:
{
lean_object* v_structs_3736_; lean_object* v_typeIdOf_3737_; lean_object* v_exprToStructId_3738_; lean_object* v_exprToStructIdEntries_3739_; lean_object* v_forbiddenNatModules_3740_; lean_object* v_natStructs_3741_; lean_object* v_natTypeIdOf_3742_; lean_object* v_exprToNatStructId_3743_; lean_object* v___x_3744_; uint8_t v___x_3745_; 
v_structs_3736_ = lean_ctor_get(v_s_3735_, 0);
v_typeIdOf_3737_ = lean_ctor_get(v_s_3735_, 1);
v_exprToStructId_3738_ = lean_ctor_get(v_s_3735_, 2);
v_exprToStructIdEntries_3739_ = lean_ctor_get(v_s_3735_, 3);
v_forbiddenNatModules_3740_ = lean_ctor_get(v_s_3735_, 4);
v_natStructs_3741_ = lean_ctor_get(v_s_3735_, 5);
v_natTypeIdOf_3742_ = lean_ctor_get(v_s_3735_, 6);
v_exprToNatStructId_3743_ = lean_ctor_get(v_s_3735_, 7);
v___x_3744_ = lean_array_get_size(v_structs_3736_);
v___x_3745_ = lean_nat_dec_lt(v_a_3732_, v___x_3744_);
if (v___x_3745_ == 0)
{
lean_dec_ref(v_fst_3734_);
return v_s_3735_;
}
else
{
lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3807_; 
lean_inc_ref(v_exprToNatStructId_3743_);
lean_inc_ref(v_natTypeIdOf_3742_);
lean_inc_ref(v_natStructs_3741_);
lean_inc_ref(v_forbiddenNatModules_3740_);
lean_inc_ref(v_exprToStructIdEntries_3739_);
lean_inc_ref(v_exprToStructId_3738_);
lean_inc_ref(v_typeIdOf_3737_);
lean_inc_ref(v_structs_3736_);
v_isSharedCheck_3807_ = !lean_is_exclusive(v_s_3735_);
if (v_isSharedCheck_3807_ == 0)
{
lean_object* v_unused_3808_; lean_object* v_unused_3809_; lean_object* v_unused_3810_; lean_object* v_unused_3811_; lean_object* v_unused_3812_; lean_object* v_unused_3813_; lean_object* v_unused_3814_; lean_object* v_unused_3815_; 
v_unused_3808_ = lean_ctor_get(v_s_3735_, 7);
lean_dec(v_unused_3808_);
v_unused_3809_ = lean_ctor_get(v_s_3735_, 6);
lean_dec(v_unused_3809_);
v_unused_3810_ = lean_ctor_get(v_s_3735_, 5);
lean_dec(v_unused_3810_);
v_unused_3811_ = lean_ctor_get(v_s_3735_, 4);
lean_dec(v_unused_3811_);
v_unused_3812_ = lean_ctor_get(v_s_3735_, 3);
lean_dec(v_unused_3812_);
v_unused_3813_ = lean_ctor_get(v_s_3735_, 2);
lean_dec(v_unused_3813_);
v_unused_3814_ = lean_ctor_get(v_s_3735_, 1);
lean_dec(v_unused_3814_);
v_unused_3815_ = lean_ctor_get(v_s_3735_, 0);
lean_dec(v_unused_3815_);
v___x_3747_ = v_s_3735_;
v_isShared_3748_ = v_isSharedCheck_3807_;
goto v_resetjp_3746_;
}
else
{
lean_dec(v_s_3735_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3807_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v_v_3749_; lean_object* v_id_3750_; lean_object* v_ringId_x3f_3751_; lean_object* v_type_3752_; lean_object* v_u_3753_; lean_object* v_intModuleInst_3754_; lean_object* v_leInst_x3f_3755_; lean_object* v_ltInst_x3f_3756_; lean_object* v_lawfulOrderLTInst_x3f_3757_; lean_object* v_isPreorderInst_x3f_3758_; lean_object* v_orderedAddInst_x3f_3759_; lean_object* v_isLinearInst_x3f_3760_; lean_object* v_noNatDivInst_x3f_3761_; lean_object* v_ringInst_x3f_3762_; lean_object* v_commRingInst_x3f_3763_; lean_object* v_orderedRingInst_x3f_3764_; lean_object* v_fieldInst_x3f_3765_; lean_object* v_charInst_x3f_3766_; lean_object* v_zero_3767_; lean_object* v_ofNatZero_3768_; lean_object* v_one_x3f_3769_; lean_object* v_leFn_x3f_3770_; lean_object* v_ltFn_x3f_3771_; lean_object* v_addFn_3772_; lean_object* v_zsmulFn_3773_; lean_object* v_nsmulFn_3774_; lean_object* v_zsmulFn_x3f_3775_; lean_object* v_nsmulFn_x3f_3776_; lean_object* v_homomulFn_x3f_3777_; lean_object* v_subFn_3778_; lean_object* v_negFn_3779_; lean_object* v_vars_3780_; lean_object* v_varMap_3781_; lean_object* v_lowers_3782_; lean_object* v_uppers_3783_; lean_object* v_diseqs_3784_; lean_object* v_assignment_3785_; uint8_t v_caseSplits_3786_; lean_object* v_conflict_x3f_3787_; lean_object* v_diseqSplits_3788_; lean_object* v_elimEqs_3789_; lean_object* v_elimStack_3790_; lean_object* v_occurs_3791_; lean_object* v_ignored_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3806_; 
v_v_3749_ = lean_array_fget(v_structs_3736_, v_a_3732_);
v_id_3750_ = lean_ctor_get(v_v_3749_, 0);
v_ringId_x3f_3751_ = lean_ctor_get(v_v_3749_, 1);
v_type_3752_ = lean_ctor_get(v_v_3749_, 2);
v_u_3753_ = lean_ctor_get(v_v_3749_, 3);
v_intModuleInst_3754_ = lean_ctor_get(v_v_3749_, 4);
v_leInst_x3f_3755_ = lean_ctor_get(v_v_3749_, 5);
v_ltInst_x3f_3756_ = lean_ctor_get(v_v_3749_, 6);
v_lawfulOrderLTInst_x3f_3757_ = lean_ctor_get(v_v_3749_, 7);
v_isPreorderInst_x3f_3758_ = lean_ctor_get(v_v_3749_, 8);
v_orderedAddInst_x3f_3759_ = lean_ctor_get(v_v_3749_, 9);
v_isLinearInst_x3f_3760_ = lean_ctor_get(v_v_3749_, 10);
v_noNatDivInst_x3f_3761_ = lean_ctor_get(v_v_3749_, 11);
v_ringInst_x3f_3762_ = lean_ctor_get(v_v_3749_, 12);
v_commRingInst_x3f_3763_ = lean_ctor_get(v_v_3749_, 13);
v_orderedRingInst_x3f_3764_ = lean_ctor_get(v_v_3749_, 14);
v_fieldInst_x3f_3765_ = lean_ctor_get(v_v_3749_, 15);
v_charInst_x3f_3766_ = lean_ctor_get(v_v_3749_, 16);
v_zero_3767_ = lean_ctor_get(v_v_3749_, 17);
v_ofNatZero_3768_ = lean_ctor_get(v_v_3749_, 18);
v_one_x3f_3769_ = lean_ctor_get(v_v_3749_, 19);
v_leFn_x3f_3770_ = lean_ctor_get(v_v_3749_, 20);
v_ltFn_x3f_3771_ = lean_ctor_get(v_v_3749_, 21);
v_addFn_3772_ = lean_ctor_get(v_v_3749_, 22);
v_zsmulFn_3773_ = lean_ctor_get(v_v_3749_, 23);
v_nsmulFn_3774_ = lean_ctor_get(v_v_3749_, 24);
v_zsmulFn_x3f_3775_ = lean_ctor_get(v_v_3749_, 25);
v_nsmulFn_x3f_3776_ = lean_ctor_get(v_v_3749_, 26);
v_homomulFn_x3f_3777_ = lean_ctor_get(v_v_3749_, 27);
v_subFn_3778_ = lean_ctor_get(v_v_3749_, 28);
v_negFn_3779_ = lean_ctor_get(v_v_3749_, 29);
v_vars_3780_ = lean_ctor_get(v_v_3749_, 30);
v_varMap_3781_ = lean_ctor_get(v_v_3749_, 31);
v_lowers_3782_ = lean_ctor_get(v_v_3749_, 32);
v_uppers_3783_ = lean_ctor_get(v_v_3749_, 33);
v_diseqs_3784_ = lean_ctor_get(v_v_3749_, 34);
v_assignment_3785_ = lean_ctor_get(v_v_3749_, 35);
v_caseSplits_3786_ = lean_ctor_get_uint8(v_v_3749_, sizeof(void*)*42);
v_conflict_x3f_3787_ = lean_ctor_get(v_v_3749_, 36);
v_diseqSplits_3788_ = lean_ctor_get(v_v_3749_, 37);
v_elimEqs_3789_ = lean_ctor_get(v_v_3749_, 38);
v_elimStack_3790_ = lean_ctor_get(v_v_3749_, 39);
v_occurs_3791_ = lean_ctor_get(v_v_3749_, 40);
v_ignored_3792_ = lean_ctor_get(v_v_3749_, 41);
v_isSharedCheck_3806_ = !lean_is_exclusive(v_v_3749_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3794_ = v_v_3749_;
v_isShared_3795_ = v_isSharedCheck_3806_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_ignored_3792_);
lean_inc(v_occurs_3791_);
lean_inc(v_elimStack_3790_);
lean_inc(v_elimEqs_3789_);
lean_inc(v_diseqSplits_3788_);
lean_inc(v_conflict_x3f_3787_);
lean_inc(v_assignment_3785_);
lean_inc(v_diseqs_3784_);
lean_inc(v_uppers_3783_);
lean_inc(v_lowers_3782_);
lean_inc(v_varMap_3781_);
lean_inc(v_vars_3780_);
lean_inc(v_negFn_3779_);
lean_inc(v_subFn_3778_);
lean_inc(v_homomulFn_x3f_3777_);
lean_inc(v_nsmulFn_x3f_3776_);
lean_inc(v_zsmulFn_x3f_3775_);
lean_inc(v_nsmulFn_3774_);
lean_inc(v_zsmulFn_3773_);
lean_inc(v_addFn_3772_);
lean_inc(v_ltFn_x3f_3771_);
lean_inc(v_leFn_x3f_3770_);
lean_inc(v_one_x3f_3769_);
lean_inc(v_ofNatZero_3768_);
lean_inc(v_zero_3767_);
lean_inc(v_charInst_x3f_3766_);
lean_inc(v_fieldInst_x3f_3765_);
lean_inc(v_orderedRingInst_x3f_3764_);
lean_inc(v_commRingInst_x3f_3763_);
lean_inc(v_ringInst_x3f_3762_);
lean_inc(v_noNatDivInst_x3f_3761_);
lean_inc(v_isLinearInst_x3f_3760_);
lean_inc(v_orderedAddInst_x3f_3759_);
lean_inc(v_isPreorderInst_x3f_3758_);
lean_inc(v_lawfulOrderLTInst_x3f_3757_);
lean_inc(v_ltInst_x3f_3756_);
lean_inc(v_leInst_x3f_3755_);
lean_inc(v_intModuleInst_3754_);
lean_inc(v_u_3753_);
lean_inc(v_type_3752_);
lean_inc(v_ringId_x3f_3751_);
lean_inc(v_id_3750_);
lean_dec(v_v_3749_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3806_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3796_; lean_object* v_xs_x27_3797_; lean_object* v___x_3798_; lean_object* v___x_3800_; 
v___x_3796_ = lean_box(0);
v_xs_x27_3797_ = lean_array_fset(v_structs_3736_, v_a_3732_, v___x_3796_);
v___x_3798_ = l_Lean_PersistentArray_set___redArg(v_diseqs_3784_, v_y_3733_, v_fst_3734_);
if (v_isShared_3795_ == 0)
{
lean_ctor_set(v___x_3794_, 34, v___x_3798_);
v___x_3800_ = v___x_3794_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_id_3750_);
lean_ctor_set(v_reuseFailAlloc_3805_, 1, v_ringId_x3f_3751_);
lean_ctor_set(v_reuseFailAlloc_3805_, 2, v_type_3752_);
lean_ctor_set(v_reuseFailAlloc_3805_, 3, v_u_3753_);
lean_ctor_set(v_reuseFailAlloc_3805_, 4, v_intModuleInst_3754_);
lean_ctor_set(v_reuseFailAlloc_3805_, 5, v_leInst_x3f_3755_);
lean_ctor_set(v_reuseFailAlloc_3805_, 6, v_ltInst_x3f_3756_);
lean_ctor_set(v_reuseFailAlloc_3805_, 7, v_lawfulOrderLTInst_x3f_3757_);
lean_ctor_set(v_reuseFailAlloc_3805_, 8, v_isPreorderInst_x3f_3758_);
lean_ctor_set(v_reuseFailAlloc_3805_, 9, v_orderedAddInst_x3f_3759_);
lean_ctor_set(v_reuseFailAlloc_3805_, 10, v_isLinearInst_x3f_3760_);
lean_ctor_set(v_reuseFailAlloc_3805_, 11, v_noNatDivInst_x3f_3761_);
lean_ctor_set(v_reuseFailAlloc_3805_, 12, v_ringInst_x3f_3762_);
lean_ctor_set(v_reuseFailAlloc_3805_, 13, v_commRingInst_x3f_3763_);
lean_ctor_set(v_reuseFailAlloc_3805_, 14, v_orderedRingInst_x3f_3764_);
lean_ctor_set(v_reuseFailAlloc_3805_, 15, v_fieldInst_x3f_3765_);
lean_ctor_set(v_reuseFailAlloc_3805_, 16, v_charInst_x3f_3766_);
lean_ctor_set(v_reuseFailAlloc_3805_, 17, v_zero_3767_);
lean_ctor_set(v_reuseFailAlloc_3805_, 18, v_ofNatZero_3768_);
lean_ctor_set(v_reuseFailAlloc_3805_, 19, v_one_x3f_3769_);
lean_ctor_set(v_reuseFailAlloc_3805_, 20, v_leFn_x3f_3770_);
lean_ctor_set(v_reuseFailAlloc_3805_, 21, v_ltFn_x3f_3771_);
lean_ctor_set(v_reuseFailAlloc_3805_, 22, v_addFn_3772_);
lean_ctor_set(v_reuseFailAlloc_3805_, 23, v_zsmulFn_3773_);
lean_ctor_set(v_reuseFailAlloc_3805_, 24, v_nsmulFn_3774_);
lean_ctor_set(v_reuseFailAlloc_3805_, 25, v_zsmulFn_x3f_3775_);
lean_ctor_set(v_reuseFailAlloc_3805_, 26, v_nsmulFn_x3f_3776_);
lean_ctor_set(v_reuseFailAlloc_3805_, 27, v_homomulFn_x3f_3777_);
lean_ctor_set(v_reuseFailAlloc_3805_, 28, v_subFn_3778_);
lean_ctor_set(v_reuseFailAlloc_3805_, 29, v_negFn_3779_);
lean_ctor_set(v_reuseFailAlloc_3805_, 30, v_vars_3780_);
lean_ctor_set(v_reuseFailAlloc_3805_, 31, v_varMap_3781_);
lean_ctor_set(v_reuseFailAlloc_3805_, 32, v_lowers_3782_);
lean_ctor_set(v_reuseFailAlloc_3805_, 33, v_uppers_3783_);
lean_ctor_set(v_reuseFailAlloc_3805_, 34, v___x_3798_);
lean_ctor_set(v_reuseFailAlloc_3805_, 35, v_assignment_3785_);
lean_ctor_set(v_reuseFailAlloc_3805_, 36, v_conflict_x3f_3787_);
lean_ctor_set(v_reuseFailAlloc_3805_, 37, v_diseqSplits_3788_);
lean_ctor_set(v_reuseFailAlloc_3805_, 38, v_elimEqs_3789_);
lean_ctor_set(v_reuseFailAlloc_3805_, 39, v_elimStack_3790_);
lean_ctor_set(v_reuseFailAlloc_3805_, 40, v_occurs_3791_);
lean_ctor_set(v_reuseFailAlloc_3805_, 41, v_ignored_3792_);
lean_ctor_set_uint8(v_reuseFailAlloc_3805_, sizeof(void*)*42, v_caseSplits_3786_);
v___x_3800_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
lean_object* v___x_3801_; lean_object* v___x_3803_; 
v___x_3801_ = lean_array_fset(v_xs_x27_3797_, v_a_3732_, v___x_3800_);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 0, v___x_3801_);
v___x_3803_ = v___x_3747_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3801_);
lean_ctor_set(v_reuseFailAlloc_3804_, 1, v_typeIdOf_3737_);
lean_ctor_set(v_reuseFailAlloc_3804_, 2, v_exprToStructId_3738_);
lean_ctor_set(v_reuseFailAlloc_3804_, 3, v_exprToStructIdEntries_3739_);
lean_ctor_set(v_reuseFailAlloc_3804_, 4, v_forbiddenNatModules_3740_);
lean_ctor_set(v_reuseFailAlloc_3804_, 5, v_natStructs_3741_);
lean_ctor_set(v_reuseFailAlloc_3804_, 6, v_natTypeIdOf_3742_);
lean_ctor_set(v_reuseFailAlloc_3804_, 7, v_exprToNatStructId_3743_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed(lean_object* v_a_3816_, lean_object* v_y_3817_, lean_object* v_fst_3818_, lean_object* v_s_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(v_a_3816_, v_y_3817_, v_fst_3818_, v_s_3819_);
lean_dec(v_y_3817_);
lean_dec(v_a_3816_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object* v_a_3821_, lean_object* v_x_3822_, lean_object* v_c_3823_, lean_object* v_as_3824_, size_t v_sz_3825_, size_t v_i_3826_, lean_object* v_b_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v_a_3841_; uint8_t v___x_3845_; 
v___x_3845_ = lean_usize_dec_lt(v_i_3826_, v_sz_3825_);
if (v___x_3845_ == 0)
{
lean_object* v___x_3846_; 
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec_ref(v_c_3823_);
v___x_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3846_, 0, v_b_3827_);
return v___x_3846_;
}
else
{
lean_object* v_a_3847_; lean_object* v_fst_3848_; lean_object* v_snd_3849_; lean_object* v___x_3850_; 
lean_dec_ref(v_b_3827_);
v_a_3847_ = lean_array_uget_borrowed(v_as_3824_, v_i_3826_);
v_fst_3848_ = lean_ctor_get(v_a_3847_, 0);
v_snd_3849_ = lean_ctor_get(v_a_3847_, 1);
lean_inc(v_snd_3849_);
lean_inc(v_fst_3848_);
lean_inc_ref(v_c_3823_);
v___x_3850_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_3821_, v_x_3822_, v_c_3823_, v_fst_3848_, v_snd_3849_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_object* v_a_3851_; lean_object* v___x_3852_; 
v_a_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_a_3851_);
lean_dec_ref(v___x_3850_);
v___x_3852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
if (lean_obj_tag(v_a_3851_) == 1)
{
lean_object* v_val_3853_; lean_object* v___x_3854_; 
v_val_3853_ = lean_ctor_get(v_a_3851_, 0);
lean_inc(v_val_3853_);
lean_dec_ref(v_a_3851_);
lean_inc(v___y_3838_);
lean_inc_ref(v___y_3837_);
lean_inc(v___y_3836_);
lean_inc_ref(v___y_3835_);
lean_inc(v___y_3834_);
lean_inc_ref(v___y_3833_);
lean_inc(v___y_3832_);
lean_inc_ref(v___y_3831_);
lean_inc(v___y_3830_);
lean_inc(v___y_3829_);
lean_inc(v___y_3828_);
v___x_3854_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_val_3853_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v___x_3855_; 
lean_dec_ref(v___x_3854_);
v___x_3855_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3865_; 
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3858_ = v___x_3855_;
v_isShared_3859_ = v_isSharedCheck_3865_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3855_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3865_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
uint8_t v___x_3860_; 
v___x_3860_ = lean_unbox(v_a_3856_);
lean_dec(v_a_3856_);
if (v___x_3860_ == 0)
{
lean_del_object(v___x_3858_);
v_a_3841_ = v___x_3852_;
goto v___jp_3840_;
}
else
{
lean_object* v___x_3861_; lean_object* v___x_3863_; 
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec_ref(v_c_3823_);
v___x_3861_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 0, v___x_3861_);
v___x_3863_ = v___x_3858_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec_ref(v_c_3823_);
v_a_3866_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v___x_3855_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3855_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec_ref(v_c_3823_);
v_a_3874_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3854_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3854_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
else
{
lean_object* v___x_3882_; 
lean_dec(v_a_3851_);
lean_inc(v___y_3828_);
v___x_3882_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_snd_3849_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_dec_ref(v___x_3882_);
v_a_3841_ = v___x_3852_;
goto v___jp_3840_;
}
else
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3890_; 
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec_ref(v_c_3823_);
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3885_ = v___x_3882_;
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3882_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
}
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec_ref(v_c_3823_);
v_a_3891_ = lean_ctor_get(v___x_3850_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___x_3850_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3850_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
if (v_isShared_3894_ == 0)
{
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
}
v___jp_3840_:
{
size_t v___x_3842_; size_t v___x_3843_; 
v___x_3842_ = ((size_t)1ULL);
v___x_3843_ = lean_usize_add(v_i_3826_, v___x_3842_);
v_i_3826_ = v___x_3843_;
v_b_3827_ = v_a_3841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object** _args){
lean_object* v_a_3899_ = _args[0];
lean_object* v_x_3900_ = _args[1];
lean_object* v_c_3901_ = _args[2];
lean_object* v_as_3902_ = _args[3];
lean_object* v_sz_3903_ = _args[4];
lean_object* v_i_3904_ = _args[5];
lean_object* v_b_3905_ = _args[6];
lean_object* v___y_3906_ = _args[7];
lean_object* v___y_3907_ = _args[8];
lean_object* v___y_3908_ = _args[9];
lean_object* v___y_3909_ = _args[10];
lean_object* v___y_3910_ = _args[11];
lean_object* v___y_3911_ = _args[12];
lean_object* v___y_3912_ = _args[13];
lean_object* v___y_3913_ = _args[14];
lean_object* v___y_3914_ = _args[15];
lean_object* v___y_3915_ = _args[16];
lean_object* v___y_3916_ = _args[17];
lean_object* v___y_3917_ = _args[18];
_start:
{
size_t v_sz_boxed_3918_; size_t v_i_boxed_3919_; lean_object* v_res_3920_; 
v_sz_boxed_3918_ = lean_unbox_usize(v_sz_3903_);
lean_dec(v_sz_3903_);
v_i_boxed_3919_ = lean_unbox_usize(v_i_3904_);
lean_dec(v_i_3904_);
v_res_3920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3899_, v_x_3900_, v_c_3901_, v_as_3902_, v_sz_boxed_3918_, v_i_boxed_3919_, v_b_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_);
lean_dec_ref(v_as_3902_);
lean_dec(v_x_3900_);
lean_dec(v_a_3899_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object* v_a_3921_, lean_object* v_x_3922_, lean_object* v_c_3923_, lean_object* v_y_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_){
_start:
{
lean_object* v___x_3937_; 
v___x_3937_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3997_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3940_ = v___x_3937_;
v_isShared_3941_ = v_isSharedCheck_3997_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3937_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3997_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
uint8_t v___x_3942_; 
v___x_3942_ = lean_unbox(v_a_3938_);
lean_dec(v_a_3938_);
if (v___x_3942_ == 0)
{
lean_object* v___x_3943_; 
lean_del_object(v___x_3940_);
v___x_3943_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v___y_3946_; lean_object* v_diseqs_3979_; lean_object* v_size_3980_; lean_object* v___x_3981_; uint8_t v___x_3982_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref(v___x_3943_);
v_diseqs_3979_ = lean_ctor_get(v_a_3944_, 34);
lean_inc_ref(v_diseqs_3979_);
lean_dec(v_a_3944_);
v_size_3980_ = lean_ctor_get(v_diseqs_3979_, 2);
v___x_3981_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_3982_ = lean_nat_dec_lt(v_y_3924_, v_size_3980_);
if (v___x_3982_ == 0)
{
lean_object* v___x_3983_; 
lean_dec_ref(v_diseqs_3979_);
v___x_3983_ = l_outOfBounds___redArg(v___x_3981_);
v___y_3946_ = v___x_3983_;
goto v___jp_3945_;
}
else
{
lean_object* v___x_3984_; 
v___x_3984_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3981_, v_diseqs_3979_, v_y_3924_);
v___y_3946_ = v___x_3984_;
goto v___jp_3945_;
}
v___jp_3945_:
{
lean_object* v___x_3947_; lean_object* v_fst_3948_; lean_object* v_snd_3949_; lean_object* v___f_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3947_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3922_, v___y_3946_);
v_fst_3948_ = lean_ctor_get(v___x_3947_, 0);
lean_inc(v_fst_3948_);
v_snd_3949_ = lean_ctor_get(v___x_3947_, 1);
lean_inc(v_snd_3949_);
lean_dec_ref(v___x_3947_);
lean_inc(v_a_3925_);
v___f_3950_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3950_, 0, v_a_3925_);
lean_closure_set(v___f_3950_, 1, v_y_3924_);
lean_closure_set(v___f_3950_, 2, v_fst_3948_);
v___x_3951_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3952_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3951_, v___f_3950_, v_a_3926_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v___x_3953_; lean_object* v___x_3954_; size_t v_sz_3955_; size_t v___x_3956_; lean_object* v___x_3957_; 
lean_dec_ref(v___x_3952_);
v___x_3953_ = lean_box(0);
v___x_3954_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_3955_ = lean_array_size(v_snd_3949_);
v___x_3956_ = ((size_t)0ULL);
v___x_3957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3921_, v_x_3922_, v_c_3923_, v_snd_3949_, v_sz_3955_, v___x_3956_, v___x_3954_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_);
lean_dec(v_snd_3949_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3970_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3960_ = v___x_3957_;
v_isShared_3961_ = v_isSharedCheck_3970_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3957_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3970_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v_fst_3962_; 
v_fst_3962_ = lean_ctor_get(v_a_3958_, 0);
lean_inc(v_fst_3962_);
lean_dec(v_a_3958_);
if (lean_obj_tag(v_fst_3962_) == 0)
{
lean_object* v___x_3964_; 
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 0, v___x_3953_);
v___x_3964_ = v___x_3960_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v___x_3953_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
else
{
lean_object* v_val_3966_; lean_object* v___x_3968_; 
v_val_3966_ = lean_ctor_get(v_fst_3962_, 0);
lean_inc(v_val_3966_);
lean_dec_ref(v_fst_3962_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 0, v_val_3966_);
v___x_3968_ = v___x_3960_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_val_3966_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
v_a_3971_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3957_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3957_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
else
{
lean_dec(v_snd_3949_);
lean_dec(v_a_3935_);
lean_dec_ref(v_a_3934_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
lean_dec(v_a_3929_);
lean_dec_ref(v_a_3928_);
lean_dec(v_a_3927_);
lean_dec(v_a_3926_);
lean_dec(v_a_3925_);
lean_dec_ref(v_c_3923_);
return v___x_3952_;
}
}
}
else
{
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3992_; 
lean_dec(v_a_3935_);
lean_dec_ref(v_a_3934_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
lean_dec(v_a_3929_);
lean_dec_ref(v_a_3928_);
lean_dec(v_a_3927_);
lean_dec(v_a_3926_);
lean_dec(v_a_3925_);
lean_dec(v_y_3924_);
lean_dec_ref(v_c_3923_);
v_a_3985_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3987_ = v___x_3943_;
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___x_3943_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3990_; 
if (v_isShared_3988_ == 0)
{
v___x_3990_ = v___x_3987_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_a_3985_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
return v___x_3990_;
}
}
}
}
else
{
lean_object* v___x_3993_; lean_object* v___x_3995_; 
lean_dec(v_a_3935_);
lean_dec_ref(v_a_3934_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
lean_dec(v_a_3929_);
lean_dec_ref(v_a_3928_);
lean_dec(v_a_3927_);
lean_dec(v_a_3926_);
lean_dec(v_a_3925_);
lean_dec(v_y_3924_);
lean_dec_ref(v_c_3923_);
v___x_3993_ = lean_box(0);
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 0, v___x_3993_);
v___x_3995_ = v___x_3940_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v___x_3993_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
else
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4005_; 
lean_dec(v_a_3935_);
lean_dec_ref(v_a_3934_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
lean_dec(v_a_3929_);
lean_dec_ref(v_a_3928_);
lean_dec(v_a_3927_);
lean_dec(v_a_3926_);
lean_dec(v_a_3925_);
lean_dec(v_y_3924_);
lean_dec_ref(v_c_3923_);
v_a_3998_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_4000_ = v___x_3937_;
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3937_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_a_3998_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object* v_a_4006_, lean_object* v_x_4007_, lean_object* v_c_4008_, lean_object* v_y_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v_a_4006_, v_x_4007_, v_c_4008_, v_y_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
lean_dec(v_x_4007_);
lean_dec(v_a_4006_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object* v_a_4023_, lean_object* v_x_4024_, lean_object* v_c_4025_, lean_object* v_y_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_){
_start:
{
lean_object* v___x_4039_; 
lean_inc(v_a_4037_);
lean_inc_ref(v_a_4036_);
lean_inc(v_a_4035_);
lean_inc_ref(v_a_4034_);
lean_inc(v_a_4033_);
lean_inc_ref(v_a_4032_);
lean_inc(v_a_4031_);
lean_inc_ref(v_a_4030_);
lean_inc(v_a_4029_);
lean_inc(v_a_4028_);
lean_inc(v_a_4027_);
lean_inc(v_y_4026_);
lean_inc_ref(v_c_4025_);
lean_inc(v_x_4024_);
lean_inc(v_a_4023_);
v___x_4039_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_4023_, v_x_4024_, v_c_4025_, v_y_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v___x_4040_; 
lean_dec_ref(v___x_4039_);
lean_inc(v_a_4037_);
lean_inc_ref(v_a_4036_);
lean_inc(v_a_4035_);
lean_inc_ref(v_a_4034_);
lean_inc(v_a_4033_);
lean_inc_ref(v_a_4032_);
lean_inc(v_a_4031_);
lean_inc_ref(v_a_4030_);
lean_inc(v_a_4029_);
lean_inc(v_a_4028_);
lean_inc(v_a_4027_);
lean_inc(v_y_4026_);
lean_inc_ref(v_c_4025_);
lean_inc(v_x_4024_);
lean_inc(v_a_4023_);
v___x_4040_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_4023_, v_x_4024_, v_c_4025_, v_y_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
lean_dec_ref(v___x_4040_);
v___x_4041_ = lean_nat_to_int(v_a_4023_);
v___x_4042_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v___x_4041_, v_x_4024_, v_c_4025_, v_y_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
lean_dec(v_x_4024_);
lean_dec(v___x_4041_);
return v___x_4042_;
}
else
{
lean_dec(v_a_4037_);
lean_dec_ref(v_a_4036_);
lean_dec(v_a_4035_);
lean_dec_ref(v_a_4034_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec(v_a_4028_);
lean_dec(v_a_4027_);
lean_dec(v_y_4026_);
lean_dec_ref(v_c_4025_);
lean_dec(v_x_4024_);
lean_dec(v_a_4023_);
return v___x_4040_;
}
}
else
{
lean_dec(v_a_4037_);
lean_dec_ref(v_a_4036_);
lean_dec(v_a_4035_);
lean_dec_ref(v_a_4034_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec(v_a_4028_);
lean_dec(v_a_4027_);
lean_dec(v_y_4026_);
lean_dec_ref(v_c_4025_);
lean_dec(v_x_4024_);
lean_dec(v_a_4023_);
return v___x_4039_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object* v_a_4043_, lean_object* v_x_4044_, lean_object* v_c_4045_, lean_object* v_y_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_){
_start:
{
lean_object* v_res_4059_; 
v_res_4059_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4043_, v_x_4044_, v_c_4045_, v_y_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(lean_object* v_a_4060_, lean_object* v_x_4061_, lean_object* v_s_4062_){
_start:
{
lean_object* v_structs_4063_; lean_object* v_typeIdOf_4064_; lean_object* v_exprToStructId_4065_; lean_object* v_exprToStructIdEntries_4066_; lean_object* v_forbiddenNatModules_4067_; lean_object* v_natStructs_4068_; lean_object* v_natTypeIdOf_4069_; lean_object* v_exprToNatStructId_4070_; lean_object* v___x_4071_; uint8_t v___x_4072_; 
v_structs_4063_ = lean_ctor_get(v_s_4062_, 0);
v_typeIdOf_4064_ = lean_ctor_get(v_s_4062_, 1);
v_exprToStructId_4065_ = lean_ctor_get(v_s_4062_, 2);
v_exprToStructIdEntries_4066_ = lean_ctor_get(v_s_4062_, 3);
v_forbiddenNatModules_4067_ = lean_ctor_get(v_s_4062_, 4);
v_natStructs_4068_ = lean_ctor_get(v_s_4062_, 5);
v_natTypeIdOf_4069_ = lean_ctor_get(v_s_4062_, 6);
v_exprToNatStructId_4070_ = lean_ctor_get(v_s_4062_, 7);
v___x_4071_ = lean_array_get_size(v_structs_4063_);
v___x_4072_ = lean_nat_dec_lt(v_a_4060_, v___x_4071_);
if (v___x_4072_ == 0)
{
return v_s_4062_;
}
else
{
lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4135_; 
lean_inc_ref(v_exprToNatStructId_4070_);
lean_inc_ref(v_natTypeIdOf_4069_);
lean_inc_ref(v_natStructs_4068_);
lean_inc_ref(v_forbiddenNatModules_4067_);
lean_inc_ref(v_exprToStructIdEntries_4066_);
lean_inc_ref(v_exprToStructId_4065_);
lean_inc_ref(v_typeIdOf_4064_);
lean_inc_ref(v_structs_4063_);
v_isSharedCheck_4135_ = !lean_is_exclusive(v_s_4062_);
if (v_isSharedCheck_4135_ == 0)
{
lean_object* v_unused_4136_; lean_object* v_unused_4137_; lean_object* v_unused_4138_; lean_object* v_unused_4139_; lean_object* v_unused_4140_; lean_object* v_unused_4141_; lean_object* v_unused_4142_; lean_object* v_unused_4143_; 
v_unused_4136_ = lean_ctor_get(v_s_4062_, 7);
lean_dec(v_unused_4136_);
v_unused_4137_ = lean_ctor_get(v_s_4062_, 6);
lean_dec(v_unused_4137_);
v_unused_4138_ = lean_ctor_get(v_s_4062_, 5);
lean_dec(v_unused_4138_);
v_unused_4139_ = lean_ctor_get(v_s_4062_, 4);
lean_dec(v_unused_4139_);
v_unused_4140_ = lean_ctor_get(v_s_4062_, 3);
lean_dec(v_unused_4140_);
v_unused_4141_ = lean_ctor_get(v_s_4062_, 2);
lean_dec(v_unused_4141_);
v_unused_4142_ = lean_ctor_get(v_s_4062_, 1);
lean_dec(v_unused_4142_);
v_unused_4143_ = lean_ctor_get(v_s_4062_, 0);
lean_dec(v_unused_4143_);
v___x_4074_ = v_s_4062_;
v_isShared_4075_ = v_isSharedCheck_4135_;
goto v_resetjp_4073_;
}
else
{
lean_dec(v_s_4062_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4135_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v_v_4076_; lean_object* v_id_4077_; lean_object* v_ringId_x3f_4078_; lean_object* v_type_4079_; lean_object* v_u_4080_; lean_object* v_intModuleInst_4081_; lean_object* v_leInst_x3f_4082_; lean_object* v_ltInst_x3f_4083_; lean_object* v_lawfulOrderLTInst_x3f_4084_; lean_object* v_isPreorderInst_x3f_4085_; lean_object* v_orderedAddInst_x3f_4086_; lean_object* v_isLinearInst_x3f_4087_; lean_object* v_noNatDivInst_x3f_4088_; lean_object* v_ringInst_x3f_4089_; lean_object* v_commRingInst_x3f_4090_; lean_object* v_orderedRingInst_x3f_4091_; lean_object* v_fieldInst_x3f_4092_; lean_object* v_charInst_x3f_4093_; lean_object* v_zero_4094_; lean_object* v_ofNatZero_4095_; lean_object* v_one_x3f_4096_; lean_object* v_leFn_x3f_4097_; lean_object* v_ltFn_x3f_4098_; lean_object* v_addFn_4099_; lean_object* v_zsmulFn_4100_; lean_object* v_nsmulFn_4101_; lean_object* v_zsmulFn_x3f_4102_; lean_object* v_nsmulFn_x3f_4103_; lean_object* v_homomulFn_x3f_4104_; lean_object* v_subFn_4105_; lean_object* v_negFn_4106_; lean_object* v_vars_4107_; lean_object* v_varMap_4108_; lean_object* v_lowers_4109_; lean_object* v_uppers_4110_; lean_object* v_diseqs_4111_; lean_object* v_assignment_4112_; uint8_t v_caseSplits_4113_; lean_object* v_conflict_x3f_4114_; lean_object* v_diseqSplits_4115_; lean_object* v_elimEqs_4116_; lean_object* v_elimStack_4117_; lean_object* v_occurs_4118_; lean_object* v_ignored_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4134_; 
v_v_4076_ = lean_array_fget(v_structs_4063_, v_a_4060_);
v_id_4077_ = lean_ctor_get(v_v_4076_, 0);
v_ringId_x3f_4078_ = lean_ctor_get(v_v_4076_, 1);
v_type_4079_ = lean_ctor_get(v_v_4076_, 2);
v_u_4080_ = lean_ctor_get(v_v_4076_, 3);
v_intModuleInst_4081_ = lean_ctor_get(v_v_4076_, 4);
v_leInst_x3f_4082_ = lean_ctor_get(v_v_4076_, 5);
v_ltInst_x3f_4083_ = lean_ctor_get(v_v_4076_, 6);
v_lawfulOrderLTInst_x3f_4084_ = lean_ctor_get(v_v_4076_, 7);
v_isPreorderInst_x3f_4085_ = lean_ctor_get(v_v_4076_, 8);
v_orderedAddInst_x3f_4086_ = lean_ctor_get(v_v_4076_, 9);
v_isLinearInst_x3f_4087_ = lean_ctor_get(v_v_4076_, 10);
v_noNatDivInst_x3f_4088_ = lean_ctor_get(v_v_4076_, 11);
v_ringInst_x3f_4089_ = lean_ctor_get(v_v_4076_, 12);
v_commRingInst_x3f_4090_ = lean_ctor_get(v_v_4076_, 13);
v_orderedRingInst_x3f_4091_ = lean_ctor_get(v_v_4076_, 14);
v_fieldInst_x3f_4092_ = lean_ctor_get(v_v_4076_, 15);
v_charInst_x3f_4093_ = lean_ctor_get(v_v_4076_, 16);
v_zero_4094_ = lean_ctor_get(v_v_4076_, 17);
v_ofNatZero_4095_ = lean_ctor_get(v_v_4076_, 18);
v_one_x3f_4096_ = lean_ctor_get(v_v_4076_, 19);
v_leFn_x3f_4097_ = lean_ctor_get(v_v_4076_, 20);
v_ltFn_x3f_4098_ = lean_ctor_get(v_v_4076_, 21);
v_addFn_4099_ = lean_ctor_get(v_v_4076_, 22);
v_zsmulFn_4100_ = lean_ctor_get(v_v_4076_, 23);
v_nsmulFn_4101_ = lean_ctor_get(v_v_4076_, 24);
v_zsmulFn_x3f_4102_ = lean_ctor_get(v_v_4076_, 25);
v_nsmulFn_x3f_4103_ = lean_ctor_get(v_v_4076_, 26);
v_homomulFn_x3f_4104_ = lean_ctor_get(v_v_4076_, 27);
v_subFn_4105_ = lean_ctor_get(v_v_4076_, 28);
v_negFn_4106_ = lean_ctor_get(v_v_4076_, 29);
v_vars_4107_ = lean_ctor_get(v_v_4076_, 30);
v_varMap_4108_ = lean_ctor_get(v_v_4076_, 31);
v_lowers_4109_ = lean_ctor_get(v_v_4076_, 32);
v_uppers_4110_ = lean_ctor_get(v_v_4076_, 33);
v_diseqs_4111_ = lean_ctor_get(v_v_4076_, 34);
v_assignment_4112_ = lean_ctor_get(v_v_4076_, 35);
v_caseSplits_4113_ = lean_ctor_get_uint8(v_v_4076_, sizeof(void*)*42);
v_conflict_x3f_4114_ = lean_ctor_get(v_v_4076_, 36);
v_diseqSplits_4115_ = lean_ctor_get(v_v_4076_, 37);
v_elimEqs_4116_ = lean_ctor_get(v_v_4076_, 38);
v_elimStack_4117_ = lean_ctor_get(v_v_4076_, 39);
v_occurs_4118_ = lean_ctor_get(v_v_4076_, 40);
v_ignored_4119_ = lean_ctor_get(v_v_4076_, 41);
v_isSharedCheck_4134_ = !lean_is_exclusive(v_v_4076_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4121_ = v_v_4076_;
v_isShared_4122_ = v_isSharedCheck_4134_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_ignored_4119_);
lean_inc(v_occurs_4118_);
lean_inc(v_elimStack_4117_);
lean_inc(v_elimEqs_4116_);
lean_inc(v_diseqSplits_4115_);
lean_inc(v_conflict_x3f_4114_);
lean_inc(v_assignment_4112_);
lean_inc(v_diseqs_4111_);
lean_inc(v_uppers_4110_);
lean_inc(v_lowers_4109_);
lean_inc(v_varMap_4108_);
lean_inc(v_vars_4107_);
lean_inc(v_negFn_4106_);
lean_inc(v_subFn_4105_);
lean_inc(v_homomulFn_x3f_4104_);
lean_inc(v_nsmulFn_x3f_4103_);
lean_inc(v_zsmulFn_x3f_4102_);
lean_inc(v_nsmulFn_4101_);
lean_inc(v_zsmulFn_4100_);
lean_inc(v_addFn_4099_);
lean_inc(v_ltFn_x3f_4098_);
lean_inc(v_leFn_x3f_4097_);
lean_inc(v_one_x3f_4096_);
lean_inc(v_ofNatZero_4095_);
lean_inc(v_zero_4094_);
lean_inc(v_charInst_x3f_4093_);
lean_inc(v_fieldInst_x3f_4092_);
lean_inc(v_orderedRingInst_x3f_4091_);
lean_inc(v_commRingInst_x3f_4090_);
lean_inc(v_ringInst_x3f_4089_);
lean_inc(v_noNatDivInst_x3f_4088_);
lean_inc(v_isLinearInst_x3f_4087_);
lean_inc(v_orderedAddInst_x3f_4086_);
lean_inc(v_isPreorderInst_x3f_4085_);
lean_inc(v_lawfulOrderLTInst_x3f_4084_);
lean_inc(v_ltInst_x3f_4083_);
lean_inc(v_leInst_x3f_4082_);
lean_inc(v_intModuleInst_4081_);
lean_inc(v_u_4080_);
lean_inc(v_type_4079_);
lean_inc(v_ringId_x3f_4078_);
lean_inc(v_id_4077_);
lean_dec(v_v_4076_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4134_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4123_; lean_object* v_xs_x27_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4128_; 
v___x_4123_ = lean_box(0);
v_xs_x27_4124_ = lean_array_fset(v_structs_4063_, v_a_4060_, v___x_4123_);
v___x_4125_ = lean_box(1);
v___x_4126_ = l_Lean_PersistentArray_set___redArg(v_occurs_4118_, v_x_4061_, v___x_4125_);
if (v_isShared_4122_ == 0)
{
lean_ctor_set(v___x_4121_, 40, v___x_4126_);
v___x_4128_ = v___x_4121_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_id_4077_);
lean_ctor_set(v_reuseFailAlloc_4133_, 1, v_ringId_x3f_4078_);
lean_ctor_set(v_reuseFailAlloc_4133_, 2, v_type_4079_);
lean_ctor_set(v_reuseFailAlloc_4133_, 3, v_u_4080_);
lean_ctor_set(v_reuseFailAlloc_4133_, 4, v_intModuleInst_4081_);
lean_ctor_set(v_reuseFailAlloc_4133_, 5, v_leInst_x3f_4082_);
lean_ctor_set(v_reuseFailAlloc_4133_, 6, v_ltInst_x3f_4083_);
lean_ctor_set(v_reuseFailAlloc_4133_, 7, v_lawfulOrderLTInst_x3f_4084_);
lean_ctor_set(v_reuseFailAlloc_4133_, 8, v_isPreorderInst_x3f_4085_);
lean_ctor_set(v_reuseFailAlloc_4133_, 9, v_orderedAddInst_x3f_4086_);
lean_ctor_set(v_reuseFailAlloc_4133_, 10, v_isLinearInst_x3f_4087_);
lean_ctor_set(v_reuseFailAlloc_4133_, 11, v_noNatDivInst_x3f_4088_);
lean_ctor_set(v_reuseFailAlloc_4133_, 12, v_ringInst_x3f_4089_);
lean_ctor_set(v_reuseFailAlloc_4133_, 13, v_commRingInst_x3f_4090_);
lean_ctor_set(v_reuseFailAlloc_4133_, 14, v_orderedRingInst_x3f_4091_);
lean_ctor_set(v_reuseFailAlloc_4133_, 15, v_fieldInst_x3f_4092_);
lean_ctor_set(v_reuseFailAlloc_4133_, 16, v_charInst_x3f_4093_);
lean_ctor_set(v_reuseFailAlloc_4133_, 17, v_zero_4094_);
lean_ctor_set(v_reuseFailAlloc_4133_, 18, v_ofNatZero_4095_);
lean_ctor_set(v_reuseFailAlloc_4133_, 19, v_one_x3f_4096_);
lean_ctor_set(v_reuseFailAlloc_4133_, 20, v_leFn_x3f_4097_);
lean_ctor_set(v_reuseFailAlloc_4133_, 21, v_ltFn_x3f_4098_);
lean_ctor_set(v_reuseFailAlloc_4133_, 22, v_addFn_4099_);
lean_ctor_set(v_reuseFailAlloc_4133_, 23, v_zsmulFn_4100_);
lean_ctor_set(v_reuseFailAlloc_4133_, 24, v_nsmulFn_4101_);
lean_ctor_set(v_reuseFailAlloc_4133_, 25, v_zsmulFn_x3f_4102_);
lean_ctor_set(v_reuseFailAlloc_4133_, 26, v_nsmulFn_x3f_4103_);
lean_ctor_set(v_reuseFailAlloc_4133_, 27, v_homomulFn_x3f_4104_);
lean_ctor_set(v_reuseFailAlloc_4133_, 28, v_subFn_4105_);
lean_ctor_set(v_reuseFailAlloc_4133_, 29, v_negFn_4106_);
lean_ctor_set(v_reuseFailAlloc_4133_, 30, v_vars_4107_);
lean_ctor_set(v_reuseFailAlloc_4133_, 31, v_varMap_4108_);
lean_ctor_set(v_reuseFailAlloc_4133_, 32, v_lowers_4109_);
lean_ctor_set(v_reuseFailAlloc_4133_, 33, v_uppers_4110_);
lean_ctor_set(v_reuseFailAlloc_4133_, 34, v_diseqs_4111_);
lean_ctor_set(v_reuseFailAlloc_4133_, 35, v_assignment_4112_);
lean_ctor_set(v_reuseFailAlloc_4133_, 36, v_conflict_x3f_4114_);
lean_ctor_set(v_reuseFailAlloc_4133_, 37, v_diseqSplits_4115_);
lean_ctor_set(v_reuseFailAlloc_4133_, 38, v_elimEqs_4116_);
lean_ctor_set(v_reuseFailAlloc_4133_, 39, v_elimStack_4117_);
lean_ctor_set(v_reuseFailAlloc_4133_, 40, v___x_4126_);
lean_ctor_set(v_reuseFailAlloc_4133_, 41, v_ignored_4119_);
lean_ctor_set_uint8(v_reuseFailAlloc_4133_, sizeof(void*)*42, v_caseSplits_4113_);
v___x_4128_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
lean_object* v___x_4129_; lean_object* v___x_4131_; 
v___x_4129_ = lean_array_fset(v_xs_x27_4124_, v_a_4060_, v___x_4128_);
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 0, v___x_4129_);
v___x_4131_ = v___x_4074_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4129_);
lean_ctor_set(v_reuseFailAlloc_4132_, 1, v_typeIdOf_4064_);
lean_ctor_set(v_reuseFailAlloc_4132_, 2, v_exprToStructId_4065_);
lean_ctor_set(v_reuseFailAlloc_4132_, 3, v_exprToStructIdEntries_4066_);
lean_ctor_set(v_reuseFailAlloc_4132_, 4, v_forbiddenNatModules_4067_);
lean_ctor_set(v_reuseFailAlloc_4132_, 5, v_natStructs_4068_);
lean_ctor_set(v_reuseFailAlloc_4132_, 6, v_natTypeIdOf_4069_);
lean_ctor_set(v_reuseFailAlloc_4132_, 7, v_exprToNatStructId_4070_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed(lean_object* v_a_4144_, lean_object* v_x_4145_, lean_object* v_s_4146_){
_start:
{
lean_object* v_res_4147_; 
v_res_4147_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(v_a_4144_, v_x_4145_, v_s_4146_);
lean_dec(v_x_4145_);
lean_dec(v_a_4144_);
return v_res_4147_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object* v_a_4148_, lean_object* v_x_4149_, lean_object* v_c_4150_, lean_object* v_init_4151_, lean_object* v_x_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
if (lean_obj_tag(v_x_4152_) == 0)
{
lean_object* v_k_4165_; lean_object* v_l_4166_; lean_object* v_r_4167_; lean_object* v___x_4168_; 
v_k_4165_ = lean_ctor_get(v_x_4152_, 1);
lean_inc(v_k_4165_);
v_l_4166_ = lean_ctor_get(v_x_4152_, 3);
lean_inc(v_l_4166_);
v_r_4167_ = lean_ctor_get(v_x_4152_, 4);
lean_inc(v_r_4167_);
lean_dec_ref(v_x_4152_);
lean_inc(v___y_4163_);
lean_inc_ref(v___y_4162_);
lean_inc(v___y_4161_);
lean_inc_ref(v___y_4160_);
lean_inc(v___y_4159_);
lean_inc_ref(v___y_4158_);
lean_inc(v___y_4157_);
lean_inc_ref(v___y_4156_);
lean_inc(v___y_4155_);
lean_inc(v___y_4154_);
lean_inc(v___y_4153_);
lean_inc_ref(v_c_4150_);
lean_inc(v_x_4149_);
lean_inc(v_a_4148_);
v___x_4168_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4148_, v_x_4149_, v_c_4150_, v_init_4151_, v_l_4166_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v___x_4169_; 
lean_dec_ref(v___x_4168_);
lean_inc(v___y_4163_);
lean_inc_ref(v___y_4162_);
lean_inc(v___y_4161_);
lean_inc_ref(v___y_4160_);
lean_inc(v___y_4159_);
lean_inc_ref(v___y_4158_);
lean_inc(v___y_4157_);
lean_inc_ref(v___y_4156_);
lean_inc(v___y_4155_);
lean_inc(v___y_4154_);
lean_inc(v___y_4153_);
lean_inc_ref(v_c_4150_);
lean_inc(v_x_4149_);
lean_inc(v_a_4148_);
v___x_4169_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4148_, v_x_4149_, v_c_4150_, v_k_4165_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_object* v___x_4170_; 
lean_dec_ref(v___x_4169_);
v___x_4170_ = lean_box(0);
v_init_4151_ = v___x_4170_;
v_x_4152_ = v_r_4167_;
goto _start;
}
else
{
lean_object* v_a_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4179_; 
lean_dec(v_r_4167_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
lean_dec(v___y_4159_);
lean_dec_ref(v___y_4158_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v_c_4150_);
lean_dec(v_x_4149_);
lean_dec(v_a_4148_);
v_a_4172_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4174_ = v___x_4169_;
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_a_4172_);
lean_dec(v___x_4169_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4177_; 
if (v_isShared_4175_ == 0)
{
v___x_4177_ = v___x_4174_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_a_4172_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
}
else
{
lean_dec(v_r_4167_);
lean_dec(v_k_4165_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
lean_dec(v___y_4159_);
lean_dec_ref(v___y_4158_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v_c_4150_);
lean_dec(v_x_4149_);
lean_dec(v_a_4148_);
return v___x_4168_;
}
}
else
{
lean_object* v___x_4180_; lean_object* v___x_4181_; 
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
lean_dec(v___y_4159_);
lean_dec_ref(v___y_4158_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v_c_4150_);
lean_dec(v_x_4149_);
lean_dec(v_a_4148_);
v___x_4180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4180_, 0, v_init_4151_);
v___x_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4180_);
return v___x_4181_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object** _args){
lean_object* v_a_4182_ = _args[0];
lean_object* v_x_4183_ = _args[1];
lean_object* v_c_4184_ = _args[2];
lean_object* v_init_4185_ = _args[3];
lean_object* v_x_4186_ = _args[4];
lean_object* v___y_4187_ = _args[5];
lean_object* v___y_4188_ = _args[6];
lean_object* v___y_4189_ = _args[7];
lean_object* v___y_4190_ = _args[8];
lean_object* v___y_4191_ = _args[9];
lean_object* v___y_4192_ = _args[10];
lean_object* v___y_4193_ = _args[11];
lean_object* v___y_4194_ = _args[12];
lean_object* v___y_4195_ = _args[13];
lean_object* v___y_4196_ = _args[14];
lean_object* v___y_4197_ = _args[15];
lean_object* v___y_4198_ = _args[16];
_start:
{
lean_object* v_res_4199_; 
v_res_4199_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4182_, v_x_4183_, v_c_4184_, v_init_4185_, v_x_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
return v_res_4199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object* v_a_4200_, lean_object* v_x_4201_, lean_object* v_c_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_){
_start:
{
lean_object* v___x_4215_; 
v___x_4215_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v_a_4216_; lean_object* v_occurs_4217_; lean_object* v_size_4218_; lean_object* v___f_4219_; lean_object* v___y_4221_; lean_object* v___x_4243_; uint8_t v___x_4244_; 
v_a_4216_ = lean_ctor_get(v___x_4215_, 0);
lean_inc(v_a_4216_);
lean_dec_ref(v___x_4215_);
v_occurs_4217_ = lean_ctor_get(v_a_4216_, 40);
lean_inc_ref(v_occurs_4217_);
lean_dec(v_a_4216_);
v_size_4218_ = lean_ctor_get(v_occurs_4217_, 2);
lean_inc(v_x_4201_);
lean_inc(v_a_4203_);
v___f_4219_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4219_, 0, v_a_4203_);
lean_closure_set(v___f_4219_, 1, v_x_4201_);
v___x_4243_ = lean_box(1);
v___x_4244_ = lean_nat_dec_lt(v_x_4201_, v_size_4218_);
if (v___x_4244_ == 0)
{
lean_object* v___x_4245_; 
lean_dec_ref(v_occurs_4217_);
v___x_4245_ = l_outOfBounds___redArg(v___x_4243_);
v___y_4221_ = v___x_4245_;
goto v___jp_4220_;
}
else
{
lean_object* v___x_4246_; 
v___x_4246_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4243_, v_occurs_4217_, v_x_4201_);
v___y_4221_ = v___x_4246_;
goto v___jp_4220_;
}
v___jp_4220_:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; 
v___x_4222_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4223_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4222_, v___f_4219_, v_a_4204_);
if (lean_obj_tag(v___x_4223_) == 0)
{
lean_object* v___x_4224_; 
lean_dec_ref(v___x_4223_);
lean_inc(v_a_4213_);
lean_inc_ref(v_a_4212_);
lean_inc(v_a_4211_);
lean_inc_ref(v_a_4210_);
lean_inc(v_a_4209_);
lean_inc_ref(v_a_4208_);
lean_inc(v_a_4207_);
lean_inc_ref(v_a_4206_);
lean_inc(v_a_4205_);
lean_inc(v_a_4204_);
lean_inc(v_a_4203_);
lean_inc_ref(v_c_4202_);
lean_inc_n(v_x_4201_, 2);
lean_inc(v_a_4200_);
v___x_4224_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4200_, v_x_4201_, v_c_4202_, v_x_4201_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v___x_4225_; lean_object* v___x_4226_; 
lean_dec_ref(v___x_4224_);
v___x_4225_ = lean_box(0);
v___x_4226_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4200_, v_x_4201_, v_c_4202_, v___x_4225_, v___y_4221_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4233_; 
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4233_ == 0)
{
lean_object* v_unused_4234_; 
v_unused_4234_ = lean_ctor_get(v___x_4226_, 0);
lean_dec(v_unused_4234_);
v___x_4228_ = v___x_4226_;
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
else
{
lean_dec(v___x_4226_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4231_; 
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 0, v___x_4225_);
v___x_4231_ = v___x_4228_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v___x_4225_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
return v___x_4231_;
}
}
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
v_a_4235_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4226_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4226_);
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
else
{
lean_dec(v___y_4221_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
lean_dec(v_a_4211_);
lean_dec_ref(v_a_4210_);
lean_dec(v_a_4209_);
lean_dec_ref(v_a_4208_);
lean_dec(v_a_4207_);
lean_dec_ref(v_a_4206_);
lean_dec(v_a_4205_);
lean_dec(v_a_4204_);
lean_dec(v_a_4203_);
lean_dec_ref(v_c_4202_);
lean_dec(v_x_4201_);
lean_dec(v_a_4200_);
return v___x_4224_;
}
}
else
{
lean_dec(v___y_4221_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
lean_dec(v_a_4211_);
lean_dec_ref(v_a_4210_);
lean_dec(v_a_4209_);
lean_dec_ref(v_a_4208_);
lean_dec(v_a_4207_);
lean_dec_ref(v_a_4206_);
lean_dec(v_a_4205_);
lean_dec(v_a_4204_);
lean_dec(v_a_4203_);
lean_dec_ref(v_c_4202_);
lean_dec(v_x_4201_);
lean_dec(v_a_4200_);
return v___x_4223_;
}
}
}
else
{
lean_object* v_a_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4254_; 
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
lean_dec(v_a_4211_);
lean_dec_ref(v_a_4210_);
lean_dec(v_a_4209_);
lean_dec_ref(v_a_4208_);
lean_dec(v_a_4207_);
lean_dec_ref(v_a_4206_);
lean_dec(v_a_4205_);
lean_dec(v_a_4204_);
lean_dec(v_a_4203_);
lean_dec_ref(v_c_4202_);
lean_dec(v_x_4201_);
lean_dec(v_a_4200_);
v_a_4247_ = lean_ctor_get(v___x_4215_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4249_ = v___x_4215_;
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_a_4247_);
lean_dec(v___x_4215_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4252_; 
if (v_isShared_4250_ == 0)
{
v___x_4252_ = v___x_4249_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4247_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
return v___x_4252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___boxed(lean_object* v_a_4255_, lean_object* v_x_4256_, lean_object* v_c_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v_a_4255_, v_x_4256_, v_c_4257_, v_a_4258_, v_a_4259_, v_a_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(lean_object* v_c_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_){
_start:
{
lean_object* v_p_4288_; 
v_p_4288_ = lean_ctor_get(v_c_4271_, 0);
if (lean_obj_tag(v_p_4288_) == 1)
{
lean_object* v_k_4289_; lean_object* v_v_4290_; lean_object* v_p_4291_; lean_object* v_y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___x_4342_; lean_object* v___x_4343_; uint8_t v___x_4344_; 
v_k_4289_ = lean_ctor_get(v_p_4288_, 0);
v_v_4290_ = lean_ctor_get(v_p_4288_, 1);
v_p_4291_ = lean_ctor_get(v_p_4288_, 2);
v___x_4342_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__1___closed__0);
v___x_4343_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4344_ = lean_int_dec_eq(v_k_4289_, v___x_4343_);
if (v___x_4344_ == 0)
{
uint8_t v___x_4345_; 
v___x_4345_ = lean_int_dec_eq(v_k_4289_, v___x_4342_);
if (v___x_4345_ == 0)
{
goto v___jp_4284_;
}
else
{
if (lean_obj_tag(v_p_4291_) == 1)
{
lean_object* v_k_4346_; lean_object* v_v_4347_; lean_object* v_p_4348_; uint8_t v___x_4349_; 
v_k_4346_ = lean_ctor_get(v_p_4291_, 0);
v_v_4347_ = lean_ctor_get(v_p_4291_, 1);
v_p_4348_ = lean_ctor_get(v_p_4291_, 2);
v___x_4349_ = lean_int_dec_eq(v_k_4346_, v___x_4343_);
if (v___x_4349_ == 0)
{
goto v___jp_4284_;
}
else
{
if (lean_obj_tag(v_p_4348_) == 0)
{
v_y_4293_ = v_v_4347_;
v___y_4294_ = v_a_4272_;
v___y_4295_ = v_a_4273_;
v___y_4296_ = v_a_4274_;
v___y_4297_ = v_a_4275_;
v___y_4298_ = v_a_4276_;
v___y_4299_ = v_a_4277_;
v___y_4300_ = v_a_4278_;
v___y_4301_ = v_a_4279_;
v___y_4302_ = v_a_4280_;
v___y_4303_ = v_a_4281_;
v___y_4304_ = v_a_4282_;
goto v___jp_4292_;
}
else
{
goto v___jp_4284_;
}
}
}
else
{
goto v___jp_4284_;
}
}
}
else
{
if (lean_obj_tag(v_p_4291_) == 1)
{
lean_object* v_k_4350_; lean_object* v_v_4351_; lean_object* v_p_4352_; uint8_t v___x_4353_; 
v_k_4350_ = lean_ctor_get(v_p_4291_, 0);
v_v_4351_ = lean_ctor_get(v_p_4291_, 1);
v_p_4352_ = lean_ctor_get(v_p_4291_, 2);
v___x_4353_ = lean_int_dec_eq(v_k_4350_, v___x_4342_);
if (v___x_4353_ == 0)
{
goto v___jp_4284_;
}
else
{
if (lean_obj_tag(v_p_4352_) == 0)
{
v_y_4293_ = v_v_4351_;
v___y_4294_ = v_a_4272_;
v___y_4295_ = v_a_4273_;
v___y_4296_ = v_a_4274_;
v___y_4297_ = v_a_4275_;
v___y_4298_ = v_a_4276_;
v___y_4299_ = v_a_4277_;
v___y_4300_ = v_a_4278_;
v___y_4301_ = v_a_4279_;
v___y_4302_ = v_a_4280_;
v___y_4303_ = v_a_4281_;
v___y_4304_ = v_a_4282_;
goto v___jp_4292_;
}
else
{
goto v___jp_4284_;
}
}
}
else
{
goto v___jp_4284_;
}
}
v___jp_4292_:
{
lean_object* v___x_4305_; 
v___x_4305_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_v_4290_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v_a_4306_; lean_object* v___x_4307_; 
v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
lean_inc(v_a_4306_);
lean_dec_ref(v___x_4305_);
v___x_4307_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_y_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v_a_4308_; lean_object* v___x_4309_; 
v_a_4308_ = lean_ctor_get(v___x_4307_, 0);
lean_inc(v_a_4308_);
lean_dec_ref(v___x_4307_);
v___x_4309_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_4306_, v_a_4308_, v___y_4295_);
lean_dec(v_a_4308_);
lean_dec(v_a_4306_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4325_; 
v_a_4310_ = lean_ctor_get(v___x_4309_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4312_ = v___x_4309_;
v_isShared_4313_ = v_isSharedCheck_4325_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4309_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4325_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
uint8_t v___x_4314_; 
v___x_4314_ = lean_unbox(v_a_4310_);
lean_dec(v_a_4310_);
if (v___x_4314_ == 0)
{
uint8_t v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4318_; 
v___x_4315_ = 1;
v___x_4316_ = lean_box(v___x_4315_);
if (v_isShared_4313_ == 0)
{
lean_ctor_set(v___x_4312_, 0, v___x_4316_);
v___x_4318_ = v___x_4312_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v___x_4316_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
else
{
uint8_t v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4323_; 
v___x_4320_ = 0;
v___x_4321_ = lean_box(v___x_4320_);
if (v_isShared_4313_ == 0)
{
lean_ctor_set(v___x_4312_, 0, v___x_4321_);
v___x_4323_ = v___x_4312_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4321_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
}
else
{
return v___x_4309_;
}
}
else
{
lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4333_; 
lean_dec(v_a_4306_);
v_a_4326_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4328_ = v___x_4307_;
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_dec(v___x_4307_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4331_; 
if (v_isShared_4329_ == 0)
{
v___x_4331_ = v___x_4328_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_a_4326_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
v_a_4334_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4305_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4305_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
}
}
else
{
goto v___jp_4284_;
}
v___jp_4284_:
{
uint8_t v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4285_ = 0;
v___x_4286_ = lean_box(v___x_4285_);
v___x_4287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4286_);
return v___x_4287_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq___boxed(lean_object* v_c_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v_c_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_);
lean_dec(v_a_4365_);
lean_dec_ref(v_a_4364_);
lean_dec(v_a_4363_);
lean_dec_ref(v_a_4362_);
lean_dec(v_a_4361_);
lean_dec_ref(v_a_4360_);
lean_dec(v_a_4359_);
lean_dec_ref(v_a_4358_);
lean_dec(v_a_4357_);
lean_dec(v_a_4356_);
lean_dec(v_a_4355_);
lean_dec_ref(v_c_4354_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(lean_object* v_c_4368_){
_start:
{
lean_object* v_p_4370_; 
v_p_4370_ = lean_ctor_get(v_c_4368_, 0);
if (lean_obj_tag(v_p_4370_) == 1)
{
lean_object* v_k_4371_; lean_object* v___x_4372_; uint8_t v___x_4373_; 
v_k_4371_ = lean_ctor_get(v_p_4370_, 0);
v___x_4372_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_4373_ = lean_int_dec_lt(v_k_4371_, v___x_4372_);
if (v___x_4373_ == 0)
{
lean_object* v___x_4374_; 
v___x_4374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4374_, 0, v_c_4368_);
return v___x_4374_;
}
else
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4375_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_4370_);
v___x_4376_ = l_Lean_Grind_Linarith_Poly_mul(v_p_4370_, v___x_4375_);
v___x_4377_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4377_, 0, v_c_4368_);
v___x_4378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4378_, 0, v___x_4376_);
lean_ctor_set(v___x_4378_, 1, v___x_4377_);
v___x_4379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4378_);
return v___x_4379_;
}
}
else
{
lean_object* v___x_4380_; 
v___x_4380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4380_, 0, v_c_4368_);
return v___x_4380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg___boxed(lean_object* v_c_4381_, lean_object* v_a_4382_){
_start:
{
lean_object* v_res_4383_; 
v_res_4383_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4381_);
return v_res_4383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(lean_object* v_c_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_){
_start:
{
lean_object* v___x_4397_; 
v___x_4397_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4384_);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___boxed(lean_object* v_c_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_){
_start:
{
lean_object* v_res_4411_; 
v_res_4411_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(v_c_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_);
lean_dec(v_a_4409_);
lean_dec_ref(v_a_4408_);
lean_dec(v_a_4407_);
lean_dec_ref(v_a_4406_);
lean_dec(v_a_4405_);
lean_dec_ref(v_a_4404_);
lean_dec(v_a_4403_);
lean_dec_ref(v_a_4402_);
lean_dec(v_a_4401_);
lean_dec(v_a_4400_);
lean_dec(v_a_4399_);
return v_res_4411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(lean_object* v___y_4412_, lean_object* v_snd_4413_, lean_object* v_fst_4414_, lean_object* v_s_4415_){
_start:
{
lean_object* v_structs_4416_; lean_object* v_typeIdOf_4417_; lean_object* v_exprToStructId_4418_; lean_object* v_exprToStructIdEntries_4419_; lean_object* v_forbiddenNatModules_4420_; lean_object* v_natStructs_4421_; lean_object* v_natTypeIdOf_4422_; lean_object* v_exprToNatStructId_4423_; lean_object* v___x_4424_; uint8_t v___x_4425_; 
v_structs_4416_ = lean_ctor_get(v_s_4415_, 0);
v_typeIdOf_4417_ = lean_ctor_get(v_s_4415_, 1);
v_exprToStructId_4418_ = lean_ctor_get(v_s_4415_, 2);
v_exprToStructIdEntries_4419_ = lean_ctor_get(v_s_4415_, 3);
v_forbiddenNatModules_4420_ = lean_ctor_get(v_s_4415_, 4);
v_natStructs_4421_ = lean_ctor_get(v_s_4415_, 5);
v_natTypeIdOf_4422_ = lean_ctor_get(v_s_4415_, 6);
v_exprToNatStructId_4423_ = lean_ctor_get(v_s_4415_, 7);
v___x_4424_ = lean_array_get_size(v_structs_4416_);
v___x_4425_ = lean_nat_dec_lt(v___y_4412_, v___x_4424_);
if (v___x_4425_ == 0)
{
lean_dec(v_fst_4414_);
lean_dec_ref(v_snd_4413_);
return v_s_4415_;
}
else
{
lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4489_; 
lean_inc_ref(v_exprToNatStructId_4423_);
lean_inc_ref(v_natTypeIdOf_4422_);
lean_inc_ref(v_natStructs_4421_);
lean_inc_ref(v_forbiddenNatModules_4420_);
lean_inc_ref(v_exprToStructIdEntries_4419_);
lean_inc_ref(v_exprToStructId_4418_);
lean_inc_ref(v_typeIdOf_4417_);
lean_inc_ref(v_structs_4416_);
v_isSharedCheck_4489_ = !lean_is_exclusive(v_s_4415_);
if (v_isSharedCheck_4489_ == 0)
{
lean_object* v_unused_4490_; lean_object* v_unused_4491_; lean_object* v_unused_4492_; lean_object* v_unused_4493_; lean_object* v_unused_4494_; lean_object* v_unused_4495_; lean_object* v_unused_4496_; lean_object* v_unused_4497_; 
v_unused_4490_ = lean_ctor_get(v_s_4415_, 7);
lean_dec(v_unused_4490_);
v_unused_4491_ = lean_ctor_get(v_s_4415_, 6);
lean_dec(v_unused_4491_);
v_unused_4492_ = lean_ctor_get(v_s_4415_, 5);
lean_dec(v_unused_4492_);
v_unused_4493_ = lean_ctor_get(v_s_4415_, 4);
lean_dec(v_unused_4493_);
v_unused_4494_ = lean_ctor_get(v_s_4415_, 3);
lean_dec(v_unused_4494_);
v_unused_4495_ = lean_ctor_get(v_s_4415_, 2);
lean_dec(v_unused_4495_);
v_unused_4496_ = lean_ctor_get(v_s_4415_, 1);
lean_dec(v_unused_4496_);
v_unused_4497_ = lean_ctor_get(v_s_4415_, 0);
lean_dec(v_unused_4497_);
v___x_4427_ = v_s_4415_;
v_isShared_4428_ = v_isSharedCheck_4489_;
goto v_resetjp_4426_;
}
else
{
lean_dec(v_s_4415_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4489_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v_v_4429_; lean_object* v_id_4430_; lean_object* v_ringId_x3f_4431_; lean_object* v_type_4432_; lean_object* v_u_4433_; lean_object* v_intModuleInst_4434_; lean_object* v_leInst_x3f_4435_; lean_object* v_ltInst_x3f_4436_; lean_object* v_lawfulOrderLTInst_x3f_4437_; lean_object* v_isPreorderInst_x3f_4438_; lean_object* v_orderedAddInst_x3f_4439_; lean_object* v_isLinearInst_x3f_4440_; lean_object* v_noNatDivInst_x3f_4441_; lean_object* v_ringInst_x3f_4442_; lean_object* v_commRingInst_x3f_4443_; lean_object* v_orderedRingInst_x3f_4444_; lean_object* v_fieldInst_x3f_4445_; lean_object* v_charInst_x3f_4446_; lean_object* v_zero_4447_; lean_object* v_ofNatZero_4448_; lean_object* v_one_x3f_4449_; lean_object* v_leFn_x3f_4450_; lean_object* v_ltFn_x3f_4451_; lean_object* v_addFn_4452_; lean_object* v_zsmulFn_4453_; lean_object* v_nsmulFn_4454_; lean_object* v_zsmulFn_x3f_4455_; lean_object* v_nsmulFn_x3f_4456_; lean_object* v_homomulFn_x3f_4457_; lean_object* v_subFn_4458_; lean_object* v_negFn_4459_; lean_object* v_vars_4460_; lean_object* v_varMap_4461_; lean_object* v_lowers_4462_; lean_object* v_uppers_4463_; lean_object* v_diseqs_4464_; lean_object* v_assignment_4465_; uint8_t v_caseSplits_4466_; lean_object* v_conflict_x3f_4467_; lean_object* v_diseqSplits_4468_; lean_object* v_elimEqs_4469_; lean_object* v_elimStack_4470_; lean_object* v_occurs_4471_; lean_object* v_ignored_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4488_; 
v_v_4429_ = lean_array_fget(v_structs_4416_, v___y_4412_);
v_id_4430_ = lean_ctor_get(v_v_4429_, 0);
v_ringId_x3f_4431_ = lean_ctor_get(v_v_4429_, 1);
v_type_4432_ = lean_ctor_get(v_v_4429_, 2);
v_u_4433_ = lean_ctor_get(v_v_4429_, 3);
v_intModuleInst_4434_ = lean_ctor_get(v_v_4429_, 4);
v_leInst_x3f_4435_ = lean_ctor_get(v_v_4429_, 5);
v_ltInst_x3f_4436_ = lean_ctor_get(v_v_4429_, 6);
v_lawfulOrderLTInst_x3f_4437_ = lean_ctor_get(v_v_4429_, 7);
v_isPreorderInst_x3f_4438_ = lean_ctor_get(v_v_4429_, 8);
v_orderedAddInst_x3f_4439_ = lean_ctor_get(v_v_4429_, 9);
v_isLinearInst_x3f_4440_ = lean_ctor_get(v_v_4429_, 10);
v_noNatDivInst_x3f_4441_ = lean_ctor_get(v_v_4429_, 11);
v_ringInst_x3f_4442_ = lean_ctor_get(v_v_4429_, 12);
v_commRingInst_x3f_4443_ = lean_ctor_get(v_v_4429_, 13);
v_orderedRingInst_x3f_4444_ = lean_ctor_get(v_v_4429_, 14);
v_fieldInst_x3f_4445_ = lean_ctor_get(v_v_4429_, 15);
v_charInst_x3f_4446_ = lean_ctor_get(v_v_4429_, 16);
v_zero_4447_ = lean_ctor_get(v_v_4429_, 17);
v_ofNatZero_4448_ = lean_ctor_get(v_v_4429_, 18);
v_one_x3f_4449_ = lean_ctor_get(v_v_4429_, 19);
v_leFn_x3f_4450_ = lean_ctor_get(v_v_4429_, 20);
v_ltFn_x3f_4451_ = lean_ctor_get(v_v_4429_, 21);
v_addFn_4452_ = lean_ctor_get(v_v_4429_, 22);
v_zsmulFn_4453_ = lean_ctor_get(v_v_4429_, 23);
v_nsmulFn_4454_ = lean_ctor_get(v_v_4429_, 24);
v_zsmulFn_x3f_4455_ = lean_ctor_get(v_v_4429_, 25);
v_nsmulFn_x3f_4456_ = lean_ctor_get(v_v_4429_, 26);
v_homomulFn_x3f_4457_ = lean_ctor_get(v_v_4429_, 27);
v_subFn_4458_ = lean_ctor_get(v_v_4429_, 28);
v_negFn_4459_ = lean_ctor_get(v_v_4429_, 29);
v_vars_4460_ = lean_ctor_get(v_v_4429_, 30);
v_varMap_4461_ = lean_ctor_get(v_v_4429_, 31);
v_lowers_4462_ = lean_ctor_get(v_v_4429_, 32);
v_uppers_4463_ = lean_ctor_get(v_v_4429_, 33);
v_diseqs_4464_ = lean_ctor_get(v_v_4429_, 34);
v_assignment_4465_ = lean_ctor_get(v_v_4429_, 35);
v_caseSplits_4466_ = lean_ctor_get_uint8(v_v_4429_, sizeof(void*)*42);
v_conflict_x3f_4467_ = lean_ctor_get(v_v_4429_, 36);
v_diseqSplits_4468_ = lean_ctor_get(v_v_4429_, 37);
v_elimEqs_4469_ = lean_ctor_get(v_v_4429_, 38);
v_elimStack_4470_ = lean_ctor_get(v_v_4429_, 39);
v_occurs_4471_ = lean_ctor_get(v_v_4429_, 40);
v_ignored_4472_ = lean_ctor_get(v_v_4429_, 41);
v_isSharedCheck_4488_ = !lean_is_exclusive(v_v_4429_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4474_ = v_v_4429_;
v_isShared_4475_ = v_isSharedCheck_4488_;
goto v_resetjp_4473_;
}
else
{
lean_inc(v_ignored_4472_);
lean_inc(v_occurs_4471_);
lean_inc(v_elimStack_4470_);
lean_inc(v_elimEqs_4469_);
lean_inc(v_diseqSplits_4468_);
lean_inc(v_conflict_x3f_4467_);
lean_inc(v_assignment_4465_);
lean_inc(v_diseqs_4464_);
lean_inc(v_uppers_4463_);
lean_inc(v_lowers_4462_);
lean_inc(v_varMap_4461_);
lean_inc(v_vars_4460_);
lean_inc(v_negFn_4459_);
lean_inc(v_subFn_4458_);
lean_inc(v_homomulFn_x3f_4457_);
lean_inc(v_nsmulFn_x3f_4456_);
lean_inc(v_zsmulFn_x3f_4455_);
lean_inc(v_nsmulFn_4454_);
lean_inc(v_zsmulFn_4453_);
lean_inc(v_addFn_4452_);
lean_inc(v_ltFn_x3f_4451_);
lean_inc(v_leFn_x3f_4450_);
lean_inc(v_one_x3f_4449_);
lean_inc(v_ofNatZero_4448_);
lean_inc(v_zero_4447_);
lean_inc(v_charInst_x3f_4446_);
lean_inc(v_fieldInst_x3f_4445_);
lean_inc(v_orderedRingInst_x3f_4444_);
lean_inc(v_commRingInst_x3f_4443_);
lean_inc(v_ringInst_x3f_4442_);
lean_inc(v_noNatDivInst_x3f_4441_);
lean_inc(v_isLinearInst_x3f_4440_);
lean_inc(v_orderedAddInst_x3f_4439_);
lean_inc(v_isPreorderInst_x3f_4438_);
lean_inc(v_lawfulOrderLTInst_x3f_4437_);
lean_inc(v_ltInst_x3f_4436_);
lean_inc(v_leInst_x3f_4435_);
lean_inc(v_intModuleInst_4434_);
lean_inc(v_u_4433_);
lean_inc(v_type_4432_);
lean_inc(v_ringId_x3f_4431_);
lean_inc(v_id_4430_);
lean_dec(v_v_4429_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4488_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v___x_4476_; lean_object* v_xs_x27_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4482_; 
v___x_4476_ = lean_box(0);
v_xs_x27_4477_ = lean_array_fset(v_structs_4416_, v___y_4412_, v___x_4476_);
v___x_4478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4478_, 0, v_snd_4413_);
v___x_4479_ = l_Lean_PersistentArray_set___redArg(v_elimEqs_4469_, v_fst_4414_, v___x_4478_);
v___x_4480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4480_, 0, v_fst_4414_);
lean_ctor_set(v___x_4480_, 1, v_elimStack_4470_);
if (v_isShared_4475_ == 0)
{
lean_ctor_set(v___x_4474_, 39, v___x_4480_);
lean_ctor_set(v___x_4474_, 38, v___x_4479_);
v___x_4482_ = v___x_4474_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_id_4430_);
lean_ctor_set(v_reuseFailAlloc_4487_, 1, v_ringId_x3f_4431_);
lean_ctor_set(v_reuseFailAlloc_4487_, 2, v_type_4432_);
lean_ctor_set(v_reuseFailAlloc_4487_, 3, v_u_4433_);
lean_ctor_set(v_reuseFailAlloc_4487_, 4, v_intModuleInst_4434_);
lean_ctor_set(v_reuseFailAlloc_4487_, 5, v_leInst_x3f_4435_);
lean_ctor_set(v_reuseFailAlloc_4487_, 6, v_ltInst_x3f_4436_);
lean_ctor_set(v_reuseFailAlloc_4487_, 7, v_lawfulOrderLTInst_x3f_4437_);
lean_ctor_set(v_reuseFailAlloc_4487_, 8, v_isPreorderInst_x3f_4438_);
lean_ctor_set(v_reuseFailAlloc_4487_, 9, v_orderedAddInst_x3f_4439_);
lean_ctor_set(v_reuseFailAlloc_4487_, 10, v_isLinearInst_x3f_4440_);
lean_ctor_set(v_reuseFailAlloc_4487_, 11, v_noNatDivInst_x3f_4441_);
lean_ctor_set(v_reuseFailAlloc_4487_, 12, v_ringInst_x3f_4442_);
lean_ctor_set(v_reuseFailAlloc_4487_, 13, v_commRingInst_x3f_4443_);
lean_ctor_set(v_reuseFailAlloc_4487_, 14, v_orderedRingInst_x3f_4444_);
lean_ctor_set(v_reuseFailAlloc_4487_, 15, v_fieldInst_x3f_4445_);
lean_ctor_set(v_reuseFailAlloc_4487_, 16, v_charInst_x3f_4446_);
lean_ctor_set(v_reuseFailAlloc_4487_, 17, v_zero_4447_);
lean_ctor_set(v_reuseFailAlloc_4487_, 18, v_ofNatZero_4448_);
lean_ctor_set(v_reuseFailAlloc_4487_, 19, v_one_x3f_4449_);
lean_ctor_set(v_reuseFailAlloc_4487_, 20, v_leFn_x3f_4450_);
lean_ctor_set(v_reuseFailAlloc_4487_, 21, v_ltFn_x3f_4451_);
lean_ctor_set(v_reuseFailAlloc_4487_, 22, v_addFn_4452_);
lean_ctor_set(v_reuseFailAlloc_4487_, 23, v_zsmulFn_4453_);
lean_ctor_set(v_reuseFailAlloc_4487_, 24, v_nsmulFn_4454_);
lean_ctor_set(v_reuseFailAlloc_4487_, 25, v_zsmulFn_x3f_4455_);
lean_ctor_set(v_reuseFailAlloc_4487_, 26, v_nsmulFn_x3f_4456_);
lean_ctor_set(v_reuseFailAlloc_4487_, 27, v_homomulFn_x3f_4457_);
lean_ctor_set(v_reuseFailAlloc_4487_, 28, v_subFn_4458_);
lean_ctor_set(v_reuseFailAlloc_4487_, 29, v_negFn_4459_);
lean_ctor_set(v_reuseFailAlloc_4487_, 30, v_vars_4460_);
lean_ctor_set(v_reuseFailAlloc_4487_, 31, v_varMap_4461_);
lean_ctor_set(v_reuseFailAlloc_4487_, 32, v_lowers_4462_);
lean_ctor_set(v_reuseFailAlloc_4487_, 33, v_uppers_4463_);
lean_ctor_set(v_reuseFailAlloc_4487_, 34, v_diseqs_4464_);
lean_ctor_set(v_reuseFailAlloc_4487_, 35, v_assignment_4465_);
lean_ctor_set(v_reuseFailAlloc_4487_, 36, v_conflict_x3f_4467_);
lean_ctor_set(v_reuseFailAlloc_4487_, 37, v_diseqSplits_4468_);
lean_ctor_set(v_reuseFailAlloc_4487_, 38, v___x_4479_);
lean_ctor_set(v_reuseFailAlloc_4487_, 39, v___x_4480_);
lean_ctor_set(v_reuseFailAlloc_4487_, 40, v_occurs_4471_);
lean_ctor_set(v_reuseFailAlloc_4487_, 41, v_ignored_4472_);
lean_ctor_set_uint8(v_reuseFailAlloc_4487_, sizeof(void*)*42, v_caseSplits_4466_);
v___x_4482_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
lean_object* v___x_4483_; lean_object* v___x_4485_; 
v___x_4483_ = lean_array_fset(v_xs_x27_4477_, v___y_4412_, v___x_4482_);
if (v_isShared_4428_ == 0)
{
lean_ctor_set(v___x_4427_, 0, v___x_4483_);
v___x_4485_ = v___x_4427_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v___x_4483_);
lean_ctor_set(v_reuseFailAlloc_4486_, 1, v_typeIdOf_4417_);
lean_ctor_set(v_reuseFailAlloc_4486_, 2, v_exprToStructId_4418_);
lean_ctor_set(v_reuseFailAlloc_4486_, 3, v_exprToStructIdEntries_4419_);
lean_ctor_set(v_reuseFailAlloc_4486_, 4, v_forbiddenNatModules_4420_);
lean_ctor_set(v_reuseFailAlloc_4486_, 5, v_natStructs_4421_);
lean_ctor_set(v_reuseFailAlloc_4486_, 6, v_natTypeIdOf_4422_);
lean_ctor_set(v_reuseFailAlloc_4486_, 7, v_exprToNatStructId_4423_);
v___x_4485_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
return v___x_4485_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed(lean_object* v___y_4498_, lean_object* v_snd_4499_, lean_object* v_fst_4500_, lean_object* v_s_4501_){
_start:
{
lean_object* v_res_4502_; 
v_res_4502_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(v___y_4498_, v_snd_4499_, v_fst_4500_, v_s_4501_);
lean_dec(v___y_4498_);
return v_res_4502_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1(void){
_start:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4504_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0));
v___x_4505_ = l_Lean_stringToMessageData(v___x_4504_);
return v___x_4505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object* v_c_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_){
_start:
{
lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4549_; lean_object* v___y_4550_; lean_object* v___y_4551_; lean_object* v___y_4552_; lean_object* v___y_4553_; lean_object* v___y_4554_; lean_object* v___y_4555_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4591_; lean_object* v___y_4592_; lean_object* v___y_4593_; lean_object* v___y_4594_; lean_object* v___y_4595_; lean_object* v___y_4596_; lean_object* v___y_4597_; lean_object* v___y_4598_; lean_object* v___y_4599_; lean_object* v___y_4600_; lean_object* v___y_4601_; lean_object* v___y_4602_; lean_object* v___y_4603_; lean_object* v___y_4604_; lean_object* v___y_4605_; lean_object* v___y_4606_; lean_object* v___y_4624_; lean_object* v___y_4625_; lean_object* v___y_4626_; lean_object* v___y_4627_; lean_object* v___y_4628_; lean_object* v___y_4629_; lean_object* v___y_4630_; lean_object* v___y_4631_; lean_object* v___y_4632_; lean_object* v___y_4633_; lean_object* v___y_4634_; lean_object* v_cls_4722_; lean_object* v___x_4723_; lean_object* v_a_4724_; uint8_t v___x_4725_; 
v_cls_4722_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0));
v___x_4723_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v_cls_4722_, v_a_4521_);
v_a_4724_ = lean_ctor_get(v___x_4723_, 0);
lean_inc(v_a_4724_);
lean_dec_ref(v___x_4723_);
v___x_4725_ = lean_unbox(v_a_4724_);
lean_dec(v_a_4724_);
if (v___x_4725_ == 0)
{
v___y_4624_ = v_a_4512_;
v___y_4625_ = v_a_4513_;
v___y_4626_ = v_a_4514_;
v___y_4627_ = v_a_4515_;
v___y_4628_ = v_a_4516_;
v___y_4629_ = v_a_4517_;
v___y_4630_ = v_a_4518_;
v___y_4631_ = v_a_4519_;
v___y_4632_ = v_a_4520_;
v___y_4633_ = v_a_4521_;
v___y_4634_ = v_a_4522_;
goto v___jp_4623_;
}
else
{
lean_object* v___x_4726_; 
v___x_4726_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_c_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
if (lean_obj_tag(v___x_4726_) == 0)
{
lean_object* v_a_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; 
v_a_4727_ = lean_ctor_get(v___x_4726_, 0);
lean_inc(v_a_4727_);
lean_dec_ref(v___x_4726_);
v___x_4728_ = l_Lean_MessageData_ofExpr(v_a_4727_);
v___x_4729_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_4722_, v___x_4728_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
if (lean_obj_tag(v___x_4729_) == 0)
{
lean_dec_ref(v___x_4729_);
v___y_4624_ = v_a_4512_;
v___y_4625_ = v_a_4513_;
v___y_4626_ = v_a_4514_;
v___y_4627_ = v_a_4515_;
v___y_4628_ = v_a_4516_;
v___y_4629_ = v_a_4517_;
v___y_4630_ = v_a_4518_;
v___y_4631_ = v_a_4519_;
v___y_4632_ = v_a_4520_;
v___y_4633_ = v_a_4521_;
v___y_4634_ = v_a_4522_;
goto v___jp_4623_;
}
else
{
lean_dec(v_a_4522_);
lean_dec_ref(v_a_4521_);
lean_dec(v_a_4520_);
lean_dec_ref(v_a_4519_);
lean_dec(v_a_4518_);
lean_dec_ref(v_a_4517_);
lean_dec(v_a_4516_);
lean_dec_ref(v_a_4515_);
lean_dec(v_a_4514_);
lean_dec(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec_ref(v_c_4511_);
return v___x_4729_;
}
}
else
{
lean_object* v_a_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4737_; 
lean_dec(v_a_4522_);
lean_dec_ref(v_a_4521_);
lean_dec(v_a_4520_);
lean_dec_ref(v_a_4519_);
lean_dec(v_a_4518_);
lean_dec_ref(v_a_4517_);
lean_dec(v_a_4516_);
lean_dec_ref(v_a_4515_);
lean_dec(v_a_4514_);
lean_dec(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec_ref(v_c_4511_);
v_a_4730_ = lean_ctor_get(v___x_4726_, 0);
v_isSharedCheck_4737_ = !lean_is_exclusive(v___x_4726_);
if (v_isSharedCheck_4737_ == 0)
{
v___x_4732_ = v___x_4726_;
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_a_4730_);
lean_dec(v___x_4726_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___x_4735_; 
if (v_isShared_4733_ == 0)
{
v___x_4735_ = v___x_4732_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4730_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
return v___x_4735_;
}
}
}
}
v___jp_4524_:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; 
v___x_4525_ = lean_box(0);
v___x_4526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4526_, 0, v___x_4525_);
return v___x_4526_;
}
v___jp_4527_:
{
lean_object* v___f_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; 
lean_inc(v___y_4533_);
v___f_4544_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4544_, 0, v___y_4533_);
lean_closure_set(v___f_4544_, 1, v___y_4529_);
lean_closure_set(v___f_4544_, 2, v___y_4528_);
v___x_4545_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4546_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4545_, v___f_4544_, v___y_4534_);
if (lean_obj_tag(v___x_4546_) == 0)
{
lean_object* v___x_4547_; 
lean_dec_ref(v___x_4546_);
v___x_4547_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_);
return v___x_4547_;
}
else
{
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec(v___y_4537_);
lean_dec_ref(v___y_4536_);
lean_dec(v___y_4535_);
lean_dec(v___y_4534_);
lean_dec(v___y_4533_);
lean_dec_ref(v___y_4532_);
lean_dec(v___y_4531_);
lean_dec(v___y_4530_);
return v___x_4546_;
}
}
v___jp_4548_:
{
lean_object* v___x_4565_; 
v___x_4565_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4565_) == 0)
{
lean_object* v_a_4566_; uint8_t v_caseSplits_4567_; 
v_a_4566_ = lean_ctor_get(v___x_4565_, 0);
lean_inc(v_a_4566_);
lean_dec_ref(v___x_4565_);
v_caseSplits_4567_ = lean_ctor_get_uint8(v_a_4566_, sizeof(void*)*42);
lean_dec(v_a_4566_);
if (v_caseSplits_4567_ == 0)
{
lean_object* v___x_4568_; 
v___x_4568_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4568_) == 0)
{
lean_object* v_a_4569_; uint8_t v___x_4570_; 
v_a_4569_ = lean_ctor_get(v___x_4568_, 0);
lean_inc(v_a_4569_);
lean_dec_ref(v___x_4568_);
v___x_4570_ = lean_unbox(v_a_4569_);
lean_dec(v_a_4569_);
if (v___x_4570_ == 0)
{
v___y_4528_ = v___y_4549_;
v___y_4529_ = v___y_4550_;
v___y_4530_ = v___y_4551_;
v___y_4531_ = v___y_4552_;
v___y_4532_ = v___y_4553_;
v___y_4533_ = v___y_4554_;
v___y_4534_ = v___y_4555_;
v___y_4535_ = v___y_4556_;
v___y_4536_ = v___y_4557_;
v___y_4537_ = v___y_4558_;
v___y_4538_ = v___y_4559_;
v___y_4539_ = v___y_4560_;
v___y_4540_ = v___y_4561_;
v___y_4541_ = v___y_4562_;
v___y_4542_ = v___y_4563_;
v___y_4543_ = v___y_4564_;
goto v___jp_4527_;
}
else
{
lean_object* v___x_4571_; lean_object* v_a_4572_; lean_object* v___x_4573_; 
lean_inc_ref(v___y_4553_);
v___x_4571_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v___y_4553_);
v_a_4572_ = lean_ctor_get(v___x_4571_, 0);
lean_inc(v_a_4572_);
lean_dec_ref(v___x_4571_);
lean_inc(v___y_4564_);
lean_inc_ref(v___y_4563_);
lean_inc(v___y_4562_);
lean_inc_ref(v___y_4561_);
lean_inc(v___y_4560_);
lean_inc_ref(v___y_4559_);
lean_inc(v___y_4558_);
lean_inc_ref(v___y_4557_);
lean_inc(v___y_4556_);
lean_inc(v___y_4555_);
lean_inc(v___y_4554_);
v___x_4573_ = l_Lean_Meta_Grind_Arith_Linear_propagateImpEq(v_a_4572_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4573_) == 0)
{
lean_dec_ref(v___x_4573_);
v___y_4528_ = v___y_4549_;
v___y_4529_ = v___y_4550_;
v___y_4530_ = v___y_4551_;
v___y_4531_ = v___y_4552_;
v___y_4532_ = v___y_4553_;
v___y_4533_ = v___y_4554_;
v___y_4534_ = v___y_4555_;
v___y_4535_ = v___y_4556_;
v___y_4536_ = v___y_4557_;
v___y_4537_ = v___y_4558_;
v___y_4538_ = v___y_4559_;
v___y_4539_ = v___y_4560_;
v___y_4540_ = v___y_4561_;
v___y_4541_ = v___y_4562_;
v___y_4542_ = v___y_4563_;
v___y_4543_ = v___y_4564_;
goto v___jp_4527_;
}
else
{
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
return v___x_4573_;
}
}
}
else
{
lean_object* v_a_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4581_; 
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
v_a_4574_ = lean_ctor_get(v___x_4568_, 0);
v_isSharedCheck_4581_ = !lean_is_exclusive(v___x_4568_);
if (v_isSharedCheck_4581_ == 0)
{
v___x_4576_ = v___x_4568_;
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_a_4574_);
lean_dec(v___x_4568_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v___x_4579_; 
if (v_isShared_4577_ == 0)
{
v___x_4579_ = v___x_4576_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v_a_4574_);
v___x_4579_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
return v___x_4579_;
}
}
}
}
else
{
v___y_4528_ = v___y_4549_;
v___y_4529_ = v___y_4550_;
v___y_4530_ = v___y_4551_;
v___y_4531_ = v___y_4552_;
v___y_4532_ = v___y_4553_;
v___y_4533_ = v___y_4554_;
v___y_4534_ = v___y_4555_;
v___y_4535_ = v___y_4556_;
v___y_4536_ = v___y_4557_;
v___y_4537_ = v___y_4558_;
v___y_4538_ = v___y_4559_;
v___y_4539_ = v___y_4560_;
v___y_4540_ = v___y_4561_;
v___y_4541_ = v___y_4562_;
v___y_4542_ = v___y_4563_;
v___y_4543_ = v___y_4564_;
goto v___jp_4527_;
}
}
else
{
lean_object* v_a_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4589_; 
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
v_a_4582_ = lean_ctor_get(v___x_4565_, 0);
v_isSharedCheck_4589_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4589_ == 0)
{
v___x_4584_ = v___x_4565_;
v_isShared_4585_ = v_isSharedCheck_4589_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_a_4582_);
lean_dec(v___x_4565_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4589_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v___x_4587_; 
if (v_isShared_4585_ == 0)
{
v___x_4587_ = v___x_4584_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v_a_4582_);
v___x_4587_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
return v___x_4587_;
}
}
}
}
v___jp_4590_:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v_a_4609_; uint8_t v___x_4610_; 
v___x_4607_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_4608_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_4607_, v___y_4605_);
v_a_4609_ = lean_ctor_get(v___x_4608_, 0);
lean_inc(v_a_4609_);
lean_dec_ref(v___x_4608_);
v___x_4610_ = lean_unbox(v_a_4609_);
lean_dec(v_a_4609_);
if (v___x_4610_ == 0)
{
v___y_4549_ = v___y_4591_;
v___y_4550_ = v___y_4592_;
v___y_4551_ = v___y_4593_;
v___y_4552_ = v___y_4594_;
v___y_4553_ = v___y_4595_;
v___y_4554_ = v___y_4596_;
v___y_4555_ = v___y_4597_;
v___y_4556_ = v___y_4598_;
v___y_4557_ = v___y_4599_;
v___y_4558_ = v___y_4600_;
v___y_4559_ = v___y_4601_;
v___y_4560_ = v___y_4602_;
v___y_4561_ = v___y_4603_;
v___y_4562_ = v___y_4604_;
v___y_4563_ = v___y_4605_;
v___y_4564_ = v___y_4606_;
goto v___jp_4548_;
}
else
{
lean_object* v___x_4611_; 
v___x_4611_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_object* v_a_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; 
v_a_4612_ = lean_ctor_get(v___x_4611_, 0);
lean_inc(v_a_4612_);
lean_dec_ref(v___x_4611_);
v___x_4613_ = l_Lean_MessageData_ofExpr(v_a_4612_);
v___x_4614_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_4607_, v___x_4613_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_dec_ref(v___x_4614_);
v___y_4549_ = v___y_4591_;
v___y_4550_ = v___y_4592_;
v___y_4551_ = v___y_4593_;
v___y_4552_ = v___y_4594_;
v___y_4553_ = v___y_4595_;
v___y_4554_ = v___y_4596_;
v___y_4555_ = v___y_4597_;
v___y_4556_ = v___y_4598_;
v___y_4557_ = v___y_4599_;
v___y_4558_ = v___y_4600_;
v___y_4559_ = v___y_4601_;
v___y_4560_ = v___y_4602_;
v___y_4561_ = v___y_4603_;
v___y_4562_ = v___y_4604_;
v___y_4563_ = v___y_4605_;
v___y_4564_ = v___y_4606_;
goto v___jp_4548_;
}
else
{
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4605_);
lean_dec(v___y_4604_);
lean_dec_ref(v___y_4603_);
lean_dec(v___y_4602_);
lean_dec_ref(v___y_4601_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
lean_dec(v___y_4598_);
lean_dec(v___y_4597_);
lean_dec(v___y_4596_);
lean_dec_ref(v___y_4595_);
lean_dec(v___y_4594_);
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
lean_dec(v___y_4591_);
return v___x_4614_;
}
}
else
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4622_; 
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4605_);
lean_dec(v___y_4604_);
lean_dec_ref(v___y_4603_);
lean_dec(v___y_4602_);
lean_dec_ref(v___y_4601_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
lean_dec(v___y_4598_);
lean_dec(v___y_4597_);
lean_dec(v___y_4596_);
lean_dec_ref(v___y_4595_);
lean_dec(v___y_4594_);
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
lean_dec(v___y_4591_);
v_a_4615_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4617_ = v___x_4611_;
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4611_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4620_; 
if (v_isShared_4618_ == 0)
{
v___x_4620_ = v___x_4617_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_a_4615_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
return v___x_4620_;
}
}
}
}
}
v___jp_4623_:
{
lean_object* v___x_4635_; 
lean_inc_ref(v___y_4633_);
v___x_4635_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_4511_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
if (lean_obj_tag(v___x_4635_) == 0)
{
lean_object* v_a_4636_; lean_object* v_p_4637_; lean_object* v___x_4638_; uint8_t v___x_4639_; 
v_a_4636_ = lean_ctor_get(v___x_4635_, 0);
lean_inc(v_a_4636_);
lean_dec_ref(v___x_4635_);
v_p_4637_ = lean_ctor_get(v_a_4636_, 0);
v___x_4638_ = lean_box(0);
v___x_4639_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_4637_, v___x_4638_);
if (v___x_4639_ == 0)
{
lean_object* v___x_4640_; 
lean_inc(v___y_4634_);
lean_inc_ref(v___y_4633_);
lean_inc(v___y_4632_);
lean_inc_ref(v___y_4631_);
lean_inc(v___y_4630_);
lean_inc_ref(v___y_4629_);
lean_inc(v___y_4628_);
lean_inc_ref(v___y_4627_);
lean_inc(v___y_4626_);
lean_inc(v___y_4625_);
lean_inc(v___y_4624_);
v___x_4640_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_a_4636_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
if (lean_obj_tag(v___x_4640_) == 0)
{
lean_object* v_a_4641_; lean_object* v_snd_4642_; lean_object* v_fst_4643_; lean_object* v___x_4645_; uint8_t v_isShared_4646_; uint8_t v_isSharedCheck_4689_; 
v_a_4641_ = lean_ctor_get(v___x_4640_, 0);
lean_inc(v_a_4641_);
lean_dec_ref(v___x_4640_);
v_snd_4642_ = lean_ctor_get(v_a_4641_, 1);
v_fst_4643_ = lean_ctor_get(v_a_4641_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v_a_4641_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4645_ = v_a_4641_;
v_isShared_4646_ = v_isSharedCheck_4689_;
goto v_resetjp_4644_;
}
else
{
lean_inc(v_snd_4642_);
lean_inc(v_fst_4643_);
lean_dec(v_a_4641_);
v___x_4645_ = lean_box(0);
v_isShared_4646_ = v_isSharedCheck_4689_;
goto v_resetjp_4644_;
}
v_resetjp_4644_:
{
lean_object* v_fst_4647_; lean_object* v_snd_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4688_; 
v_fst_4647_ = lean_ctor_get(v_snd_4642_, 0);
v_snd_4648_ = lean_ctor_get(v_snd_4642_, 1);
v_isSharedCheck_4688_ = !lean_is_exclusive(v_snd_4642_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4650_ = v_snd_4642_;
v_isShared_4651_ = v_isSharedCheck_4688_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_snd_4648_);
lean_inc(v_fst_4647_);
lean_dec(v_snd_4642_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4688_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v_a_4654_; uint8_t v___x_4655_; 
v___x_4652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_4653_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_4652_, v___y_4633_);
v_a_4654_ = lean_ctor_get(v___x_4653_, 0);
lean_inc(v_a_4654_);
lean_dec_ref(v___x_4653_);
v___x_4655_ = lean_unbox(v_a_4654_);
lean_dec(v_a_4654_);
if (v___x_4655_ == 0)
{
lean_del_object(v___x_4650_);
lean_del_object(v___x_4645_);
lean_inc(v_snd_4648_);
lean_inc(v_fst_4647_);
v___y_4591_ = v_fst_4647_;
v___y_4592_ = v_snd_4648_;
v___y_4593_ = v_fst_4643_;
v___y_4594_ = v_fst_4647_;
v___y_4595_ = v_snd_4648_;
v___y_4596_ = v___y_4624_;
v___y_4597_ = v___y_4625_;
v___y_4598_ = v___y_4626_;
v___y_4599_ = v___y_4627_;
v___y_4600_ = v___y_4628_;
v___y_4601_ = v___y_4629_;
v___y_4602_ = v___y_4630_;
v___y_4603_ = v___y_4631_;
v___y_4604_ = v___y_4632_;
v___y_4605_ = v___y_4633_;
v___y_4606_ = v___y_4634_;
goto v___jp_4590_;
}
else
{
lean_object* v___x_4656_; 
v___x_4656_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_4647_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
if (lean_obj_tag(v___x_4656_) == 0)
{
lean_object* v_a_4657_; lean_object* v___x_4658_; 
v_a_4657_ = lean_ctor_get(v___x_4656_, 0);
lean_inc(v_a_4657_);
lean_dec_ref(v___x_4656_);
v___x_4658_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_snd_4648_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
if (lean_obj_tag(v___x_4658_) == 0)
{
lean_object* v_a_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4663_; 
v_a_4659_ = lean_ctor_get(v___x_4658_, 0);
lean_inc(v_a_4659_);
lean_dec_ref(v___x_4658_);
v___x_4660_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1);
v___x_4661_ = l_Lean_MessageData_ofExpr(v_a_4657_);
if (v_isShared_4651_ == 0)
{
lean_ctor_set_tag(v___x_4650_, 7);
lean_ctor_set(v___x_4650_, 1, v___x_4661_);
lean_ctor_set(v___x_4650_, 0, v___x_4660_);
v___x_4663_ = v___x_4650_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v___x_4660_);
lean_ctor_set(v_reuseFailAlloc_4671_, 1, v___x_4661_);
v___x_4663_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
lean_object* v___x_4664_; lean_object* v___x_4666_; 
v___x_4664_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6);
if (v_isShared_4646_ == 0)
{
lean_ctor_set_tag(v___x_4645_, 7);
lean_ctor_set(v___x_4645_, 1, v___x_4664_);
lean_ctor_set(v___x_4645_, 0, v___x_4663_);
v___x_4666_ = v___x_4645_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v___x_4663_);
lean_ctor_set(v_reuseFailAlloc_4670_, 1, v___x_4664_);
v___x_4666_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; 
v___x_4667_ = l_Lean_MessageData_ofExpr(v_a_4659_);
v___x_4668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4668_, 0, v___x_4666_);
lean_ctor_set(v___x_4668_, 1, v___x_4667_);
v___x_4669_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_4652_, v___x_4668_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
if (lean_obj_tag(v___x_4669_) == 0)
{
lean_dec_ref(v___x_4669_);
lean_inc(v_snd_4648_);
lean_inc(v_fst_4647_);
v___y_4591_ = v_fst_4647_;
v___y_4592_ = v_snd_4648_;
v___y_4593_ = v_fst_4643_;
v___y_4594_ = v_fst_4647_;
v___y_4595_ = v_snd_4648_;
v___y_4596_ = v___y_4624_;
v___y_4597_ = v___y_4625_;
v___y_4598_ = v___y_4626_;
v___y_4599_ = v___y_4627_;
v___y_4600_ = v___y_4628_;
v___y_4601_ = v___y_4629_;
v___y_4602_ = v___y_4630_;
v___y_4603_ = v___y_4631_;
v___y_4604_ = v___y_4632_;
v___y_4605_ = v___y_4633_;
v___y_4606_ = v___y_4634_;
goto v___jp_4590_;
}
else
{
lean_dec(v_snd_4648_);
lean_dec(v_fst_4647_);
lean_dec(v_fst_4643_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v___y_4630_);
lean_dec_ref(v___y_4629_);
lean_dec(v___y_4628_);
lean_dec_ref(v___y_4627_);
lean_dec(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec(v___y_4624_);
return v___x_4669_;
}
}
}
}
else
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4679_; 
lean_dec(v_a_4657_);
lean_del_object(v___x_4650_);
lean_dec(v_snd_4648_);
lean_dec(v_fst_4647_);
lean_del_object(v___x_4645_);
lean_dec(v_fst_4643_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v___y_4630_);
lean_dec_ref(v___y_4629_);
lean_dec(v___y_4628_);
lean_dec_ref(v___y_4627_);
lean_dec(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec(v___y_4624_);
v_a_4672_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4679_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4674_ = v___x_4658_;
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4658_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4677_; 
if (v_isShared_4675_ == 0)
{
v___x_4677_ = v___x_4674_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4672_);
v___x_4677_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
return v___x_4677_;
}
}
}
}
else
{
lean_object* v_a_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4687_; 
lean_del_object(v___x_4650_);
lean_dec(v_snd_4648_);
lean_dec(v_fst_4647_);
lean_del_object(v___x_4645_);
lean_dec(v_fst_4643_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v___y_4630_);
lean_dec_ref(v___y_4629_);
lean_dec(v___y_4628_);
lean_dec_ref(v___y_4627_);
lean_dec(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec(v___y_4624_);
v_a_4680_ = lean_ctor_get(v___x_4656_, 0);
v_isSharedCheck_4687_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4687_ == 0)
{
v___x_4682_ = v___x_4656_;
v_isShared_4683_ = v_isSharedCheck_4687_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_a_4680_);
lean_dec(v___x_4656_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4687_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v___x_4685_; 
if (v_isShared_4683_ == 0)
{
v___x_4685_ = v___x_4682_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v_a_4680_);
v___x_4685_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
return v___x_4685_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4697_; 
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v___y_4630_);
lean_dec_ref(v___y_4629_);
lean_dec(v___y_4628_);
lean_dec_ref(v___y_4627_);
lean_dec(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec(v___y_4624_);
v_a_4690_ = lean_ctor_get(v___x_4640_, 0);
v_isSharedCheck_4697_ = !lean_is_exclusive(v___x_4640_);
if (v_isSharedCheck_4697_ == 0)
{
v___x_4692_ = v___x_4640_;
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_a_4690_);
lean_dec(v___x_4640_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v___x_4695_; 
if (v_isShared_4693_ == 0)
{
v___x_4695_ = v___x_4692_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_a_4690_);
v___x_4695_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
return v___x_4695_;
}
}
}
}
else
{
lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v_a_4700_; uint8_t v___x_4701_; 
v___x_4698_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4699_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v___x_4698_, v___y_4633_);
v_a_4700_ = lean_ctor_get(v___x_4699_, 0);
lean_inc(v_a_4700_);
lean_dec_ref(v___x_4699_);
v___x_4701_ = lean_unbox(v_a_4700_);
lean_dec(v_a_4700_);
if (v___x_4701_ == 0)
{
lean_dec(v_a_4636_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v___y_4630_);
lean_dec_ref(v___y_4629_);
lean_dec(v___y_4628_);
lean_dec_ref(v___y_4627_);
lean_dec(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec(v___y_4624_);
goto v___jp_4524_;
}
else
{
lean_object* v___x_4702_; 
v___x_4702_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_a_4636_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
lean_dec(v___y_4630_);
lean_dec_ref(v___y_4629_);
lean_dec(v___y_4628_);
lean_dec_ref(v___y_4627_);
lean_dec(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec(v___y_4624_);
lean_dec(v_a_4636_);
if (lean_obj_tag(v___x_4702_) == 0)
{
lean_object* v_a_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; 
v_a_4703_ = lean_ctor_get(v___x_4702_, 0);
lean_inc(v_a_4703_);
lean_dec_ref(v___x_4702_);
v___x_4704_ = l_Lean_MessageData_ofExpr(v_a_4703_);
v___x_4705_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v___x_4698_, v___x_4704_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
if (lean_obj_tag(v___x_4705_) == 0)
{
lean_dec_ref(v___x_4705_);
goto v___jp_4524_;
}
else
{
return v___x_4705_;
}
}
else
{
lean_object* v_a_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4713_; 
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
v_a_4706_ = lean_ctor_get(v___x_4702_, 0);
v_isSharedCheck_4713_ = !lean_is_exclusive(v___x_4702_);
if (v_isSharedCheck_4713_ == 0)
{
v___x_4708_ = v___x_4702_;
v_isShared_4709_ = v_isSharedCheck_4713_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_a_4706_);
lean_dec(v___x_4702_);
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
else
{
lean_object* v_a_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4721_; 
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v___y_4630_);
lean_dec_ref(v___y_4629_);
lean_dec(v___y_4628_);
lean_dec_ref(v___y_4627_);
lean_dec(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec(v___y_4624_);
v_a_4714_ = lean_ctor_get(v___x_4635_, 0);
v_isSharedCheck_4721_ = !lean_is_exclusive(v___x_4635_);
if (v_isSharedCheck_4721_ == 0)
{
v___x_4716_ = v___x_4635_;
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_a_4714_);
lean_dec(v___x_4635_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v___x_4719_; 
if (v_isShared_4717_ == 0)
{
v___x_4719_ = v___x_4716_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v_a_4714_);
v___x_4719_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
return v___x_4719_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object* v_c_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_){
_start:
{
lean_object* v_res_4751_; 
v_res_4751_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v_c_4738_, v_a_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_);
return v_res_4751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object* v_a_4756_, lean_object* v_b_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_){
_start:
{
lean_object* v_cls_4763_; lean_object* v___x_4764_; lean_object* v_a_4765_; lean_object* v___x_4767_; uint8_t v_isShared_4768_; uint8_t v_isSharedCheck_4780_; 
v_cls_4763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4764_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___redArg(v_cls_4763_, v_a_4760_);
v_a_4765_ = lean_ctor_get(v___x_4764_, 0);
v_isSharedCheck_4780_ = !lean_is_exclusive(v___x_4764_);
if (v_isSharedCheck_4780_ == 0)
{
v___x_4767_ = v___x_4764_;
v_isShared_4768_ = v_isSharedCheck_4780_;
goto v_resetjp_4766_;
}
else
{
lean_inc(v_a_4765_);
lean_dec(v___x_4764_);
v___x_4767_ = lean_box(0);
v_isShared_4768_ = v_isSharedCheck_4780_;
goto v_resetjp_4766_;
}
v_resetjp_4766_:
{
uint8_t v___x_4769_; 
v___x_4769_ = lean_unbox(v_a_4765_);
lean_dec(v_a_4765_);
if (v___x_4769_ == 0)
{
lean_object* v___x_4770_; lean_object* v___x_4772_; 
lean_dec_ref(v_b_4757_);
lean_dec_ref(v_a_4756_);
v___x_4770_ = lean_box(0);
if (v_isShared_4768_ == 0)
{
lean_ctor_set(v___x_4767_, 0, v___x_4770_);
v___x_4772_ = v___x_4767_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v___x_4770_);
v___x_4772_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
return v___x_4772_;
}
}
else
{
lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; 
lean_del_object(v___x_4767_);
v___x_4774_ = l_Lean_MessageData_ofExpr(v_a_4756_);
v___x_4775_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6);
v___x_4776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4776_, 0, v___x_4774_);
lean_ctor_set(v___x_4776_, 1, v___x_4775_);
v___x_4777_ = l_Lean_MessageData_ofExpr(v_b_4757_);
v___x_4778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4778_, 0, v___x_4776_);
lean_ctor_set(v___x_4778_, 1, v___x_4777_);
v___x_4779_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__3___redArg(v_cls_4763_, v___x_4778_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
return v___x_4779_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object* v_a_4781_, lean_object* v_b_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_){
_start:
{
lean_object* v_res_4788_; 
v_res_4788_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4781_, v_b_4782_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
lean_dec(v_a_4786_);
lean_dec_ref(v_a_4785_);
lean_dec(v_a_4784_);
lean_dec_ref(v_a_4783_);
return v_res_4788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object* v_a_4789_, lean_object* v_b_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_){
_start:
{
lean_object* v___x_4803_; 
v___x_4803_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4789_, v_b_4790_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_);
return v___x_4803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object* v_a_4804_, lean_object* v_b_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_){
_start:
{
lean_object* v_res_4818_; 
v_res_4818_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(v_a_4804_, v_b_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
lean_dec(v_a_4816_);
lean_dec_ref(v_a_4815_);
lean_dec(v_a_4814_);
lean_dec_ref(v_a_4813_);
lean_dec(v_a_4812_);
lean_dec_ref(v_a_4811_);
lean_dec(v_a_4810_);
lean_dec_ref(v_a_4809_);
lean_dec(v_a_4808_);
lean_dec(v_a_4807_);
lean_dec(v_a_4806_);
return v_res_4818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object* v_a_4819_, lean_object* v_b_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_){
_start:
{
lean_object* v___x_4833_; 
v___x_4833_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4819_, v_a_4822_);
if (lean_obj_tag(v___x_4833_) == 0)
{
lean_object* v_a_4834_; uint8_t v___x_4835_; lean_object* v___x_4836_; 
v_a_4834_ = lean_ctor_get(v___x_4833_, 0);
lean_inc(v_a_4834_);
lean_dec_ref(v___x_4833_);
v___x_4835_ = 0;
lean_inc(v_a_4831_);
lean_inc_ref(v_a_4830_);
lean_inc(v_a_4829_);
lean_inc_ref(v_a_4828_);
lean_inc(v_a_4827_);
lean_inc_ref(v_a_4826_);
lean_inc(v_a_4825_);
lean_inc_ref(v_a_4824_);
lean_inc(v_a_4823_);
lean_inc(v_a_4822_);
lean_inc(v_a_4821_);
lean_inc_ref(v_a_4819_);
v___x_4836_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_4819_, v___x_4835_, v_a_4834_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
if (lean_obj_tag(v___x_4836_) == 0)
{
lean_object* v_a_4837_; lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4886_; 
v_a_4837_ = lean_ctor_get(v___x_4836_, 0);
v_isSharedCheck_4886_ = !lean_is_exclusive(v___x_4836_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4839_ = v___x_4836_;
v_isShared_4840_ = v_isSharedCheck_4886_;
goto v_resetjp_4838_;
}
else
{
lean_inc(v_a_4837_);
lean_dec(v___x_4836_);
v___x_4839_ = lean_box(0);
v_isShared_4840_ = v_isSharedCheck_4886_;
goto v_resetjp_4838_;
}
v_resetjp_4838_:
{
if (lean_obj_tag(v_a_4837_) == 1)
{
lean_object* v_val_4841_; lean_object* v___x_4842_; 
lean_del_object(v___x_4839_);
v_val_4841_ = lean_ctor_get(v_a_4837_, 0);
lean_inc(v_val_4841_);
lean_dec_ref(v_a_4837_);
v___x_4842_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4820_, v_a_4822_);
if (lean_obj_tag(v___x_4842_) == 0)
{
lean_object* v_a_4843_; lean_object* v___x_4844_; 
v_a_4843_ = lean_ctor_get(v___x_4842_, 0);
lean_inc(v_a_4843_);
lean_dec_ref(v___x_4842_);
lean_inc(v_a_4831_);
lean_inc_ref(v_a_4830_);
lean_inc(v_a_4829_);
lean_inc_ref(v_a_4828_);
lean_inc(v_a_4827_);
lean_inc_ref(v_a_4826_);
lean_inc(v_a_4825_);
lean_inc_ref(v_a_4824_);
lean_inc(v_a_4823_);
lean_inc(v_a_4822_);
lean_inc(v_a_4821_);
lean_inc_ref(v_b_4820_);
v___x_4844_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_4820_, v___x_4835_, v_a_4843_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
if (lean_obj_tag(v___x_4844_) == 0)
{
lean_object* v_a_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4865_; 
v_a_4845_ = lean_ctor_get(v___x_4844_, 0);
v_isSharedCheck_4865_ = !lean_is_exclusive(v___x_4844_);
if (v_isSharedCheck_4865_ == 0)
{
v___x_4847_ = v___x_4844_;
v_isShared_4848_ = v_isSharedCheck_4865_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_a_4845_);
lean_dec(v___x_4844_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4865_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
if (lean_obj_tag(v_a_4845_) == 1)
{
lean_object* v_val_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; uint8_t v___x_4853_; 
v_val_4849_ = lean_ctor_get(v_a_4845_, 0);
lean_inc(v_val_4849_);
lean_dec_ref(v_a_4845_);
lean_inc(v_val_4849_);
lean_inc(v_val_4841_);
v___x_4850_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4850_, 0, v_val_4841_);
lean_ctor_set(v___x_4850_, 1, v_val_4849_);
v___x_4851_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4850_);
v___x_4852_ = lean_box(0);
v___x_4853_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4851_, v___x_4852_);
if (v___x_4853_ == 0)
{
lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; 
lean_del_object(v___x_4847_);
v___x_4854_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4854_, 0, v_a_4819_);
lean_ctor_set(v___x_4854_, 1, v_b_4820_);
lean_ctor_set(v___x_4854_, 2, v_val_4841_);
lean_ctor_set(v___x_4854_, 3, v_val_4849_);
v___x_4855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4855_, 0, v___x_4851_);
lean_ctor_set(v___x_4855_, 1, v___x_4854_);
v___x_4856_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_4855_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
return v___x_4856_;
}
else
{
lean_object* v___x_4857_; lean_object* v___x_4859_; 
lean_dec(v___x_4851_);
lean_dec(v_val_4849_);
lean_dec(v_val_4841_);
lean_dec(v_a_4831_);
lean_dec_ref(v_a_4830_);
lean_dec(v_a_4829_);
lean_dec_ref(v_a_4828_);
lean_dec(v_a_4827_);
lean_dec_ref(v_a_4826_);
lean_dec(v_a_4825_);
lean_dec_ref(v_a_4824_);
lean_dec(v_a_4823_);
lean_dec(v_a_4822_);
lean_dec(v_a_4821_);
lean_dec_ref(v_b_4820_);
lean_dec_ref(v_a_4819_);
v___x_4857_ = lean_box(0);
if (v_isShared_4848_ == 0)
{
lean_ctor_set(v___x_4847_, 0, v___x_4857_);
v___x_4859_ = v___x_4847_;
goto v_reusejp_4858_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v___x_4857_);
v___x_4859_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4858_;
}
v_reusejp_4858_:
{
return v___x_4859_;
}
}
}
else
{
lean_object* v___x_4861_; lean_object* v___x_4863_; 
lean_dec(v_a_4845_);
lean_dec(v_val_4841_);
lean_dec(v_a_4831_);
lean_dec_ref(v_a_4830_);
lean_dec(v_a_4829_);
lean_dec_ref(v_a_4828_);
lean_dec(v_a_4827_);
lean_dec_ref(v_a_4826_);
lean_dec(v_a_4825_);
lean_dec_ref(v_a_4824_);
lean_dec(v_a_4823_);
lean_dec(v_a_4822_);
lean_dec(v_a_4821_);
lean_dec_ref(v_b_4820_);
lean_dec_ref(v_a_4819_);
v___x_4861_ = lean_box(0);
if (v_isShared_4848_ == 0)
{
lean_ctor_set(v___x_4847_, 0, v___x_4861_);
v___x_4863_ = v___x_4847_;
goto v_reusejp_4862_;
}
else
{
lean_object* v_reuseFailAlloc_4864_; 
v_reuseFailAlloc_4864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4864_, 0, v___x_4861_);
v___x_4863_ = v_reuseFailAlloc_4864_;
goto v_reusejp_4862_;
}
v_reusejp_4862_:
{
return v___x_4863_;
}
}
}
}
else
{
lean_object* v_a_4866_; lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4873_; 
lean_dec(v_val_4841_);
lean_dec(v_a_4831_);
lean_dec_ref(v_a_4830_);
lean_dec(v_a_4829_);
lean_dec_ref(v_a_4828_);
lean_dec(v_a_4827_);
lean_dec_ref(v_a_4826_);
lean_dec(v_a_4825_);
lean_dec_ref(v_a_4824_);
lean_dec(v_a_4823_);
lean_dec(v_a_4822_);
lean_dec(v_a_4821_);
lean_dec_ref(v_b_4820_);
lean_dec_ref(v_a_4819_);
v_a_4866_ = lean_ctor_get(v___x_4844_, 0);
v_isSharedCheck_4873_ = !lean_is_exclusive(v___x_4844_);
if (v_isSharedCheck_4873_ == 0)
{
v___x_4868_ = v___x_4844_;
v_isShared_4869_ = v_isSharedCheck_4873_;
goto v_resetjp_4867_;
}
else
{
lean_inc(v_a_4866_);
lean_dec(v___x_4844_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4873_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
lean_object* v___x_4871_; 
if (v_isShared_4869_ == 0)
{
v___x_4871_ = v___x_4868_;
goto v_reusejp_4870_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v_a_4866_);
v___x_4871_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4870_;
}
v_reusejp_4870_:
{
return v___x_4871_;
}
}
}
}
else
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4881_; 
lean_dec(v_val_4841_);
lean_dec(v_a_4831_);
lean_dec_ref(v_a_4830_);
lean_dec(v_a_4829_);
lean_dec_ref(v_a_4828_);
lean_dec(v_a_4827_);
lean_dec_ref(v_a_4826_);
lean_dec(v_a_4825_);
lean_dec_ref(v_a_4824_);
lean_dec(v_a_4823_);
lean_dec(v_a_4822_);
lean_dec(v_a_4821_);
lean_dec_ref(v_b_4820_);
lean_dec_ref(v_a_4819_);
v_a_4874_ = lean_ctor_get(v___x_4842_, 0);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4842_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4876_ = v___x_4842_;
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4842_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4879_; 
if (v_isShared_4877_ == 0)
{
v___x_4879_ = v___x_4876_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_a_4874_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
}
else
{
lean_object* v___x_4882_; lean_object* v___x_4884_; 
lean_dec(v_a_4837_);
lean_dec(v_a_4831_);
lean_dec_ref(v_a_4830_);
lean_dec(v_a_4829_);
lean_dec_ref(v_a_4828_);
lean_dec(v_a_4827_);
lean_dec_ref(v_a_4826_);
lean_dec(v_a_4825_);
lean_dec_ref(v_a_4824_);
lean_dec(v_a_4823_);
lean_dec(v_a_4822_);
lean_dec(v_a_4821_);
lean_dec_ref(v_b_4820_);
lean_dec_ref(v_a_4819_);
v___x_4882_ = lean_box(0);
if (v_isShared_4840_ == 0)
{
lean_ctor_set(v___x_4839_, 0, v___x_4882_);
v___x_4884_ = v___x_4839_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v___x_4882_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
}
}
else
{
lean_object* v_a_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4894_; 
lean_dec(v_a_4831_);
lean_dec_ref(v_a_4830_);
lean_dec(v_a_4829_);
lean_dec_ref(v_a_4828_);
lean_dec(v_a_4827_);
lean_dec_ref(v_a_4826_);
lean_dec(v_a_4825_);
lean_dec_ref(v_a_4824_);
lean_dec(v_a_4823_);
lean_dec(v_a_4822_);
lean_dec(v_a_4821_);
lean_dec_ref(v_b_4820_);
lean_dec_ref(v_a_4819_);
v_a_4887_ = lean_ctor_get(v___x_4836_, 0);
v_isSharedCheck_4894_ = !lean_is_exclusive(v___x_4836_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4889_ = v___x_4836_;
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_a_4887_);
lean_dec(v___x_4836_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v___x_4892_; 
if (v_isShared_4890_ == 0)
{
v___x_4892_ = v___x_4889_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v_a_4887_);
v___x_4892_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
return v___x_4892_;
}
}
}
}
else
{
lean_object* v_a_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4902_; 
lean_dec(v_a_4831_);
lean_dec_ref(v_a_4830_);
lean_dec(v_a_4829_);
lean_dec_ref(v_a_4828_);
lean_dec(v_a_4827_);
lean_dec_ref(v_a_4826_);
lean_dec(v_a_4825_);
lean_dec_ref(v_a_4824_);
lean_dec(v_a_4823_);
lean_dec(v_a_4822_);
lean_dec(v_a_4821_);
lean_dec_ref(v_b_4820_);
lean_dec_ref(v_a_4819_);
v_a_4895_ = lean_ctor_get(v___x_4833_, 0);
v_isSharedCheck_4902_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4897_ = v___x_4833_;
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_a_4895_);
lean_dec(v___x_4833_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4900_; 
if (v_isShared_4898_ == 0)
{
v___x_4900_ = v___x_4897_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_a_4895_);
v___x_4900_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
return v___x_4900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___boxed(lean_object* v_a_4903_, lean_object* v_b_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_){
_start:
{
lean_object* v_res_4917_; 
v_res_4917_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_4903_, v_b_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_);
return v_res_4917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(lean_object* v_a_4918_, lean_object* v_b_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_){
_start:
{
lean_object* v___x_4932_; 
v___x_4932_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_);
if (lean_obj_tag(v___x_4932_) == 0)
{
lean_object* v_a_4933_; lean_object* v___x_4934_; 
v_a_4933_ = lean_ctor_get(v___x_4932_, 0);
lean_inc(v_a_4933_);
lean_dec_ref(v___x_4932_);
lean_inc(v_a_4930_);
lean_inc_ref(v_a_4929_);
lean_inc(v_a_4928_);
lean_inc_ref(v_a_4927_);
lean_inc(v_a_4926_);
lean_inc_ref(v_a_4925_);
lean_inc(v_a_4924_);
lean_inc_ref(v_a_4923_);
lean_inc(v_a_4922_);
lean_inc(v_a_4921_);
lean_inc(v_a_4920_);
lean_inc_ref(v_a_4918_);
v___x_4934_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_4918_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_);
if (lean_obj_tag(v___x_4934_) == 0)
{
lean_object* v_a_4935_; lean_object* v_fst_4936_; lean_object* v___x_4937_; 
v_a_4935_ = lean_ctor_get(v___x_4934_, 0);
lean_inc(v_a_4935_);
lean_dec_ref(v___x_4934_);
v_fst_4936_ = lean_ctor_get(v_a_4935_, 0);
lean_inc(v_fst_4936_);
lean_dec(v_a_4935_);
lean_inc(v_a_4930_);
lean_inc_ref(v_a_4929_);
lean_inc(v_a_4928_);
lean_inc_ref(v_a_4927_);
lean_inc(v_a_4926_);
lean_inc_ref(v_a_4925_);
lean_inc(v_a_4924_);
lean_inc_ref(v_a_4923_);
lean_inc(v_a_4922_);
lean_inc(v_a_4921_);
lean_inc_ref(v_b_4919_);
v___x_4937_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_);
if (lean_obj_tag(v___x_4937_) == 0)
{
lean_object* v_a_4938_; lean_object* v_fst_4939_; lean_object* v___x_4941_; uint8_t v_isShared_4942_; uint8_t v_isSharedCheck_5022_; 
v_a_4938_ = lean_ctor_get(v___x_4937_, 0);
lean_inc(v_a_4938_);
lean_dec_ref(v___x_4937_);
v_fst_4939_ = lean_ctor_get(v_a_4938_, 0);
v_isSharedCheck_5022_ = !lean_is_exclusive(v_a_4938_);
if (v_isSharedCheck_5022_ == 0)
{
lean_object* v_unused_5023_; 
v_unused_5023_ = lean_ctor_get(v_a_4938_, 1);
lean_dec(v_unused_5023_);
v___x_4941_ = v_a_4938_;
v_isShared_4942_ = v_isSharedCheck_5022_;
goto v_resetjp_4940_;
}
else
{
lean_inc(v_fst_4939_);
lean_dec(v_a_4938_);
v___x_4941_ = lean_box(0);
v_isShared_4942_ = v_isSharedCheck_5022_;
goto v_resetjp_4940_;
}
v_resetjp_4940_:
{
lean_object* v___x_4943_; 
v___x_4943_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4918_, v_a_4921_);
if (lean_obj_tag(v___x_4943_) == 0)
{
lean_object* v_a_4944_; lean_object* v_id_4945_; lean_object* v_structId_4946_; uint8_t v___x_4947_; lean_object* v___x_4948_; 
v_a_4944_ = lean_ctor_get(v___x_4943_, 0);
lean_inc(v_a_4944_);
lean_dec_ref(v___x_4943_);
v_id_4945_ = lean_ctor_get(v_a_4933_, 0);
lean_inc(v_id_4945_);
v_structId_4946_ = lean_ctor_get(v_a_4933_, 1);
lean_inc(v_structId_4946_);
lean_dec(v_a_4933_);
v___x_4947_ = 0;
lean_inc(v_a_4930_);
lean_inc_ref(v_a_4929_);
lean_inc(v_a_4928_);
lean_inc_ref(v_a_4927_);
lean_inc(v_a_4926_);
lean_inc_ref(v_a_4925_);
lean_inc(v_a_4924_);
lean_inc_ref(v_a_4923_);
lean_inc(v_a_4922_);
lean_inc(v_a_4921_);
lean_inc(v_structId_4946_);
v___x_4948_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4936_, v___x_4947_, v_a_4944_, v_structId_4946_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_);
if (lean_obj_tag(v___x_4948_) == 0)
{
lean_object* v_a_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_5005_; 
v_a_4949_ = lean_ctor_get(v___x_4948_, 0);
v_isSharedCheck_5005_ = !lean_is_exclusive(v___x_4948_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_4951_ = v___x_4948_;
v_isShared_4952_ = v_isSharedCheck_5005_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_a_4949_);
lean_dec(v___x_4948_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_5005_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
if (lean_obj_tag(v_a_4949_) == 1)
{
lean_object* v_val_4953_; lean_object* v___x_4954_; 
lean_del_object(v___x_4951_);
v_val_4953_ = lean_ctor_get(v_a_4949_, 0);
lean_inc(v_val_4953_);
lean_dec_ref(v_a_4949_);
v___x_4954_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4919_, v_a_4921_);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_object* v_a_4955_; lean_object* v___x_4956_; 
v_a_4955_ = lean_ctor_get(v___x_4954_, 0);
lean_inc(v_a_4955_);
lean_dec_ref(v___x_4954_);
lean_inc(v_a_4930_);
lean_inc_ref(v_a_4929_);
lean_inc(v_a_4928_);
lean_inc_ref(v_a_4927_);
lean_inc(v_a_4926_);
lean_inc_ref(v_a_4925_);
lean_inc(v_a_4924_);
lean_inc_ref(v_a_4923_);
lean_inc(v_a_4922_);
lean_inc(v_a_4921_);
lean_inc(v_structId_4946_);
v___x_4956_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4939_, v___x_4947_, v_a_4955_, v_structId_4946_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_);
if (lean_obj_tag(v___x_4956_) == 0)
{
lean_object* v_a_4957_; lean_object* v___x_4959_; uint8_t v_isShared_4960_; uint8_t v_isSharedCheck_4984_; 
v_a_4957_ = lean_ctor_get(v___x_4956_, 0);
v_isSharedCheck_4984_ = !lean_is_exclusive(v___x_4956_);
if (v_isSharedCheck_4984_ == 0)
{
v___x_4959_ = v___x_4956_;
v_isShared_4960_ = v_isSharedCheck_4984_;
goto v_resetjp_4958_;
}
else
{
lean_inc(v_a_4957_);
lean_dec(v___x_4956_);
v___x_4959_ = lean_box(0);
v_isShared_4960_ = v_isSharedCheck_4984_;
goto v_resetjp_4958_;
}
v_resetjp_4958_:
{
if (lean_obj_tag(v_a_4957_) == 1)
{
lean_object* v_val_4961_; lean_object* v___x_4963_; 
v_val_4961_ = lean_ctor_get(v_a_4957_, 0);
lean_inc(v_val_4961_);
lean_dec_ref(v_a_4957_);
lean_inc(v_val_4961_);
lean_inc(v_val_4953_);
if (v_isShared_4942_ == 0)
{
lean_ctor_set_tag(v___x_4941_, 3);
lean_ctor_set(v___x_4941_, 1, v_val_4961_);
lean_ctor_set(v___x_4941_, 0, v_val_4953_);
v___x_4963_ = v___x_4941_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_val_4953_);
lean_ctor_set(v_reuseFailAlloc_4979_, 1, v_val_4961_);
v___x_4963_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4962_;
}
v_reusejp_4962_:
{
lean_object* v___x_4964_; lean_object* v___x_4965_; uint8_t v___x_4966_; 
v___x_4964_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4963_);
v___x_4965_ = lean_box(0);
v___x_4966_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4964_, v___x_4965_);
if (v___x_4966_ == 0)
{
lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
lean_del_object(v___x_4959_);
lean_inc(v_val_4961_);
lean_inc(v_val_4953_);
lean_inc(v_id_4945_);
lean_inc_ref(v_b_4919_);
lean_inc_ref(v_a_4918_);
v___x_4967_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4967_, 0, v_a_4918_);
lean_ctor_set(v___x_4967_, 1, v_b_4919_);
lean_ctor_set(v___x_4967_, 2, v_id_4945_);
lean_ctor_set(v___x_4967_, 3, v_val_4953_);
lean_ctor_set(v___x_4967_, 4, v_val_4961_);
lean_inc(v___x_4964_);
v___x_4968_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4968_, 0, v___x_4964_);
lean_ctor_set(v___x_4968_, 1, v___x_4967_);
lean_ctor_set_uint8(v___x_4968_, sizeof(void*)*2, v___x_4947_);
lean_inc(v_a_4930_);
lean_inc_ref(v_a_4929_);
lean_inc(v_a_4928_);
lean_inc_ref(v_a_4927_);
lean_inc(v_a_4926_);
lean_inc_ref(v_a_4925_);
lean_inc(v_a_4924_);
lean_inc_ref(v_a_4923_);
lean_inc(v_a_4922_);
lean_inc(v_a_4921_);
lean_inc(v_structId_4946_);
v___x_4969_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4968_, v_structId_4946_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_);
if (lean_obj_tag(v___x_4969_) == 0)
{
lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; 
lean_dec_ref(v___x_4969_);
v___x_4970_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4971_ = l_Lean_Grind_Linarith_Poly_mul(v___x_4964_, v___x_4970_);
v___x_4972_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4972_, 0, v_b_4919_);
lean_ctor_set(v___x_4972_, 1, v_a_4918_);
lean_ctor_set(v___x_4972_, 2, v_id_4945_);
lean_ctor_set(v___x_4972_, 3, v_val_4961_);
lean_ctor_set(v___x_4972_, 4, v_val_4953_);
v___x_4973_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4973_, 0, v___x_4971_);
lean_ctor_set(v___x_4973_, 1, v___x_4972_);
lean_ctor_set_uint8(v___x_4973_, sizeof(void*)*2, v___x_4947_);
v___x_4974_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4973_, v_structId_4946_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_);
return v___x_4974_;
}
else
{
lean_dec(v___x_4964_);
lean_dec(v_val_4961_);
lean_dec(v_val_4953_);
lean_dec(v_structId_4946_);
lean_dec(v_id_4945_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
lean_dec(v_a_4928_);
lean_dec_ref(v_a_4927_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
lean_dec(v_a_4922_);
lean_dec(v_a_4921_);
lean_dec_ref(v_b_4919_);
lean_dec_ref(v_a_4918_);
return v___x_4969_;
}
}
else
{
lean_object* v___x_4975_; lean_object* v___x_4977_; 
lean_dec(v___x_4964_);
lean_dec(v_val_4961_);
lean_dec(v_val_4953_);
lean_dec(v_structId_4946_);
lean_dec(v_id_4945_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
lean_dec(v_a_4928_);
lean_dec_ref(v_a_4927_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
lean_dec(v_a_4922_);
lean_dec(v_a_4921_);
lean_dec_ref(v_b_4919_);
lean_dec_ref(v_a_4918_);
v___x_4975_ = lean_box(0);
if (v_isShared_4960_ == 0)
{
lean_ctor_set(v___x_4959_, 0, v___x_4975_);
v___x_4977_ = v___x_4959_;
goto v_reusejp_4976_;
}
else
{
lean_object* v_reuseFailAlloc_4978_; 
v_reuseFailAlloc_4978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4978_, 0, v___x_4975_);
v___x_4977_ = v_reuseFailAlloc_4978_;
goto v_reusejp_4976_;
}
v_reusejp_4976_:
{
return v___x_4977_;
}
}
}
}
else
{
lean_object* v___x_4980_; lean_object* v___x_4982_; 
lean_dec(v_a_4957_);
lean_dec(v_val_4953_);
lean_dec(v_structId_4946_);
lean_dec(v_id_4945_);
lean_del_object(v___x_4941_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
lean_dec(v_a_4928_);
lean_dec_ref(v_a_4927_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
lean_dec(v_a_4922_);
lean_dec(v_a_4921_);
lean_dec_ref(v_b_4919_);
lean_dec_ref(v_a_4918_);
v___x_4980_ = lean_box(0);
if (v_isShared_4960_ == 0)
{
lean_ctor_set(v___x_4959_, 0, v___x_4980_);
v___x_4982_ = v___x_4959_;
goto v_reusejp_4981_;
}
else
{
lean_object* v_reuseFailAlloc_4983_; 
v_reuseFailAlloc_4983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4983_, 0, v___x_4980_);
v___x_4982_ = v_reuseFailAlloc_4983_;
goto v_reusejp_4981_;
}
v_reusejp_4981_:
{
return v___x_4982_;
}
}
}
}
else
{
lean_object* v_a_4985_; lean_object* v___x_4987_; uint8_t v_isShared_4988_; uint8_t v_isSharedCheck_4992_; 
lean_dec(v_val_4953_);
lean_dec(v_structId_4946_);
lean_dec(v_id_4945_);
lean_del_object(v___x_4941_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
lean_dec(v_a_4928_);
lean_dec_ref(v_a_4927_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
lean_dec(v_a_4922_);
lean_dec(v_a_4921_);
lean_dec_ref(v_b_4919_);
lean_dec_ref(v_a_4918_);
v_a_4985_ = lean_ctor_get(v___x_4956_, 0);
v_isSharedCheck_4992_ = !lean_is_exclusive(v___x_4956_);
if (v_isSharedCheck_4992_ == 0)
{
v___x_4987_ = v___x_4956_;
v_isShared_4988_ = v_isSharedCheck_4992_;
goto v_resetjp_4986_;
}
else
{
lean_inc(v_a_4985_);
lean_dec(v___x_4956_);
v___x_4987_ = lean_box(0);
v_isShared_4988_ = v_isSharedCheck_4992_;
goto v_resetjp_4986_;
}
v_resetjp_4986_:
{
lean_object* v___x_4990_; 
if (v_isShared_4988_ == 0)
{
v___x_4990_ = v___x_4987_;
goto v_reusejp_4989_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v_a_4985_);
v___x_4990_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4989_;
}
v_reusejp_4989_:
{
return v___x_4990_;
}
}
}
}
else
{
lean_object* v_a_4993_; lean_object* v___x_4995_; uint8_t v_isShared_4996_; uint8_t v_isSharedCheck_5000_; 
lean_dec(v_val_4953_);
lean_dec(v_structId_4946_);
lean_dec(v_id_4945_);
lean_del_object(v___x_4941_);
lean_dec(v_fst_4939_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
lean_dec(v_a_4928_);
lean_dec_ref(v_a_4927_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
lean_dec(v_a_4922_);
lean_dec(v_a_4921_);
lean_dec_ref(v_b_4919_);
lean_dec_ref(v_a_4918_);
v_a_4993_ = lean_ctor_get(v___x_4954_, 0);
v_isSharedCheck_5000_ = !lean_is_exclusive(v___x_4954_);
if (v_isSharedCheck_5000_ == 0)
{
v___x_4995_ = v___x_4954_;
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
else
{
lean_inc(v_a_4993_);
lean_dec(v___x_4954_);
v___x_4995_ = lean_box(0);
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
v_resetjp_4994_:
{
lean_object* v___x_4998_; 
if (v_isShared_4996_ == 0)
{
v___x_4998_ = v___x_4995_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_a_4993_);
v___x_4998_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
return v___x_4998_;
}
}
}
}
else
{
lean_object* v___x_5001_; lean_object* v___x_5003_; 
lean_dec(v_a_4949_);
lean_dec(v_structId_4946_);
lean_dec(v_id_4945_);
lean_del_object(v___x_4941_);
lean_dec(v_fst_4939_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
lean_dec(v_a_4928_);
lean_dec_ref(v_a_4927_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
lean_dec(v_a_4922_);
lean_dec(v_a_4921_);
lean_dec_ref(v_b_4919_);
lean_dec_ref(v_a_4918_);
v___x_5001_ = lean_box(0);
if (v_isShared_4952_ == 0)
{
lean_ctor_set(v___x_4951_, 0, v___x_5001_);
v___x_5003_ = v___x_4951_;
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
lean_object* v_a_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5013_; 
lean_dec(v_structId_4946_);
lean_dec(v_id_4945_);
lean_del_object(v___x_4941_);
lean_dec(v_fst_4939_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
lean_dec(v_a_4928_);
lean_dec_ref(v_a_4927_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
lean_dec(v_a_4922_);
lean_dec(v_a_4921_);
lean_dec_ref(v_b_4919_);
lean_dec_ref(v_a_4918_);
v_a_5006_ = lean_ctor_get(v___x_4948_, 0);
v_isSharedCheck_5013_ = !lean_is_exclusive(v___x_4948_);
if (v_isSharedCheck_5013_ == 0)
{
v___x_5008_ = v___x_4948_;
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_a_5006_);
lean_dec(v___x_4948_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v___x_5011_; 
if (v_isShared_5009_ == 0)
{
v___x_5011_ = v___x_5008_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_a_5006_);
v___x_5011_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
return v___x_5011_;
}
}
}
}
else
{
lean_object* v_a_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5021_; 
lean_del_object(v___x_4941_);
lean_dec(v_fst_4939_);
lean_dec(v_fst_4936_);
lean_dec(v_a_4933_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
lean_dec(v_a_4928_);
lean_dec_ref(v_a_4927_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
lean_dec(v_a_4922_);
lean_dec(v_a_4921_);
lean_dec_ref(v_b_4919_);
lean_dec_ref(v_a_4918_);
v_a_5014_ = lean_ctor_get(v___x_4943_, 0);
v_isSharedCheck_5021_ = !lean_is_exclusive(v___x_4943_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_5016_ = v___x_4943_;
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_a_5014_);
lean_dec(v___x_4943_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
lean_object* v___x_5019_; 
if (v_isShared_5017_ == 0)
{
v___x_5019_ = v___x_5016_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_a_5014_);
v___x_5019_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
return v___x_5019_;
}
}
}
}
}
else
{
lean_object* v_a_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5031_; 
lean_dec(v_fst_4936_);
lean_dec(v_a_4933_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
lean_dec(v_a_4928_);
lean_dec_ref(v_a_4927_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
lean_dec(v_a_4922_);
lean_dec(v_a_4921_);
lean_dec_ref(v_b_4919_);
lean_dec_ref(v_a_4918_);
v_a_5024_ = lean_ctor_get(v___x_4937_, 0);
v_isSharedCheck_5031_ = !lean_is_exclusive(v___x_4937_);
if (v_isSharedCheck_5031_ == 0)
{
v___x_5026_ = v___x_4937_;
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_a_5024_);
lean_dec(v___x_4937_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v___x_5029_; 
if (v_isShared_5027_ == 0)
{
v___x_5029_ = v___x_5026_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v_a_5024_);
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
lean_dec(v_a_4933_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
lean_dec(v_a_4928_);
lean_dec_ref(v_a_4927_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
lean_dec(v_a_4922_);
lean_dec(v_a_4921_);
lean_dec(v_a_4920_);
lean_dec_ref(v_b_4919_);
lean_dec_ref(v_a_4918_);
v_a_5032_ = lean_ctor_get(v___x_4934_, 0);
v_isSharedCheck_5039_ = !lean_is_exclusive(v___x_4934_);
if (v_isSharedCheck_5039_ == 0)
{
v___x_5034_ = v___x_4934_;
v_isShared_5035_ = v_isSharedCheck_5039_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_a_5032_);
lean_dec(v___x_4934_);
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
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
lean_dec(v_a_4928_);
lean_dec_ref(v_a_4927_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
lean_dec(v_a_4922_);
lean_dec(v_a_4921_);
lean_dec(v_a_4920_);
lean_dec_ref(v_b_4919_);
lean_dec_ref(v_a_4918_);
v_a_5040_ = lean_ctor_get(v___x_4932_, 0);
v_isSharedCheck_5047_ = !lean_is_exclusive(v___x_4932_);
if (v_isSharedCheck_5047_ == 0)
{
v___x_5042_ = v___x_4932_;
v_isShared_5043_ = v_isSharedCheck_5047_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_a_5040_);
lean_dec(v___x_4932_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27___boxed(lean_object* v_a_5048_, lean_object* v_b_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_){
_start:
{
lean_object* v_res_5062_; 
v_res_5062_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5048_, v_b_5049_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_);
return v_res_5062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(lean_object* v_a_5063_, lean_object* v_b_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_){
_start:
{
lean_object* v___x_5077_; 
v___x_5077_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_);
if (lean_obj_tag(v___x_5077_) == 0)
{
lean_object* v_a_5078_; lean_object* v___x_5079_; 
v_a_5078_ = lean_ctor_get(v___x_5077_, 0);
lean_inc(v_a_5078_);
lean_dec_ref(v___x_5077_);
lean_inc(v_a_5075_);
lean_inc_ref(v_a_5074_);
lean_inc(v_a_5073_);
lean_inc_ref(v_a_5072_);
lean_inc(v_a_5071_);
lean_inc_ref(v_a_5070_);
lean_inc(v_a_5069_);
lean_inc_ref(v_a_5068_);
lean_inc(v_a_5067_);
lean_inc(v_a_5066_);
lean_inc(v_a_5065_);
lean_inc_ref(v_a_5063_);
v___x_5079_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5063_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_object* v_a_5080_; lean_object* v_fst_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5177_; 
v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
lean_inc(v_a_5080_);
lean_dec_ref(v___x_5079_);
v_fst_5081_ = lean_ctor_get(v_a_5080_, 0);
v_isSharedCheck_5177_ = !lean_is_exclusive(v_a_5080_);
if (v_isSharedCheck_5177_ == 0)
{
lean_object* v_unused_5178_; 
v_unused_5178_ = lean_ctor_get(v_a_5080_, 1);
lean_dec(v_unused_5178_);
v___x_5083_ = v_a_5080_;
v_isShared_5084_ = v_isSharedCheck_5177_;
goto v_resetjp_5082_;
}
else
{
lean_inc(v_fst_5081_);
lean_dec(v_a_5080_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5177_;
goto v_resetjp_5082_;
}
v_resetjp_5082_:
{
lean_object* v___x_5085_; 
lean_inc(v_a_5075_);
lean_inc_ref(v_a_5074_);
lean_inc(v_a_5073_);
lean_inc_ref(v_a_5072_);
lean_inc(v_a_5071_);
lean_inc_ref(v_a_5070_);
lean_inc(v_a_5069_);
lean_inc_ref(v_a_5068_);
lean_inc(v_a_5067_);
lean_inc(v_a_5066_);
lean_inc_ref(v_b_5064_);
v___x_5085_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5064_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_);
if (lean_obj_tag(v___x_5085_) == 0)
{
lean_object* v_a_5086_; lean_object* v_fst_5087_; lean_object* v___x_5089_; uint8_t v_isShared_5090_; uint8_t v_isSharedCheck_5167_; 
v_a_5086_ = lean_ctor_get(v___x_5085_, 0);
lean_inc(v_a_5086_);
lean_dec_ref(v___x_5085_);
v_fst_5087_ = lean_ctor_get(v_a_5086_, 0);
v_isSharedCheck_5167_ = !lean_is_exclusive(v_a_5086_);
if (v_isSharedCheck_5167_ == 0)
{
lean_object* v_unused_5168_; 
v_unused_5168_ = lean_ctor_get(v_a_5086_, 1);
lean_dec(v_unused_5168_);
v___x_5089_ = v_a_5086_;
v_isShared_5090_ = v_isSharedCheck_5167_;
goto v_resetjp_5088_;
}
else
{
lean_inc(v_fst_5087_);
lean_dec(v_a_5086_);
v___x_5089_ = lean_box(0);
v_isShared_5090_ = v_isSharedCheck_5167_;
goto v_resetjp_5088_;
}
v_resetjp_5088_:
{
lean_object* v___x_5091_; 
v___x_5091_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5063_, v_a_5066_);
if (lean_obj_tag(v___x_5091_) == 0)
{
lean_object* v_a_5092_; lean_object* v_id_5093_; lean_object* v_structId_5094_; uint8_t v___x_5095_; lean_object* v___x_5096_; 
v_a_5092_ = lean_ctor_get(v___x_5091_, 0);
lean_inc(v_a_5092_);
lean_dec_ref(v___x_5091_);
v_id_5093_ = lean_ctor_get(v_a_5078_, 0);
lean_inc(v_id_5093_);
v_structId_5094_ = lean_ctor_get(v_a_5078_, 1);
lean_inc(v_structId_5094_);
lean_dec(v_a_5078_);
v___x_5095_ = 0;
lean_inc(v_a_5075_);
lean_inc_ref(v_a_5074_);
lean_inc(v_a_5073_);
lean_inc_ref(v_a_5072_);
lean_inc(v_a_5071_);
lean_inc_ref(v_a_5070_);
lean_inc(v_a_5069_);
lean_inc_ref(v_a_5068_);
lean_inc(v_a_5067_);
lean_inc(v_a_5066_);
lean_inc(v_structId_5094_);
v___x_5096_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5081_, v___x_5095_, v_a_5092_, v_structId_5094_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_);
if (lean_obj_tag(v___x_5096_) == 0)
{
lean_object* v_a_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5150_; 
v_a_5097_ = lean_ctor_get(v___x_5096_, 0);
v_isSharedCheck_5150_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_5099_ = v___x_5096_;
v_isShared_5100_ = v_isSharedCheck_5150_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_a_5097_);
lean_dec(v___x_5096_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5150_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
if (lean_obj_tag(v_a_5097_) == 1)
{
lean_object* v_val_5101_; lean_object* v___x_5102_; 
lean_del_object(v___x_5099_);
v_val_5101_ = lean_ctor_get(v_a_5097_, 0);
lean_inc(v_val_5101_);
lean_dec_ref(v_a_5097_);
v___x_5102_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5064_, v_a_5066_);
if (lean_obj_tag(v___x_5102_) == 0)
{
lean_object* v_a_5103_; lean_object* v___x_5104_; 
v_a_5103_ = lean_ctor_get(v___x_5102_, 0);
lean_inc(v_a_5103_);
lean_dec_ref(v___x_5102_);
lean_inc(v_a_5075_);
lean_inc_ref(v_a_5074_);
lean_inc(v_a_5073_);
lean_inc_ref(v_a_5072_);
lean_inc(v_a_5071_);
lean_inc_ref(v_a_5070_);
lean_inc(v_a_5069_);
lean_inc_ref(v_a_5068_);
lean_inc(v_a_5067_);
lean_inc(v_a_5066_);
lean_inc(v_structId_5094_);
v___x_5104_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5087_, v___x_5095_, v_a_5103_, v_structId_5094_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_);
if (lean_obj_tag(v___x_5104_) == 0)
{
lean_object* v_a_5105_; lean_object* v___x_5107_; uint8_t v_isShared_5108_; uint8_t v_isSharedCheck_5129_; 
v_a_5105_ = lean_ctor_get(v___x_5104_, 0);
v_isSharedCheck_5129_ = !lean_is_exclusive(v___x_5104_);
if (v_isSharedCheck_5129_ == 0)
{
v___x_5107_ = v___x_5104_;
v_isShared_5108_ = v_isSharedCheck_5129_;
goto v_resetjp_5106_;
}
else
{
lean_inc(v_a_5105_);
lean_dec(v___x_5104_);
v___x_5107_ = lean_box(0);
v_isShared_5108_ = v_isSharedCheck_5129_;
goto v_resetjp_5106_;
}
v_resetjp_5106_:
{
if (lean_obj_tag(v_a_5105_) == 1)
{
lean_object* v_val_5109_; lean_object* v___x_5111_; 
v_val_5109_ = lean_ctor_get(v_a_5105_, 0);
lean_inc(v_val_5109_);
lean_dec_ref(v_a_5105_);
lean_inc(v_val_5109_);
lean_inc(v_val_5101_);
if (v_isShared_5090_ == 0)
{
lean_ctor_set_tag(v___x_5089_, 3);
lean_ctor_set(v___x_5089_, 1, v_val_5109_);
lean_ctor_set(v___x_5089_, 0, v_val_5101_);
v___x_5111_ = v___x_5089_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5124_; 
v_reuseFailAlloc_5124_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_val_5101_);
lean_ctor_set(v_reuseFailAlloc_5124_, 1, v_val_5109_);
v___x_5111_ = v_reuseFailAlloc_5124_;
goto v_reusejp_5110_;
}
v_reusejp_5110_:
{
lean_object* v___x_5112_; lean_object* v___x_5113_; uint8_t v___x_5114_; 
v___x_5112_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5111_);
v___x_5113_ = lean_box(0);
v___x_5114_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_5112_, v___x_5113_);
if (v___x_5114_ == 0)
{
lean_object* v___x_5115_; lean_object* v___x_5117_; 
lean_del_object(v___x_5107_);
v___x_5115_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5115_, 0, v_a_5063_);
lean_ctor_set(v___x_5115_, 1, v_b_5064_);
lean_ctor_set(v___x_5115_, 2, v_id_5093_);
lean_ctor_set(v___x_5115_, 3, v_val_5101_);
lean_ctor_set(v___x_5115_, 4, v_val_5109_);
if (v_isShared_5084_ == 0)
{
lean_ctor_set(v___x_5083_, 1, v___x_5115_);
lean_ctor_set(v___x_5083_, 0, v___x_5112_);
v___x_5117_ = v___x_5083_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v___x_5112_);
lean_ctor_set(v_reuseFailAlloc_5119_, 1, v___x_5115_);
v___x_5117_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
lean_object* v___x_5118_; 
v___x_5118_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_5117_, v_structId_5094_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_);
return v___x_5118_;
}
}
else
{
lean_object* v___x_5120_; lean_object* v___x_5122_; 
lean_dec(v___x_5112_);
lean_dec(v_val_5109_);
lean_dec(v_val_5101_);
lean_dec(v_structId_5094_);
lean_dec(v_id_5093_);
lean_del_object(v___x_5083_);
lean_dec(v_a_5075_);
lean_dec_ref(v_a_5074_);
lean_dec(v_a_5073_);
lean_dec_ref(v_a_5072_);
lean_dec(v_a_5071_);
lean_dec_ref(v_a_5070_);
lean_dec(v_a_5069_);
lean_dec_ref(v_a_5068_);
lean_dec(v_a_5067_);
lean_dec(v_a_5066_);
lean_dec_ref(v_b_5064_);
lean_dec_ref(v_a_5063_);
v___x_5120_ = lean_box(0);
if (v_isShared_5108_ == 0)
{
lean_ctor_set(v___x_5107_, 0, v___x_5120_);
v___x_5122_ = v___x_5107_;
goto v_reusejp_5121_;
}
else
{
lean_object* v_reuseFailAlloc_5123_; 
v_reuseFailAlloc_5123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5123_, 0, v___x_5120_);
v___x_5122_ = v_reuseFailAlloc_5123_;
goto v_reusejp_5121_;
}
v_reusejp_5121_:
{
return v___x_5122_;
}
}
}
}
else
{
lean_object* v___x_5125_; lean_object* v___x_5127_; 
lean_dec(v_a_5105_);
lean_dec(v_val_5101_);
lean_dec(v_structId_5094_);
lean_dec(v_id_5093_);
lean_del_object(v___x_5089_);
lean_del_object(v___x_5083_);
lean_dec(v_a_5075_);
lean_dec_ref(v_a_5074_);
lean_dec(v_a_5073_);
lean_dec_ref(v_a_5072_);
lean_dec(v_a_5071_);
lean_dec_ref(v_a_5070_);
lean_dec(v_a_5069_);
lean_dec_ref(v_a_5068_);
lean_dec(v_a_5067_);
lean_dec(v_a_5066_);
lean_dec_ref(v_b_5064_);
lean_dec_ref(v_a_5063_);
v___x_5125_ = lean_box(0);
if (v_isShared_5108_ == 0)
{
lean_ctor_set(v___x_5107_, 0, v___x_5125_);
v___x_5127_ = v___x_5107_;
goto v_reusejp_5126_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v___x_5125_);
v___x_5127_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5126_;
}
v_reusejp_5126_:
{
return v___x_5127_;
}
}
}
}
else
{
lean_object* v_a_5130_; lean_object* v___x_5132_; uint8_t v_isShared_5133_; uint8_t v_isSharedCheck_5137_; 
lean_dec(v_val_5101_);
lean_dec(v_structId_5094_);
lean_dec(v_id_5093_);
lean_del_object(v___x_5089_);
lean_del_object(v___x_5083_);
lean_dec(v_a_5075_);
lean_dec_ref(v_a_5074_);
lean_dec(v_a_5073_);
lean_dec_ref(v_a_5072_);
lean_dec(v_a_5071_);
lean_dec_ref(v_a_5070_);
lean_dec(v_a_5069_);
lean_dec_ref(v_a_5068_);
lean_dec(v_a_5067_);
lean_dec(v_a_5066_);
lean_dec_ref(v_b_5064_);
lean_dec_ref(v_a_5063_);
v_a_5130_ = lean_ctor_get(v___x_5104_, 0);
v_isSharedCheck_5137_ = !lean_is_exclusive(v___x_5104_);
if (v_isSharedCheck_5137_ == 0)
{
v___x_5132_ = v___x_5104_;
v_isShared_5133_ = v_isSharedCheck_5137_;
goto v_resetjp_5131_;
}
else
{
lean_inc(v_a_5130_);
lean_dec(v___x_5104_);
v___x_5132_ = lean_box(0);
v_isShared_5133_ = v_isSharedCheck_5137_;
goto v_resetjp_5131_;
}
v_resetjp_5131_:
{
lean_object* v___x_5135_; 
if (v_isShared_5133_ == 0)
{
v___x_5135_ = v___x_5132_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v_a_5130_);
v___x_5135_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
return v___x_5135_;
}
}
}
}
else
{
lean_object* v_a_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5145_; 
lean_dec(v_val_5101_);
lean_dec(v_structId_5094_);
lean_dec(v_id_5093_);
lean_del_object(v___x_5089_);
lean_dec(v_fst_5087_);
lean_del_object(v___x_5083_);
lean_dec(v_a_5075_);
lean_dec_ref(v_a_5074_);
lean_dec(v_a_5073_);
lean_dec_ref(v_a_5072_);
lean_dec(v_a_5071_);
lean_dec_ref(v_a_5070_);
lean_dec(v_a_5069_);
lean_dec_ref(v_a_5068_);
lean_dec(v_a_5067_);
lean_dec(v_a_5066_);
lean_dec_ref(v_b_5064_);
lean_dec_ref(v_a_5063_);
v_a_5138_ = lean_ctor_get(v___x_5102_, 0);
v_isSharedCheck_5145_ = !lean_is_exclusive(v___x_5102_);
if (v_isSharedCheck_5145_ == 0)
{
v___x_5140_ = v___x_5102_;
v_isShared_5141_ = v_isSharedCheck_5145_;
goto v_resetjp_5139_;
}
else
{
lean_inc(v_a_5138_);
lean_dec(v___x_5102_);
v___x_5140_ = lean_box(0);
v_isShared_5141_ = v_isSharedCheck_5145_;
goto v_resetjp_5139_;
}
v_resetjp_5139_:
{
lean_object* v___x_5143_; 
if (v_isShared_5141_ == 0)
{
v___x_5143_ = v___x_5140_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v_a_5138_);
v___x_5143_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
return v___x_5143_;
}
}
}
}
else
{
lean_object* v___x_5146_; lean_object* v___x_5148_; 
lean_dec(v_a_5097_);
lean_dec(v_structId_5094_);
lean_dec(v_id_5093_);
lean_del_object(v___x_5089_);
lean_dec(v_fst_5087_);
lean_del_object(v___x_5083_);
lean_dec(v_a_5075_);
lean_dec_ref(v_a_5074_);
lean_dec(v_a_5073_);
lean_dec_ref(v_a_5072_);
lean_dec(v_a_5071_);
lean_dec_ref(v_a_5070_);
lean_dec(v_a_5069_);
lean_dec_ref(v_a_5068_);
lean_dec(v_a_5067_);
lean_dec(v_a_5066_);
lean_dec_ref(v_b_5064_);
lean_dec_ref(v_a_5063_);
v___x_5146_ = lean_box(0);
if (v_isShared_5100_ == 0)
{
lean_ctor_set(v___x_5099_, 0, v___x_5146_);
v___x_5148_ = v___x_5099_;
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
lean_object* v_a_5151_; lean_object* v___x_5153_; uint8_t v_isShared_5154_; uint8_t v_isSharedCheck_5158_; 
lean_dec(v_structId_5094_);
lean_dec(v_id_5093_);
lean_del_object(v___x_5089_);
lean_dec(v_fst_5087_);
lean_del_object(v___x_5083_);
lean_dec(v_a_5075_);
lean_dec_ref(v_a_5074_);
lean_dec(v_a_5073_);
lean_dec_ref(v_a_5072_);
lean_dec(v_a_5071_);
lean_dec_ref(v_a_5070_);
lean_dec(v_a_5069_);
lean_dec_ref(v_a_5068_);
lean_dec(v_a_5067_);
lean_dec(v_a_5066_);
lean_dec_ref(v_b_5064_);
lean_dec_ref(v_a_5063_);
v_a_5151_ = lean_ctor_get(v___x_5096_, 0);
v_isSharedCheck_5158_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5158_ == 0)
{
v___x_5153_ = v___x_5096_;
v_isShared_5154_ = v_isSharedCheck_5158_;
goto v_resetjp_5152_;
}
else
{
lean_inc(v_a_5151_);
lean_dec(v___x_5096_);
v___x_5153_ = lean_box(0);
v_isShared_5154_ = v_isSharedCheck_5158_;
goto v_resetjp_5152_;
}
v_resetjp_5152_:
{
lean_object* v___x_5156_; 
if (v_isShared_5154_ == 0)
{
v___x_5156_ = v___x_5153_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v_a_5151_);
v___x_5156_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
return v___x_5156_;
}
}
}
}
else
{
lean_object* v_a_5159_; lean_object* v___x_5161_; uint8_t v_isShared_5162_; uint8_t v_isSharedCheck_5166_; 
lean_del_object(v___x_5089_);
lean_dec(v_fst_5087_);
lean_del_object(v___x_5083_);
lean_dec(v_fst_5081_);
lean_dec(v_a_5078_);
lean_dec(v_a_5075_);
lean_dec_ref(v_a_5074_);
lean_dec(v_a_5073_);
lean_dec_ref(v_a_5072_);
lean_dec(v_a_5071_);
lean_dec_ref(v_a_5070_);
lean_dec(v_a_5069_);
lean_dec_ref(v_a_5068_);
lean_dec(v_a_5067_);
lean_dec(v_a_5066_);
lean_dec_ref(v_b_5064_);
lean_dec_ref(v_a_5063_);
v_a_5159_ = lean_ctor_get(v___x_5091_, 0);
v_isSharedCheck_5166_ = !lean_is_exclusive(v___x_5091_);
if (v_isSharedCheck_5166_ == 0)
{
v___x_5161_ = v___x_5091_;
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
else
{
lean_inc(v_a_5159_);
lean_dec(v___x_5091_);
v___x_5161_ = lean_box(0);
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
v_resetjp_5160_:
{
lean_object* v___x_5164_; 
if (v_isShared_5162_ == 0)
{
v___x_5164_ = v___x_5161_;
goto v_reusejp_5163_;
}
else
{
lean_object* v_reuseFailAlloc_5165_; 
v_reuseFailAlloc_5165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5165_, 0, v_a_5159_);
v___x_5164_ = v_reuseFailAlloc_5165_;
goto v_reusejp_5163_;
}
v_reusejp_5163_:
{
return v___x_5164_;
}
}
}
}
}
else
{
lean_object* v_a_5169_; lean_object* v___x_5171_; uint8_t v_isShared_5172_; uint8_t v_isSharedCheck_5176_; 
lean_del_object(v___x_5083_);
lean_dec(v_fst_5081_);
lean_dec(v_a_5078_);
lean_dec(v_a_5075_);
lean_dec_ref(v_a_5074_);
lean_dec(v_a_5073_);
lean_dec_ref(v_a_5072_);
lean_dec(v_a_5071_);
lean_dec_ref(v_a_5070_);
lean_dec(v_a_5069_);
lean_dec_ref(v_a_5068_);
lean_dec(v_a_5067_);
lean_dec(v_a_5066_);
lean_dec_ref(v_b_5064_);
lean_dec_ref(v_a_5063_);
v_a_5169_ = lean_ctor_get(v___x_5085_, 0);
v_isSharedCheck_5176_ = !lean_is_exclusive(v___x_5085_);
if (v_isSharedCheck_5176_ == 0)
{
v___x_5171_ = v___x_5085_;
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
else
{
lean_inc(v_a_5169_);
lean_dec(v___x_5085_);
v___x_5171_ = lean_box(0);
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
v_resetjp_5170_:
{
lean_object* v___x_5174_; 
if (v_isShared_5172_ == 0)
{
v___x_5174_ = v___x_5171_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_a_5169_);
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
}
else
{
lean_object* v_a_5179_; lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5186_; 
lean_dec(v_a_5078_);
lean_dec(v_a_5075_);
lean_dec_ref(v_a_5074_);
lean_dec(v_a_5073_);
lean_dec_ref(v_a_5072_);
lean_dec(v_a_5071_);
lean_dec_ref(v_a_5070_);
lean_dec(v_a_5069_);
lean_dec_ref(v_a_5068_);
lean_dec(v_a_5067_);
lean_dec(v_a_5066_);
lean_dec(v_a_5065_);
lean_dec_ref(v_b_5064_);
lean_dec_ref(v_a_5063_);
v_a_5179_ = lean_ctor_get(v___x_5079_, 0);
v_isSharedCheck_5186_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5186_ == 0)
{
v___x_5181_ = v___x_5079_;
v_isShared_5182_ = v_isSharedCheck_5186_;
goto v_resetjp_5180_;
}
else
{
lean_inc(v_a_5179_);
lean_dec(v___x_5079_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5186_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
lean_object* v___x_5184_; 
if (v_isShared_5182_ == 0)
{
v___x_5184_ = v___x_5181_;
goto v_reusejp_5183_;
}
else
{
lean_object* v_reuseFailAlloc_5185_; 
v_reuseFailAlloc_5185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5185_, 0, v_a_5179_);
v___x_5184_ = v_reuseFailAlloc_5185_;
goto v_reusejp_5183_;
}
v_reusejp_5183_:
{
return v___x_5184_;
}
}
}
}
else
{
lean_object* v_a_5187_; lean_object* v___x_5189_; uint8_t v_isShared_5190_; uint8_t v_isSharedCheck_5194_; 
lean_dec(v_a_5075_);
lean_dec_ref(v_a_5074_);
lean_dec(v_a_5073_);
lean_dec_ref(v_a_5072_);
lean_dec(v_a_5071_);
lean_dec_ref(v_a_5070_);
lean_dec(v_a_5069_);
lean_dec_ref(v_a_5068_);
lean_dec(v_a_5067_);
lean_dec(v_a_5066_);
lean_dec(v_a_5065_);
lean_dec_ref(v_b_5064_);
lean_dec_ref(v_a_5063_);
v_a_5187_ = lean_ctor_get(v___x_5077_, 0);
v_isSharedCheck_5194_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5194_ == 0)
{
v___x_5189_ = v___x_5077_;
v_isShared_5190_ = v_isSharedCheck_5194_;
goto v_resetjp_5188_;
}
else
{
lean_inc(v_a_5187_);
lean_dec(v___x_5077_);
v___x_5189_ = lean_box(0);
v_isShared_5190_ = v_isSharedCheck_5194_;
goto v_resetjp_5188_;
}
v_resetjp_5188_:
{
lean_object* v___x_5192_; 
if (v_isShared_5190_ == 0)
{
v___x_5192_ = v___x_5189_;
goto v_reusejp_5191_;
}
else
{
lean_object* v_reuseFailAlloc_5193_; 
v_reuseFailAlloc_5193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_a_5187_);
v___x_5192_ = v_reuseFailAlloc_5193_;
goto v_reusejp_5191_;
}
v_reusejp_5191_:
{
return v___x_5192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq___boxed(lean_object* v_a_5195_, lean_object* v_b_5196_, lean_object* v_a_5197_, lean_object* v_a_5198_, lean_object* v_a_5199_, lean_object* v_a_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_, lean_object* v_a_5208_){
_start:
{
lean_object* v_res_5209_; 
v_res_5209_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5195_, v_b_5196_, v_a_5197_, v_a_5198_, v_a_5199_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_, v_a_5206_, v_a_5207_);
return v_res_5209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq(lean_object* v_a_5210_, lean_object* v_b_5211_, lean_object* v_a_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_){
_start:
{
uint8_t v___x_5223_; 
v___x_5223_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_5210_, v_b_5211_);
if (v___x_5223_ == 0)
{
lean_object* v___x_5224_; 
v___x_5224_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5210_, v_b_5211_, v_a_5212_, v_a_5220_);
if (lean_obj_tag(v___x_5224_) == 0)
{
lean_object* v_a_5225_; 
v_a_5225_ = lean_ctor_get(v___x_5224_, 0);
lean_inc(v_a_5225_);
lean_dec_ref(v___x_5224_);
if (lean_obj_tag(v_a_5225_) == 1)
{
lean_object* v_val_5226_; lean_object* v___x_5227_; 
v_val_5226_ = lean_ctor_get(v_a_5225_, 0);
lean_inc(v_val_5226_);
lean_dec_ref(v_a_5225_);
v___x_5227_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_val_5226_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_);
if (lean_obj_tag(v___x_5227_) == 0)
{
lean_object* v_a_5228_; uint8_t v___x_5229_; 
v_a_5228_ = lean_ctor_get(v___x_5227_, 0);
lean_inc(v_a_5228_);
lean_dec_ref(v___x_5227_);
v___x_5229_ = lean_unbox(v_a_5228_);
lean_dec(v_a_5228_);
if (v___x_5229_ == 0)
{
lean_object* v___x_5230_; 
v___x_5230_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5226_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_);
if (lean_obj_tag(v___x_5230_) == 0)
{
lean_object* v_a_5231_; uint8_t v___x_5232_; 
v_a_5231_ = lean_ctor_get(v___x_5230_, 0);
lean_inc(v_a_5231_);
lean_dec_ref(v___x_5230_);
v___x_5232_ = lean_unbox(v_a_5231_);
lean_dec(v_a_5231_);
if (v___x_5232_ == 0)
{
lean_object* v___x_5233_; 
v___x_5233_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_5210_, v_b_5211_, v_val_5226_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_);
return v___x_5233_;
}
else
{
lean_object* v___x_5234_; 
lean_dec(v_val_5226_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec(v_a_5213_);
lean_dec(v_a_5212_);
v___x_5234_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_5210_, v_b_5211_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_);
lean_dec(v_a_5221_);
lean_dec_ref(v_a_5220_);
lean_dec(v_a_5219_);
lean_dec_ref(v_a_5218_);
return v___x_5234_;
}
}
else
{
lean_object* v_a_5235_; lean_object* v___x_5237_; uint8_t v_isShared_5238_; uint8_t v_isSharedCheck_5242_; 
lean_dec(v_val_5226_);
lean_dec(v_a_5221_);
lean_dec_ref(v_a_5220_);
lean_dec(v_a_5219_);
lean_dec_ref(v_a_5218_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec(v_a_5213_);
lean_dec(v_a_5212_);
lean_dec_ref(v_b_5211_);
lean_dec_ref(v_a_5210_);
v_a_5235_ = lean_ctor_get(v___x_5230_, 0);
v_isSharedCheck_5242_ = !lean_is_exclusive(v___x_5230_);
if (v_isSharedCheck_5242_ == 0)
{
v___x_5237_ = v___x_5230_;
v_isShared_5238_ = v_isSharedCheck_5242_;
goto v_resetjp_5236_;
}
else
{
lean_inc(v_a_5235_);
lean_dec(v___x_5230_);
v___x_5237_ = lean_box(0);
v_isShared_5238_ = v_isSharedCheck_5242_;
goto v_resetjp_5236_;
}
v_resetjp_5236_:
{
lean_object* v___x_5240_; 
if (v_isShared_5238_ == 0)
{
v___x_5240_ = v___x_5237_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5241_; 
v_reuseFailAlloc_5241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5241_, 0, v_a_5235_);
v___x_5240_ = v_reuseFailAlloc_5241_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
return v___x_5240_;
}
}
}
}
else
{
lean_object* v___x_5243_; 
v___x_5243_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5226_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_);
if (lean_obj_tag(v___x_5243_) == 0)
{
lean_object* v_a_5244_; uint8_t v___x_5245_; 
v_a_5244_ = lean_ctor_get(v___x_5243_, 0);
lean_inc(v_a_5244_);
lean_dec_ref(v___x_5243_);
v___x_5245_ = lean_unbox(v_a_5244_);
lean_dec(v_a_5244_);
if (v___x_5245_ == 0)
{
lean_object* v___x_5246_; 
v___x_5246_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_5210_, v_b_5211_, v_val_5226_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_);
return v___x_5246_;
}
else
{
lean_object* v___x_5247_; 
v___x_5247_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_5210_, v_b_5211_, v_val_5226_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_);
return v___x_5247_;
}
}
else
{
lean_object* v_a_5248_; lean_object* v___x_5250_; uint8_t v_isShared_5251_; uint8_t v_isSharedCheck_5255_; 
lean_dec(v_val_5226_);
lean_dec(v_a_5221_);
lean_dec_ref(v_a_5220_);
lean_dec(v_a_5219_);
lean_dec_ref(v_a_5218_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec(v_a_5213_);
lean_dec(v_a_5212_);
lean_dec_ref(v_b_5211_);
lean_dec_ref(v_a_5210_);
v_a_5248_ = lean_ctor_get(v___x_5243_, 0);
v_isSharedCheck_5255_ = !lean_is_exclusive(v___x_5243_);
if (v_isSharedCheck_5255_ == 0)
{
v___x_5250_ = v___x_5243_;
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
else
{
lean_inc(v_a_5248_);
lean_dec(v___x_5243_);
v___x_5250_ = lean_box(0);
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
v_resetjp_5249_:
{
lean_object* v___x_5253_; 
if (v_isShared_5251_ == 0)
{
v___x_5253_ = v___x_5250_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_a_5248_);
v___x_5253_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
return v___x_5253_;
}
}
}
}
}
else
{
lean_object* v_a_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5263_; 
lean_dec(v_val_5226_);
lean_dec(v_a_5221_);
lean_dec_ref(v_a_5220_);
lean_dec(v_a_5219_);
lean_dec_ref(v_a_5218_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec(v_a_5213_);
lean_dec(v_a_5212_);
lean_dec_ref(v_b_5211_);
lean_dec_ref(v_a_5210_);
v_a_5256_ = lean_ctor_get(v___x_5227_, 0);
v_isSharedCheck_5263_ = !lean_is_exclusive(v___x_5227_);
if (v_isSharedCheck_5263_ == 0)
{
v___x_5258_ = v___x_5227_;
v_isShared_5259_ = v_isSharedCheck_5263_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_a_5256_);
lean_dec(v___x_5227_);
v___x_5258_ = lean_box(0);
v_isShared_5259_ = v_isSharedCheck_5263_;
goto v_resetjp_5257_;
}
v_resetjp_5257_:
{
lean_object* v___x_5261_; 
if (v_isShared_5259_ == 0)
{
v___x_5261_ = v___x_5258_;
goto v_reusejp_5260_;
}
else
{
lean_object* v_reuseFailAlloc_5262_; 
v_reuseFailAlloc_5262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_a_5256_);
v___x_5261_ = v_reuseFailAlloc_5262_;
goto v_reusejp_5260_;
}
v_reusejp_5260_:
{
return v___x_5261_;
}
}
}
}
else
{
lean_object* v___x_5264_; 
lean_dec(v_a_5225_);
v___x_5264_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5210_, v_b_5211_, v_a_5212_, v_a_5220_);
if (lean_obj_tag(v___x_5264_) == 0)
{
lean_object* v_a_5265_; lean_object* v___x_5267_; uint8_t v_isShared_5268_; uint8_t v_isSharedCheck_5287_; 
v_a_5265_ = lean_ctor_get(v___x_5264_, 0);
v_isSharedCheck_5287_ = !lean_is_exclusive(v___x_5264_);
if (v_isSharedCheck_5287_ == 0)
{
v___x_5267_ = v___x_5264_;
v_isShared_5268_ = v_isSharedCheck_5287_;
goto v_resetjp_5266_;
}
else
{
lean_inc(v_a_5265_);
lean_dec(v___x_5264_);
v___x_5267_ = lean_box(0);
v_isShared_5268_ = v_isSharedCheck_5287_;
goto v_resetjp_5266_;
}
v_resetjp_5266_:
{
if (lean_obj_tag(v_a_5265_) == 1)
{
lean_object* v_val_5269_; lean_object* v___x_5270_; 
lean_del_object(v___x_5267_);
v_val_5269_ = lean_ctor_get(v_a_5265_, 0);
lean_inc(v_val_5269_);
lean_dec_ref(v_a_5265_);
v___x_5270_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_5269_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_);
if (lean_obj_tag(v___x_5270_) == 0)
{
lean_object* v_a_5271_; lean_object* v_orderedAddInst_x3f_5272_; 
v_a_5271_ = lean_ctor_get(v___x_5270_, 0);
lean_inc(v_a_5271_);
lean_dec_ref(v___x_5270_);
v_orderedAddInst_x3f_5272_ = lean_ctor_get(v_a_5271_, 9);
lean_inc(v_orderedAddInst_x3f_5272_);
lean_dec(v_a_5271_);
if (lean_obj_tag(v_orderedAddInst_x3f_5272_) == 0)
{
lean_object* v___x_5273_; 
v___x_5273_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5210_, v_b_5211_, v_val_5269_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_);
return v___x_5273_;
}
else
{
lean_object* v___x_5274_; 
lean_dec_ref(v_orderedAddInst_x3f_5272_);
v___x_5274_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5210_, v_b_5211_, v_val_5269_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_);
return v___x_5274_;
}
}
else
{
lean_object* v_a_5275_; lean_object* v___x_5277_; uint8_t v_isShared_5278_; uint8_t v_isSharedCheck_5282_; 
lean_dec(v_val_5269_);
lean_dec(v_a_5221_);
lean_dec_ref(v_a_5220_);
lean_dec(v_a_5219_);
lean_dec_ref(v_a_5218_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec(v_a_5213_);
lean_dec(v_a_5212_);
lean_dec_ref(v_b_5211_);
lean_dec_ref(v_a_5210_);
v_a_5275_ = lean_ctor_get(v___x_5270_, 0);
v_isSharedCheck_5282_ = !lean_is_exclusive(v___x_5270_);
if (v_isSharedCheck_5282_ == 0)
{
v___x_5277_ = v___x_5270_;
v_isShared_5278_ = v_isSharedCheck_5282_;
goto v_resetjp_5276_;
}
else
{
lean_inc(v_a_5275_);
lean_dec(v___x_5270_);
v___x_5277_ = lean_box(0);
v_isShared_5278_ = v_isSharedCheck_5282_;
goto v_resetjp_5276_;
}
v_resetjp_5276_:
{
lean_object* v___x_5280_; 
if (v_isShared_5278_ == 0)
{
v___x_5280_ = v___x_5277_;
goto v_reusejp_5279_;
}
else
{
lean_object* v_reuseFailAlloc_5281_; 
v_reuseFailAlloc_5281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5281_, 0, v_a_5275_);
v___x_5280_ = v_reuseFailAlloc_5281_;
goto v_reusejp_5279_;
}
v_reusejp_5279_:
{
return v___x_5280_;
}
}
}
}
else
{
lean_object* v___x_5283_; lean_object* v___x_5285_; 
lean_dec(v_a_5265_);
lean_dec(v_a_5221_);
lean_dec_ref(v_a_5220_);
lean_dec(v_a_5219_);
lean_dec_ref(v_a_5218_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec(v_a_5213_);
lean_dec(v_a_5212_);
lean_dec_ref(v_b_5211_);
lean_dec_ref(v_a_5210_);
v___x_5283_ = lean_box(0);
if (v_isShared_5268_ == 0)
{
lean_ctor_set(v___x_5267_, 0, v___x_5283_);
v___x_5285_ = v___x_5267_;
goto v_reusejp_5284_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v___x_5283_);
v___x_5285_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5284_;
}
v_reusejp_5284_:
{
return v___x_5285_;
}
}
}
}
else
{
lean_object* v_a_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5295_; 
lean_dec(v_a_5221_);
lean_dec_ref(v_a_5220_);
lean_dec(v_a_5219_);
lean_dec_ref(v_a_5218_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec(v_a_5213_);
lean_dec(v_a_5212_);
lean_dec_ref(v_b_5211_);
lean_dec_ref(v_a_5210_);
v_a_5288_ = lean_ctor_get(v___x_5264_, 0);
v_isSharedCheck_5295_ = !lean_is_exclusive(v___x_5264_);
if (v_isSharedCheck_5295_ == 0)
{
v___x_5290_ = v___x_5264_;
v_isShared_5291_ = v_isSharedCheck_5295_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_a_5288_);
lean_dec(v___x_5264_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5295_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v___x_5293_; 
if (v_isShared_5291_ == 0)
{
v___x_5293_ = v___x_5290_;
goto v_reusejp_5292_;
}
else
{
lean_object* v_reuseFailAlloc_5294_; 
v_reuseFailAlloc_5294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5294_, 0, v_a_5288_);
v___x_5293_ = v_reuseFailAlloc_5294_;
goto v_reusejp_5292_;
}
v_reusejp_5292_:
{
return v___x_5293_;
}
}
}
}
}
else
{
lean_object* v_a_5296_; lean_object* v___x_5298_; uint8_t v_isShared_5299_; uint8_t v_isSharedCheck_5303_; 
lean_dec(v_a_5221_);
lean_dec_ref(v_a_5220_);
lean_dec(v_a_5219_);
lean_dec_ref(v_a_5218_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec(v_a_5213_);
lean_dec(v_a_5212_);
lean_dec_ref(v_b_5211_);
lean_dec_ref(v_a_5210_);
v_a_5296_ = lean_ctor_get(v___x_5224_, 0);
v_isSharedCheck_5303_ = !lean_is_exclusive(v___x_5224_);
if (v_isSharedCheck_5303_ == 0)
{
v___x_5298_ = v___x_5224_;
v_isShared_5299_ = v_isSharedCheck_5303_;
goto v_resetjp_5297_;
}
else
{
lean_inc(v_a_5296_);
lean_dec(v___x_5224_);
v___x_5298_ = lean_box(0);
v_isShared_5299_ = v_isSharedCheck_5303_;
goto v_resetjp_5297_;
}
v_resetjp_5297_:
{
lean_object* v___x_5301_; 
if (v_isShared_5299_ == 0)
{
v___x_5301_ = v___x_5298_;
goto v_reusejp_5300_;
}
else
{
lean_object* v_reuseFailAlloc_5302_; 
v_reuseFailAlloc_5302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5302_, 0, v_a_5296_);
v___x_5301_ = v_reuseFailAlloc_5302_;
goto v_reusejp_5300_;
}
v_reusejp_5300_:
{
return v___x_5301_;
}
}
}
}
else
{
lean_object* v___x_5304_; lean_object* v___x_5305_; 
lean_dec(v_a_5221_);
lean_dec_ref(v_a_5220_);
lean_dec(v_a_5219_);
lean_dec_ref(v_a_5218_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec(v_a_5213_);
lean_dec(v_a_5212_);
lean_dec_ref(v_b_5211_);
lean_dec_ref(v_a_5210_);
v___x_5304_ = lean_box(0);
v___x_5305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5305_, 0, v___x_5304_);
return v___x_5305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed(lean_object* v_a_5306_, lean_object* v_b_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_){
_start:
{
lean_object* v_res_5319_; 
v_res_5319_ = l_Lean_Meta_Grind_Arith_Linear_processNewEq(v_a_5306_, v_b_5307_, v_a_5308_, v_a_5309_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_);
return v_res_5319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object* v_a_5320_, lean_object* v_b_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_, lean_object* v_a_5326_, lean_object* v_a_5327_, lean_object* v_a_5328_, lean_object* v_a_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_){
_start:
{
uint8_t v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; 
v___x_5334_ = 0;
v___x_5335_ = lean_unsigned_to_nat(0u);
v___x_5336_ = lean_box(v___x_5334_);
lean_inc_ref(v_a_5320_);
v___x_5337_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5337_, 0, v_a_5320_);
lean_closure_set(v___x_5337_, 1, v___x_5336_);
lean_closure_set(v___x_5337_, 2, v___x_5335_);
lean_inc(v_a_5332_);
lean_inc_ref(v_a_5331_);
lean_inc(v_a_5330_);
lean_inc_ref(v_a_5329_);
lean_inc(v_a_5328_);
lean_inc_ref(v_a_5327_);
lean_inc(v_a_5326_);
lean_inc_ref(v_a_5325_);
lean_inc(v_a_5324_);
lean_inc(v_a_5323_);
v___x_5338_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5337_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_);
if (lean_obj_tag(v___x_5338_) == 0)
{
lean_object* v_a_5339_; lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5440_; 
v_a_5339_ = lean_ctor_get(v___x_5338_, 0);
v_isSharedCheck_5440_ = !lean_is_exclusive(v___x_5338_);
if (v_isSharedCheck_5440_ == 0)
{
v___x_5341_ = v___x_5338_;
v_isShared_5342_ = v_isSharedCheck_5440_;
goto v_resetjp_5340_;
}
else
{
lean_inc(v_a_5339_);
lean_dec(v___x_5338_);
v___x_5341_ = lean_box(0);
v_isShared_5342_ = v_isSharedCheck_5440_;
goto v_resetjp_5340_;
}
v_resetjp_5340_:
{
if (lean_obj_tag(v_a_5339_) == 1)
{
lean_object* v_val_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; 
lean_del_object(v___x_5341_);
v_val_5343_ = lean_ctor_get(v_a_5339_, 0);
lean_inc(v_val_5343_);
lean_dec_ref(v_a_5339_);
v___x_5344_ = lean_box(v___x_5334_);
lean_inc_ref(v_b_5321_);
v___x_5345_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5345_, 0, v_b_5321_);
lean_closure_set(v___x_5345_, 1, v___x_5344_);
lean_closure_set(v___x_5345_, 2, v___x_5335_);
lean_inc(v_a_5332_);
lean_inc_ref(v_a_5331_);
lean_inc(v_a_5330_);
lean_inc_ref(v_a_5329_);
lean_inc(v_a_5328_);
lean_inc_ref(v_a_5327_);
lean_inc(v_a_5326_);
lean_inc_ref(v_a_5325_);
lean_inc(v_a_5324_);
lean_inc(v_a_5323_);
v___x_5346_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5345_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_);
if (lean_obj_tag(v___x_5346_) == 0)
{
lean_object* v_a_5347_; lean_object* v___x_5349_; uint8_t v_isShared_5350_; uint8_t v_isSharedCheck_5427_; 
v_a_5347_ = lean_ctor_get(v___x_5346_, 0);
v_isSharedCheck_5427_ = !lean_is_exclusive(v___x_5346_);
if (v_isSharedCheck_5427_ == 0)
{
v___x_5349_ = v___x_5346_;
v_isShared_5350_ = v_isSharedCheck_5427_;
goto v_resetjp_5348_;
}
else
{
lean_inc(v_a_5347_);
lean_dec(v___x_5346_);
v___x_5349_ = lean_box(0);
v_isShared_5350_ = v_isSharedCheck_5427_;
goto v_resetjp_5348_;
}
v_resetjp_5348_:
{
if (lean_obj_tag(v_a_5347_) == 1)
{
lean_object* v_val_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; 
lean_del_object(v___x_5349_);
v_val_5351_ = lean_ctor_get(v_a_5347_, 0);
lean_inc(v_val_5351_);
lean_dec_ref(v_a_5347_);
lean_inc(v_val_5351_);
lean_inc(v_val_5343_);
v___x_5352_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_5352_, 0, v_val_5343_);
lean_ctor_set(v___x_5352_, 1, v_val_5351_);
v___x_5353_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_5352_);
lean_inc_ref(v_b_5321_);
lean_inc_ref(v_a_5320_);
v___x_5354_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5354_, 0, v_a_5320_);
lean_ctor_set(v___x_5354_, 1, v_b_5321_);
lean_ctor_set(v___x_5354_, 2, v_val_5343_);
lean_ctor_set(v___x_5354_, 3, v_val_5351_);
v___x_5355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5355_, 0, v___x_5353_);
lean_ctor_set(v___x_5355_, 1, v___x_5354_);
lean_inc(v_a_5332_);
lean_inc_ref(v_a_5331_);
lean_inc(v_a_5330_);
lean_inc_ref(v_a_5329_);
lean_inc(v_a_5328_);
lean_inc_ref(v_a_5327_);
lean_inc(v_a_5326_);
lean_inc_ref(v_a_5325_);
lean_inc(v_a_5324_);
lean_inc(v_a_5323_);
v___x_5356_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(v___x_5355_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_);
if (lean_obj_tag(v___x_5356_) == 0)
{
lean_object* v_a_5357_; lean_object* v___x_5358_; 
v_a_5357_ = lean_ctor_get(v___x_5356_, 0);
lean_inc(v_a_5357_);
lean_dec_ref(v___x_5356_);
v___x_5358_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5320_, v_a_5323_);
lean_dec_ref(v_a_5320_);
if (lean_obj_tag(v___x_5358_) == 0)
{
lean_object* v_a_5359_; lean_object* v___x_5360_; 
v_a_5359_ = lean_ctor_get(v___x_5358_, 0);
lean_inc(v_a_5359_);
lean_dec_ref(v___x_5358_);
v___x_5360_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5321_, v_a_5323_);
lean_dec_ref(v_b_5321_);
if (lean_obj_tag(v___x_5360_) == 0)
{
lean_object* v_a_5361_; lean_object* v_p_5362_; lean_object* v___y_5364_; uint8_t v___x_5398_; 
v_a_5361_ = lean_ctor_get(v___x_5360_, 0);
lean_inc(v_a_5361_);
lean_dec_ref(v___x_5360_);
v_p_5362_ = lean_ctor_get(v_a_5357_, 0);
v___x_5398_ = lean_nat_dec_le(v_a_5359_, v_a_5361_);
if (v___x_5398_ == 0)
{
lean_dec(v_a_5361_);
v___y_5364_ = v_a_5359_;
goto v___jp_5363_;
}
else
{
lean_dec(v_a_5359_);
v___y_5364_ = v_a_5361_;
goto v___jp_5363_;
}
v___jp_5363_:
{
lean_object* v___x_5365_; 
lean_inc(v_a_5332_);
lean_inc_ref(v_a_5331_);
lean_inc(v_a_5330_);
lean_inc_ref(v_a_5329_);
lean_inc(v_a_5328_);
lean_inc_ref(v_a_5327_);
lean_inc(v_a_5326_);
lean_inc_ref(v_a_5325_);
lean_inc(v_a_5324_);
lean_inc(v_a_5323_);
lean_inc(v___y_5364_);
lean_inc_ref(v_p_5362_);
v___x_5365_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_5362_, v___y_5364_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_);
if (lean_obj_tag(v___x_5365_) == 0)
{
lean_object* v_a_5366_; lean_object* v___x_5367_; 
v_a_5366_ = lean_ctor_get(v___x_5365_, 0);
lean_inc(v_a_5366_);
lean_dec_ref(v___x_5365_);
lean_inc(v_a_5332_);
lean_inc_ref(v_a_5331_);
lean_inc(v_a_5330_);
lean_inc_ref(v_a_5329_);
lean_inc(v_a_5328_);
lean_inc_ref(v_a_5327_);
lean_inc(v_a_5326_);
lean_inc_ref(v_a_5325_);
lean_inc(v_a_5324_);
lean_inc(v_a_5323_);
lean_inc(v_a_5322_);
v___x_5367_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5366_, v___x_5334_, v___y_5364_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_);
if (lean_obj_tag(v___x_5367_) == 0)
{
lean_object* v_a_5368_; lean_object* v___x_5370_; uint8_t v_isShared_5371_; uint8_t v_isSharedCheck_5381_; 
v_a_5368_ = lean_ctor_get(v___x_5367_, 0);
v_isSharedCheck_5381_ = !lean_is_exclusive(v___x_5367_);
if (v_isSharedCheck_5381_ == 0)
{
v___x_5370_ = v___x_5367_;
v_isShared_5371_ = v_isSharedCheck_5381_;
goto v_resetjp_5369_;
}
else
{
lean_inc(v_a_5368_);
lean_dec(v___x_5367_);
v___x_5370_ = lean_box(0);
v_isShared_5371_ = v_isSharedCheck_5381_;
goto v_resetjp_5369_;
}
v_resetjp_5369_:
{
if (lean_obj_tag(v_a_5368_) == 1)
{
lean_object* v_val_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; 
lean_del_object(v___x_5370_);
v_val_5372_ = lean_ctor_get(v_a_5368_, 0);
lean_inc(v_val_5372_);
lean_dec_ref(v_a_5368_);
lean_inc(v_val_5372_);
v___x_5373_ = l_Lean_Grind_Linarith_Expr_norm(v_val_5372_);
v___x_5374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5374_, 0, v_a_5357_);
lean_ctor_set(v___x_5374_, 1, v_val_5372_);
v___x_5375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5375_, 0, v___x_5373_);
lean_ctor_set(v___x_5375_, 1, v___x_5374_);
v___x_5376_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5375_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_);
return v___x_5376_;
}
else
{
lean_object* v___x_5377_; lean_object* v___x_5379_; 
lean_dec(v_a_5368_);
lean_dec(v_a_5357_);
lean_dec(v_a_5332_);
lean_dec_ref(v_a_5331_);
lean_dec(v_a_5330_);
lean_dec_ref(v_a_5329_);
lean_dec(v_a_5328_);
lean_dec_ref(v_a_5327_);
lean_dec(v_a_5326_);
lean_dec_ref(v_a_5325_);
lean_dec(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec(v_a_5322_);
v___x_5377_ = lean_box(0);
if (v_isShared_5371_ == 0)
{
lean_ctor_set(v___x_5370_, 0, v___x_5377_);
v___x_5379_ = v___x_5370_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v___x_5377_);
v___x_5379_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
return v___x_5379_;
}
}
}
}
else
{
lean_object* v_a_5382_; lean_object* v___x_5384_; uint8_t v_isShared_5385_; uint8_t v_isSharedCheck_5389_; 
lean_dec(v_a_5357_);
lean_dec(v_a_5332_);
lean_dec_ref(v_a_5331_);
lean_dec(v_a_5330_);
lean_dec_ref(v_a_5329_);
lean_dec(v_a_5328_);
lean_dec_ref(v_a_5327_);
lean_dec(v_a_5326_);
lean_dec_ref(v_a_5325_);
lean_dec(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec(v_a_5322_);
v_a_5382_ = lean_ctor_get(v___x_5367_, 0);
v_isSharedCheck_5389_ = !lean_is_exclusive(v___x_5367_);
if (v_isSharedCheck_5389_ == 0)
{
v___x_5384_ = v___x_5367_;
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
else
{
lean_inc(v_a_5382_);
lean_dec(v___x_5367_);
v___x_5384_ = lean_box(0);
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
v_resetjp_5383_:
{
lean_object* v___x_5387_; 
if (v_isShared_5385_ == 0)
{
v___x_5387_ = v___x_5384_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_a_5382_);
v___x_5387_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
return v___x_5387_;
}
}
}
}
else
{
lean_object* v_a_5390_; lean_object* v___x_5392_; uint8_t v_isShared_5393_; uint8_t v_isSharedCheck_5397_; 
lean_dec(v___y_5364_);
lean_dec(v_a_5357_);
lean_dec(v_a_5332_);
lean_dec_ref(v_a_5331_);
lean_dec(v_a_5330_);
lean_dec_ref(v_a_5329_);
lean_dec(v_a_5328_);
lean_dec_ref(v_a_5327_);
lean_dec(v_a_5326_);
lean_dec_ref(v_a_5325_);
lean_dec(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec(v_a_5322_);
v_a_5390_ = lean_ctor_get(v___x_5365_, 0);
v_isSharedCheck_5397_ = !lean_is_exclusive(v___x_5365_);
if (v_isSharedCheck_5397_ == 0)
{
v___x_5392_ = v___x_5365_;
v_isShared_5393_ = v_isSharedCheck_5397_;
goto v_resetjp_5391_;
}
else
{
lean_inc(v_a_5390_);
lean_dec(v___x_5365_);
v___x_5392_ = lean_box(0);
v_isShared_5393_ = v_isSharedCheck_5397_;
goto v_resetjp_5391_;
}
v_resetjp_5391_:
{
lean_object* v___x_5395_; 
if (v_isShared_5393_ == 0)
{
v___x_5395_ = v___x_5392_;
goto v_reusejp_5394_;
}
else
{
lean_object* v_reuseFailAlloc_5396_; 
v_reuseFailAlloc_5396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5396_, 0, v_a_5390_);
v___x_5395_ = v_reuseFailAlloc_5396_;
goto v_reusejp_5394_;
}
v_reusejp_5394_:
{
return v___x_5395_;
}
}
}
}
}
else
{
lean_object* v_a_5399_; lean_object* v___x_5401_; uint8_t v_isShared_5402_; uint8_t v_isSharedCheck_5406_; 
lean_dec(v_a_5359_);
lean_dec(v_a_5357_);
lean_dec(v_a_5332_);
lean_dec_ref(v_a_5331_);
lean_dec(v_a_5330_);
lean_dec_ref(v_a_5329_);
lean_dec(v_a_5328_);
lean_dec_ref(v_a_5327_);
lean_dec(v_a_5326_);
lean_dec_ref(v_a_5325_);
lean_dec(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec(v_a_5322_);
v_a_5399_ = lean_ctor_get(v___x_5360_, 0);
v_isSharedCheck_5406_ = !lean_is_exclusive(v___x_5360_);
if (v_isSharedCheck_5406_ == 0)
{
v___x_5401_ = v___x_5360_;
v_isShared_5402_ = v_isSharedCheck_5406_;
goto v_resetjp_5400_;
}
else
{
lean_inc(v_a_5399_);
lean_dec(v___x_5360_);
v___x_5401_ = lean_box(0);
v_isShared_5402_ = v_isSharedCheck_5406_;
goto v_resetjp_5400_;
}
v_resetjp_5400_:
{
lean_object* v___x_5404_; 
if (v_isShared_5402_ == 0)
{
v___x_5404_ = v___x_5401_;
goto v_reusejp_5403_;
}
else
{
lean_object* v_reuseFailAlloc_5405_; 
v_reuseFailAlloc_5405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5405_, 0, v_a_5399_);
v___x_5404_ = v_reuseFailAlloc_5405_;
goto v_reusejp_5403_;
}
v_reusejp_5403_:
{
return v___x_5404_;
}
}
}
}
else
{
lean_object* v_a_5407_; lean_object* v___x_5409_; uint8_t v_isShared_5410_; uint8_t v_isSharedCheck_5414_; 
lean_dec(v_a_5357_);
lean_dec(v_a_5332_);
lean_dec_ref(v_a_5331_);
lean_dec(v_a_5330_);
lean_dec_ref(v_a_5329_);
lean_dec(v_a_5328_);
lean_dec_ref(v_a_5327_);
lean_dec(v_a_5326_);
lean_dec_ref(v_a_5325_);
lean_dec(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec(v_a_5322_);
lean_dec_ref(v_b_5321_);
v_a_5407_ = lean_ctor_get(v___x_5358_, 0);
v_isSharedCheck_5414_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5414_ == 0)
{
v___x_5409_ = v___x_5358_;
v_isShared_5410_ = v_isSharedCheck_5414_;
goto v_resetjp_5408_;
}
else
{
lean_inc(v_a_5407_);
lean_dec(v___x_5358_);
v___x_5409_ = lean_box(0);
v_isShared_5410_ = v_isSharedCheck_5414_;
goto v_resetjp_5408_;
}
v_resetjp_5408_:
{
lean_object* v___x_5412_; 
if (v_isShared_5410_ == 0)
{
v___x_5412_ = v___x_5409_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5413_; 
v_reuseFailAlloc_5413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5413_, 0, v_a_5407_);
v___x_5412_ = v_reuseFailAlloc_5413_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
return v___x_5412_;
}
}
}
}
else
{
lean_object* v_a_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5422_; 
lean_dec(v_a_5332_);
lean_dec_ref(v_a_5331_);
lean_dec(v_a_5330_);
lean_dec_ref(v_a_5329_);
lean_dec(v_a_5328_);
lean_dec_ref(v_a_5327_);
lean_dec(v_a_5326_);
lean_dec_ref(v_a_5325_);
lean_dec(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec(v_a_5322_);
lean_dec_ref(v_b_5321_);
lean_dec_ref(v_a_5320_);
v_a_5415_ = lean_ctor_get(v___x_5356_, 0);
v_isSharedCheck_5422_ = !lean_is_exclusive(v___x_5356_);
if (v_isSharedCheck_5422_ == 0)
{
v___x_5417_ = v___x_5356_;
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_a_5415_);
lean_dec(v___x_5356_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
lean_object* v___x_5420_; 
if (v_isShared_5418_ == 0)
{
v___x_5420_ = v___x_5417_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5421_, 0, v_a_5415_);
v___x_5420_ = v_reuseFailAlloc_5421_;
goto v_reusejp_5419_;
}
v_reusejp_5419_:
{
return v___x_5420_;
}
}
}
}
else
{
lean_object* v___x_5423_; lean_object* v___x_5425_; 
lean_dec(v_a_5347_);
lean_dec(v_val_5343_);
lean_dec(v_a_5332_);
lean_dec_ref(v_a_5331_);
lean_dec(v_a_5330_);
lean_dec_ref(v_a_5329_);
lean_dec(v_a_5328_);
lean_dec_ref(v_a_5327_);
lean_dec(v_a_5326_);
lean_dec_ref(v_a_5325_);
lean_dec(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec(v_a_5322_);
lean_dec_ref(v_b_5321_);
lean_dec_ref(v_a_5320_);
v___x_5423_ = lean_box(0);
if (v_isShared_5350_ == 0)
{
lean_ctor_set(v___x_5349_, 0, v___x_5423_);
v___x_5425_ = v___x_5349_;
goto v_reusejp_5424_;
}
else
{
lean_object* v_reuseFailAlloc_5426_; 
v_reuseFailAlloc_5426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5426_, 0, v___x_5423_);
v___x_5425_ = v_reuseFailAlloc_5426_;
goto v_reusejp_5424_;
}
v_reusejp_5424_:
{
return v___x_5425_;
}
}
}
}
else
{
lean_object* v_a_5428_; lean_object* v___x_5430_; uint8_t v_isShared_5431_; uint8_t v_isSharedCheck_5435_; 
lean_dec(v_val_5343_);
lean_dec(v_a_5332_);
lean_dec_ref(v_a_5331_);
lean_dec(v_a_5330_);
lean_dec_ref(v_a_5329_);
lean_dec(v_a_5328_);
lean_dec_ref(v_a_5327_);
lean_dec(v_a_5326_);
lean_dec_ref(v_a_5325_);
lean_dec(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec(v_a_5322_);
lean_dec_ref(v_b_5321_);
lean_dec_ref(v_a_5320_);
v_a_5428_ = lean_ctor_get(v___x_5346_, 0);
v_isSharedCheck_5435_ = !lean_is_exclusive(v___x_5346_);
if (v_isSharedCheck_5435_ == 0)
{
v___x_5430_ = v___x_5346_;
v_isShared_5431_ = v_isSharedCheck_5435_;
goto v_resetjp_5429_;
}
else
{
lean_inc(v_a_5428_);
lean_dec(v___x_5346_);
v___x_5430_ = lean_box(0);
v_isShared_5431_ = v_isSharedCheck_5435_;
goto v_resetjp_5429_;
}
v_resetjp_5429_:
{
lean_object* v___x_5433_; 
if (v_isShared_5431_ == 0)
{
v___x_5433_ = v___x_5430_;
goto v_reusejp_5432_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_a_5428_);
v___x_5433_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5432_;
}
v_reusejp_5432_:
{
return v___x_5433_;
}
}
}
}
else
{
lean_object* v___x_5436_; lean_object* v___x_5438_; 
lean_dec(v_a_5339_);
lean_dec(v_a_5332_);
lean_dec_ref(v_a_5331_);
lean_dec(v_a_5330_);
lean_dec_ref(v_a_5329_);
lean_dec(v_a_5328_);
lean_dec_ref(v_a_5327_);
lean_dec(v_a_5326_);
lean_dec_ref(v_a_5325_);
lean_dec(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec(v_a_5322_);
lean_dec_ref(v_b_5321_);
lean_dec_ref(v_a_5320_);
v___x_5436_ = lean_box(0);
if (v_isShared_5342_ == 0)
{
lean_ctor_set(v___x_5341_, 0, v___x_5436_);
v___x_5438_ = v___x_5341_;
goto v_reusejp_5437_;
}
else
{
lean_object* v_reuseFailAlloc_5439_; 
v_reuseFailAlloc_5439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5439_, 0, v___x_5436_);
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
lean_dec(v_a_5332_);
lean_dec_ref(v_a_5331_);
lean_dec(v_a_5330_);
lean_dec_ref(v_a_5329_);
lean_dec(v_a_5328_);
lean_dec_ref(v_a_5327_);
lean_dec(v_a_5326_);
lean_dec_ref(v_a_5325_);
lean_dec(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec(v_a_5322_);
lean_dec_ref(v_b_5321_);
lean_dec_ref(v_a_5320_);
v_a_5441_ = lean_ctor_get(v___x_5338_, 0);
v_isSharedCheck_5448_ = !lean_is_exclusive(v___x_5338_);
if (v_isSharedCheck_5448_ == 0)
{
v___x_5443_ = v___x_5338_;
v_isShared_5444_ = v_isSharedCheck_5448_;
goto v_resetjp_5442_;
}
else
{
lean_inc(v_a_5441_);
lean_dec(v___x_5338_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq___boxed(lean_object* v_a_5449_, lean_object* v_b_5450_, lean_object* v_a_5451_, lean_object* v_a_5452_, lean_object* v_a_5453_, lean_object* v_a_5454_, lean_object* v_a_5455_, lean_object* v_a_5456_, lean_object* v_a_5457_, lean_object* v_a_5458_, lean_object* v_a_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_){
_start:
{
lean_object* v_res_5463_; 
v_res_5463_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5449_, v_b_5450_, v_a_5451_, v_a_5452_, v_a_5453_, v_a_5454_, v_a_5455_, v_a_5456_, v_a_5457_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_);
return v_res_5463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(lean_object* v_a_5464_, lean_object* v_b_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_, lean_object* v_a_5469_, lean_object* v_a_5470_, lean_object* v_a_5471_, lean_object* v_a_5472_, lean_object* v_a_5473_, lean_object* v_a_5474_, lean_object* v_a_5475_, lean_object* v_a_5476_){
_start:
{
lean_object* v___x_5478_; 
v___x_5478_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5464_, v_a_5467_);
if (lean_obj_tag(v___x_5478_) == 0)
{
lean_object* v_a_5479_; uint8_t v___x_5480_; lean_object* v___x_5481_; 
v_a_5479_ = lean_ctor_get(v___x_5478_, 0);
lean_inc(v_a_5479_);
lean_dec_ref(v___x_5478_);
v___x_5480_ = 0;
lean_inc(v_a_5476_);
lean_inc_ref(v_a_5475_);
lean_inc(v_a_5474_);
lean_inc_ref(v_a_5473_);
lean_inc(v_a_5472_);
lean_inc_ref(v_a_5471_);
lean_inc(v_a_5470_);
lean_inc_ref(v_a_5469_);
lean_inc(v_a_5468_);
lean_inc(v_a_5467_);
lean_inc(v_a_5466_);
lean_inc_ref(v_a_5464_);
v___x_5481_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5464_, v___x_5480_, v_a_5479_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_, v_a_5472_, v_a_5473_, v_a_5474_, v_a_5475_, v_a_5476_);
if (lean_obj_tag(v___x_5481_) == 0)
{
lean_object* v_a_5482_; lean_object* v___x_5484_; uint8_t v_isShared_5485_; uint8_t v_isSharedCheck_5525_; 
v_a_5482_ = lean_ctor_get(v___x_5481_, 0);
v_isSharedCheck_5525_ = !lean_is_exclusive(v___x_5481_);
if (v_isSharedCheck_5525_ == 0)
{
v___x_5484_ = v___x_5481_;
v_isShared_5485_ = v_isSharedCheck_5525_;
goto v_resetjp_5483_;
}
else
{
lean_inc(v_a_5482_);
lean_dec(v___x_5481_);
v___x_5484_ = lean_box(0);
v_isShared_5485_ = v_isSharedCheck_5525_;
goto v_resetjp_5483_;
}
v_resetjp_5483_:
{
if (lean_obj_tag(v_a_5482_) == 1)
{
lean_object* v_val_5486_; lean_object* v___x_5487_; 
lean_del_object(v___x_5484_);
v_val_5486_ = lean_ctor_get(v_a_5482_, 0);
lean_inc(v_val_5486_);
lean_dec_ref(v_a_5482_);
v___x_5487_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5465_, v_a_5467_);
if (lean_obj_tag(v___x_5487_) == 0)
{
lean_object* v_a_5488_; lean_object* v___x_5489_; 
v_a_5488_ = lean_ctor_get(v___x_5487_, 0);
lean_inc(v_a_5488_);
lean_dec_ref(v___x_5487_);
lean_inc(v_a_5476_);
lean_inc_ref(v_a_5475_);
lean_inc(v_a_5474_);
lean_inc_ref(v_a_5473_);
lean_inc(v_a_5472_);
lean_inc_ref(v_a_5471_);
lean_inc(v_a_5470_);
lean_inc_ref(v_a_5469_);
lean_inc(v_a_5468_);
lean_inc(v_a_5467_);
lean_inc(v_a_5466_);
lean_inc_ref(v_b_5465_);
v___x_5489_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_5465_, v___x_5480_, v_a_5488_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_, v_a_5472_, v_a_5473_, v_a_5474_, v_a_5475_, v_a_5476_);
if (lean_obj_tag(v___x_5489_) == 0)
{
lean_object* v_a_5490_; lean_object* v___x_5492_; uint8_t v_isShared_5493_; uint8_t v_isSharedCheck_5504_; 
v_a_5490_ = lean_ctor_get(v___x_5489_, 0);
v_isSharedCheck_5504_ = !lean_is_exclusive(v___x_5489_);
if (v_isSharedCheck_5504_ == 0)
{
v___x_5492_ = v___x_5489_;
v_isShared_5493_ = v_isSharedCheck_5504_;
goto v_resetjp_5491_;
}
else
{
lean_inc(v_a_5490_);
lean_dec(v___x_5489_);
v___x_5492_ = lean_box(0);
v_isShared_5493_ = v_isSharedCheck_5504_;
goto v_resetjp_5491_;
}
v_resetjp_5491_:
{
if (lean_obj_tag(v_a_5490_) == 1)
{
lean_object* v_val_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; 
lean_del_object(v___x_5492_);
v_val_5494_ = lean_ctor_get(v_a_5490_, 0);
lean_inc(v_val_5494_);
lean_dec_ref(v_a_5490_);
lean_inc(v_val_5494_);
lean_inc(v_val_5486_);
v___x_5495_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5495_, 0, v_val_5486_);
lean_ctor_set(v___x_5495_, 1, v_val_5494_);
v___x_5496_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5495_);
v___x_5497_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5497_, 0, v_a_5464_);
lean_ctor_set(v___x_5497_, 1, v_b_5465_);
lean_ctor_set(v___x_5497_, 2, v_val_5486_);
lean_ctor_set(v___x_5497_, 3, v_val_5494_);
v___x_5498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5498_, 0, v___x_5496_);
lean_ctor_set(v___x_5498_, 1, v___x_5497_);
v___x_5499_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5498_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_, v_a_5472_, v_a_5473_, v_a_5474_, v_a_5475_, v_a_5476_);
return v___x_5499_;
}
else
{
lean_object* v___x_5500_; lean_object* v___x_5502_; 
lean_dec(v_a_5490_);
lean_dec(v_val_5486_);
lean_dec(v_a_5476_);
lean_dec_ref(v_a_5475_);
lean_dec(v_a_5474_);
lean_dec_ref(v_a_5473_);
lean_dec(v_a_5472_);
lean_dec_ref(v_a_5471_);
lean_dec(v_a_5470_);
lean_dec_ref(v_a_5469_);
lean_dec(v_a_5468_);
lean_dec(v_a_5467_);
lean_dec(v_a_5466_);
lean_dec_ref(v_b_5465_);
lean_dec_ref(v_a_5464_);
v___x_5500_ = lean_box(0);
if (v_isShared_5493_ == 0)
{
lean_ctor_set(v___x_5492_, 0, v___x_5500_);
v___x_5502_ = v___x_5492_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5503_; 
v_reuseFailAlloc_5503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5503_, 0, v___x_5500_);
v___x_5502_ = v_reuseFailAlloc_5503_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
return v___x_5502_;
}
}
}
}
else
{
lean_object* v_a_5505_; lean_object* v___x_5507_; uint8_t v_isShared_5508_; uint8_t v_isSharedCheck_5512_; 
lean_dec(v_val_5486_);
lean_dec(v_a_5476_);
lean_dec_ref(v_a_5475_);
lean_dec(v_a_5474_);
lean_dec_ref(v_a_5473_);
lean_dec(v_a_5472_);
lean_dec_ref(v_a_5471_);
lean_dec(v_a_5470_);
lean_dec_ref(v_a_5469_);
lean_dec(v_a_5468_);
lean_dec(v_a_5467_);
lean_dec(v_a_5466_);
lean_dec_ref(v_b_5465_);
lean_dec_ref(v_a_5464_);
v_a_5505_ = lean_ctor_get(v___x_5489_, 0);
v_isSharedCheck_5512_ = !lean_is_exclusive(v___x_5489_);
if (v_isSharedCheck_5512_ == 0)
{
v___x_5507_ = v___x_5489_;
v_isShared_5508_ = v_isSharedCheck_5512_;
goto v_resetjp_5506_;
}
else
{
lean_inc(v_a_5505_);
lean_dec(v___x_5489_);
v___x_5507_ = lean_box(0);
v_isShared_5508_ = v_isSharedCheck_5512_;
goto v_resetjp_5506_;
}
v_resetjp_5506_:
{
lean_object* v___x_5510_; 
if (v_isShared_5508_ == 0)
{
v___x_5510_ = v___x_5507_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5511_; 
v_reuseFailAlloc_5511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5511_, 0, v_a_5505_);
v___x_5510_ = v_reuseFailAlloc_5511_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
return v___x_5510_;
}
}
}
}
else
{
lean_object* v_a_5513_; lean_object* v___x_5515_; uint8_t v_isShared_5516_; uint8_t v_isSharedCheck_5520_; 
lean_dec(v_val_5486_);
lean_dec(v_a_5476_);
lean_dec_ref(v_a_5475_);
lean_dec(v_a_5474_);
lean_dec_ref(v_a_5473_);
lean_dec(v_a_5472_);
lean_dec_ref(v_a_5471_);
lean_dec(v_a_5470_);
lean_dec_ref(v_a_5469_);
lean_dec(v_a_5468_);
lean_dec(v_a_5467_);
lean_dec(v_a_5466_);
lean_dec_ref(v_b_5465_);
lean_dec_ref(v_a_5464_);
v_a_5513_ = lean_ctor_get(v___x_5487_, 0);
v_isSharedCheck_5520_ = !lean_is_exclusive(v___x_5487_);
if (v_isSharedCheck_5520_ == 0)
{
v___x_5515_ = v___x_5487_;
v_isShared_5516_ = v_isSharedCheck_5520_;
goto v_resetjp_5514_;
}
else
{
lean_inc(v_a_5513_);
lean_dec(v___x_5487_);
v___x_5515_ = lean_box(0);
v_isShared_5516_ = v_isSharedCheck_5520_;
goto v_resetjp_5514_;
}
v_resetjp_5514_:
{
lean_object* v___x_5518_; 
if (v_isShared_5516_ == 0)
{
v___x_5518_ = v___x_5515_;
goto v_reusejp_5517_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_a_5513_);
v___x_5518_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5517_;
}
v_reusejp_5517_:
{
return v___x_5518_;
}
}
}
}
else
{
lean_object* v___x_5521_; lean_object* v___x_5523_; 
lean_dec(v_a_5482_);
lean_dec(v_a_5476_);
lean_dec_ref(v_a_5475_);
lean_dec(v_a_5474_);
lean_dec_ref(v_a_5473_);
lean_dec(v_a_5472_);
lean_dec_ref(v_a_5471_);
lean_dec(v_a_5470_);
lean_dec_ref(v_a_5469_);
lean_dec(v_a_5468_);
lean_dec(v_a_5467_);
lean_dec(v_a_5466_);
lean_dec_ref(v_b_5465_);
lean_dec_ref(v_a_5464_);
v___x_5521_ = lean_box(0);
if (v_isShared_5485_ == 0)
{
lean_ctor_set(v___x_5484_, 0, v___x_5521_);
v___x_5523_ = v___x_5484_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v___x_5521_);
v___x_5523_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
return v___x_5523_;
}
}
}
}
else
{
lean_object* v_a_5526_; lean_object* v___x_5528_; uint8_t v_isShared_5529_; uint8_t v_isSharedCheck_5533_; 
lean_dec(v_a_5476_);
lean_dec_ref(v_a_5475_);
lean_dec(v_a_5474_);
lean_dec_ref(v_a_5473_);
lean_dec(v_a_5472_);
lean_dec_ref(v_a_5471_);
lean_dec(v_a_5470_);
lean_dec_ref(v_a_5469_);
lean_dec(v_a_5468_);
lean_dec(v_a_5467_);
lean_dec(v_a_5466_);
lean_dec_ref(v_b_5465_);
lean_dec_ref(v_a_5464_);
v_a_5526_ = lean_ctor_get(v___x_5481_, 0);
v_isSharedCheck_5533_ = !lean_is_exclusive(v___x_5481_);
if (v_isSharedCheck_5533_ == 0)
{
v___x_5528_ = v___x_5481_;
v_isShared_5529_ = v_isSharedCheck_5533_;
goto v_resetjp_5527_;
}
else
{
lean_inc(v_a_5526_);
lean_dec(v___x_5481_);
v___x_5528_ = lean_box(0);
v_isShared_5529_ = v_isSharedCheck_5533_;
goto v_resetjp_5527_;
}
v_resetjp_5527_:
{
lean_object* v___x_5531_; 
if (v_isShared_5529_ == 0)
{
v___x_5531_ = v___x_5528_;
goto v_reusejp_5530_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v_a_5526_);
v___x_5531_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5530_;
}
v_reusejp_5530_:
{
return v___x_5531_;
}
}
}
}
else
{
lean_object* v_a_5534_; lean_object* v___x_5536_; uint8_t v_isShared_5537_; uint8_t v_isSharedCheck_5541_; 
lean_dec(v_a_5476_);
lean_dec_ref(v_a_5475_);
lean_dec(v_a_5474_);
lean_dec_ref(v_a_5473_);
lean_dec(v_a_5472_);
lean_dec_ref(v_a_5471_);
lean_dec(v_a_5470_);
lean_dec_ref(v_a_5469_);
lean_dec(v_a_5468_);
lean_dec(v_a_5467_);
lean_dec(v_a_5466_);
lean_dec_ref(v_b_5465_);
lean_dec_ref(v_a_5464_);
v_a_5534_ = lean_ctor_get(v___x_5478_, 0);
v_isSharedCheck_5541_ = !lean_is_exclusive(v___x_5478_);
if (v_isSharedCheck_5541_ == 0)
{
v___x_5536_ = v___x_5478_;
v_isShared_5537_ = v_isSharedCheck_5541_;
goto v_resetjp_5535_;
}
else
{
lean_inc(v_a_5534_);
lean_dec(v___x_5478_);
v___x_5536_ = lean_box(0);
v_isShared_5537_ = v_isSharedCheck_5541_;
goto v_resetjp_5535_;
}
v_resetjp_5535_:
{
lean_object* v___x_5539_; 
if (v_isShared_5537_ == 0)
{
v___x_5539_ = v___x_5536_;
goto v_reusejp_5538_;
}
else
{
lean_object* v_reuseFailAlloc_5540_; 
v_reuseFailAlloc_5540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5540_, 0, v_a_5534_);
v___x_5539_ = v_reuseFailAlloc_5540_;
goto v_reusejp_5538_;
}
v_reusejp_5538_:
{
return v___x_5539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq___boxed(lean_object* v_a_5542_, lean_object* v_b_5543_, lean_object* v_a_5544_, lean_object* v_a_5545_, lean_object* v_a_5546_, lean_object* v_a_5547_, lean_object* v_a_5548_, lean_object* v_a_5549_, lean_object* v_a_5550_, lean_object* v_a_5551_, lean_object* v_a_5552_, lean_object* v_a_5553_, lean_object* v_a_5554_, lean_object* v_a_5555_){
_start:
{
lean_object* v_res_5556_; 
v_res_5556_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5542_, v_b_5543_, v_a_5544_, v_a_5545_, v_a_5546_, v_a_5547_, v_a_5548_, v_a_5549_, v_a_5550_, v_a_5551_, v_a_5552_, v_a_5553_, v_a_5554_);
return v_res_5556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(lean_object* v_a_5557_, lean_object* v_b_5558_, lean_object* v_a_5559_, lean_object* v_a_5560_, lean_object* v_a_5561_, lean_object* v_a_5562_, lean_object* v_a_5563_, lean_object* v_a_5564_, lean_object* v_a_5565_, lean_object* v_a_5566_, lean_object* v_a_5567_, lean_object* v_a_5568_, lean_object* v_a_5569_){
_start:
{
lean_object* v___x_5571_; 
v___x_5571_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5559_, v_a_5560_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_);
if (lean_obj_tag(v___x_5571_) == 0)
{
lean_object* v_a_5572_; lean_object* v_addRightCancelInst_x3f_5573_; 
v_a_5572_ = lean_ctor_get(v___x_5571_, 0);
lean_inc(v_a_5572_);
lean_dec_ref(v___x_5571_);
v_addRightCancelInst_x3f_5573_ = lean_ctor_get(v_a_5572_, 11);
if (lean_obj_tag(v_addRightCancelInst_x3f_5573_) == 0)
{
lean_object* v___x_5574_; 
lean_dec(v_a_5572_);
v___x_5574_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(v_a_5557_, v_b_5558_, v_a_5559_, v_a_5560_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_);
lean_dec(v_a_5559_);
return v___x_5574_;
}
else
{
lean_object* v_id_5575_; lean_object* v_structId_5576_; lean_object* v___x_5577_; 
v_id_5575_ = lean_ctor_get(v_a_5572_, 0);
lean_inc(v_id_5575_);
v_structId_5576_ = lean_ctor_get(v_a_5572_, 1);
lean_inc(v_structId_5576_);
lean_dec(v_a_5572_);
lean_inc(v_a_5569_);
lean_inc_ref(v_a_5568_);
lean_inc(v_a_5567_);
lean_inc_ref(v_a_5566_);
lean_inc(v_a_5565_);
lean_inc_ref(v_a_5564_);
lean_inc(v_a_5563_);
lean_inc_ref(v_a_5562_);
lean_inc(v_a_5561_);
lean_inc(v_a_5560_);
lean_inc(v_a_5559_);
lean_inc_ref(v_a_5557_);
v___x_5577_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5557_, v_a_5559_, v_a_5560_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_);
if (lean_obj_tag(v___x_5577_) == 0)
{
lean_object* v_a_5578_; lean_object* v_fst_5579_; lean_object* v___x_5581_; uint8_t v_isShared_5582_; uint8_t v_isSharedCheck_5667_; 
v_a_5578_ = lean_ctor_get(v___x_5577_, 0);
lean_inc(v_a_5578_);
lean_dec_ref(v___x_5577_);
v_fst_5579_ = lean_ctor_get(v_a_5578_, 0);
v_isSharedCheck_5667_ = !lean_is_exclusive(v_a_5578_);
if (v_isSharedCheck_5667_ == 0)
{
lean_object* v_unused_5668_; 
v_unused_5668_ = lean_ctor_get(v_a_5578_, 1);
lean_dec(v_unused_5668_);
v___x_5581_ = v_a_5578_;
v_isShared_5582_ = v_isSharedCheck_5667_;
goto v_resetjp_5580_;
}
else
{
lean_inc(v_fst_5579_);
lean_dec(v_a_5578_);
v___x_5581_ = lean_box(0);
v_isShared_5582_ = v_isSharedCheck_5667_;
goto v_resetjp_5580_;
}
v_resetjp_5580_:
{
lean_object* v___x_5583_; 
lean_inc(v_a_5569_);
lean_inc_ref(v_a_5568_);
lean_inc(v_a_5567_);
lean_inc_ref(v_a_5566_);
lean_inc(v_a_5565_);
lean_inc_ref(v_a_5564_);
lean_inc(v_a_5563_);
lean_inc_ref(v_a_5562_);
lean_inc(v_a_5561_);
lean_inc(v_a_5560_);
lean_inc_ref(v_b_5558_);
v___x_5583_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5558_, v_a_5559_, v_a_5560_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_);
if (lean_obj_tag(v___x_5583_) == 0)
{
lean_object* v_a_5584_; lean_object* v_fst_5585_; lean_object* v___x_5587_; uint8_t v_isShared_5588_; uint8_t v_isSharedCheck_5657_; 
v_a_5584_ = lean_ctor_get(v___x_5583_, 0);
lean_inc(v_a_5584_);
lean_dec_ref(v___x_5583_);
v_fst_5585_ = lean_ctor_get(v_a_5584_, 0);
v_isSharedCheck_5657_ = !lean_is_exclusive(v_a_5584_);
if (v_isSharedCheck_5657_ == 0)
{
lean_object* v_unused_5658_; 
v_unused_5658_ = lean_ctor_get(v_a_5584_, 1);
lean_dec(v_unused_5658_);
v___x_5587_ = v_a_5584_;
v_isShared_5588_ = v_isSharedCheck_5657_;
goto v_resetjp_5586_;
}
else
{
lean_inc(v_fst_5585_);
lean_dec(v_a_5584_);
v___x_5587_ = lean_box(0);
v_isShared_5588_ = v_isSharedCheck_5657_;
goto v_resetjp_5586_;
}
v_resetjp_5586_:
{
lean_object* v___x_5589_; 
v___x_5589_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5557_, v_a_5560_);
if (lean_obj_tag(v___x_5589_) == 0)
{
lean_object* v_a_5590_; uint8_t v___x_5591_; lean_object* v___x_5592_; 
v_a_5590_ = lean_ctor_get(v___x_5589_, 0);
lean_inc(v_a_5590_);
lean_dec_ref(v___x_5589_);
v___x_5591_ = 0;
lean_inc(v_a_5569_);
lean_inc_ref(v_a_5568_);
lean_inc(v_a_5567_);
lean_inc_ref(v_a_5566_);
lean_inc(v_a_5565_);
lean_inc_ref(v_a_5564_);
lean_inc(v_a_5563_);
lean_inc_ref(v_a_5562_);
lean_inc(v_a_5561_);
lean_inc(v_a_5560_);
lean_inc(v_structId_5576_);
v___x_5592_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5579_, v___x_5591_, v_a_5590_, v_structId_5576_, v_a_5560_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_);
if (lean_obj_tag(v___x_5592_) == 0)
{
lean_object* v_a_5593_; lean_object* v___x_5595_; uint8_t v_isShared_5596_; uint8_t v_isSharedCheck_5640_; 
v_a_5593_ = lean_ctor_get(v___x_5592_, 0);
v_isSharedCheck_5640_ = !lean_is_exclusive(v___x_5592_);
if (v_isSharedCheck_5640_ == 0)
{
v___x_5595_ = v___x_5592_;
v_isShared_5596_ = v_isSharedCheck_5640_;
goto v_resetjp_5594_;
}
else
{
lean_inc(v_a_5593_);
lean_dec(v___x_5592_);
v___x_5595_ = lean_box(0);
v_isShared_5596_ = v_isSharedCheck_5640_;
goto v_resetjp_5594_;
}
v_resetjp_5594_:
{
if (lean_obj_tag(v_a_5593_) == 1)
{
lean_object* v_val_5597_; lean_object* v___x_5598_; 
lean_del_object(v___x_5595_);
v_val_5597_ = lean_ctor_get(v_a_5593_, 0);
lean_inc(v_val_5597_);
lean_dec_ref(v_a_5593_);
v___x_5598_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5558_, v_a_5560_);
if (lean_obj_tag(v___x_5598_) == 0)
{
lean_object* v_a_5599_; lean_object* v___x_5600_; 
v_a_5599_ = lean_ctor_get(v___x_5598_, 0);
lean_inc(v_a_5599_);
lean_dec_ref(v___x_5598_);
lean_inc(v_a_5569_);
lean_inc_ref(v_a_5568_);
lean_inc(v_a_5567_);
lean_inc_ref(v_a_5566_);
lean_inc(v_a_5565_);
lean_inc_ref(v_a_5564_);
lean_inc(v_a_5563_);
lean_inc_ref(v_a_5562_);
lean_inc(v_a_5561_);
lean_inc(v_a_5560_);
lean_inc(v_structId_5576_);
v___x_5600_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5585_, v___x_5591_, v_a_5599_, v_structId_5576_, v_a_5560_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_);
if (lean_obj_tag(v___x_5600_) == 0)
{
lean_object* v_a_5601_; lean_object* v___x_5603_; uint8_t v_isShared_5604_; uint8_t v_isSharedCheck_5619_; 
v_a_5601_ = lean_ctor_get(v___x_5600_, 0);
v_isSharedCheck_5619_ = !lean_is_exclusive(v___x_5600_);
if (v_isSharedCheck_5619_ == 0)
{
v___x_5603_ = v___x_5600_;
v_isShared_5604_ = v_isSharedCheck_5619_;
goto v_resetjp_5602_;
}
else
{
lean_inc(v_a_5601_);
lean_dec(v___x_5600_);
v___x_5603_ = lean_box(0);
v_isShared_5604_ = v_isSharedCheck_5619_;
goto v_resetjp_5602_;
}
v_resetjp_5602_:
{
if (lean_obj_tag(v_a_5601_) == 1)
{
lean_object* v_val_5605_; lean_object* v___x_5607_; 
lean_del_object(v___x_5603_);
v_val_5605_ = lean_ctor_get(v_a_5601_, 0);
lean_inc(v_val_5605_);
lean_dec_ref(v_a_5601_);
lean_inc(v_val_5605_);
lean_inc(v_val_5597_);
if (v_isShared_5588_ == 0)
{
lean_ctor_set_tag(v___x_5587_, 3);
lean_ctor_set(v___x_5587_, 1, v_val_5605_);
lean_ctor_set(v___x_5587_, 0, v_val_5597_);
v___x_5607_ = v___x_5587_;
goto v_reusejp_5606_;
}
else
{
lean_object* v_reuseFailAlloc_5614_; 
v_reuseFailAlloc_5614_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5614_, 0, v_val_5597_);
lean_ctor_set(v_reuseFailAlloc_5614_, 1, v_val_5605_);
v___x_5607_ = v_reuseFailAlloc_5614_;
goto v_reusejp_5606_;
}
v_reusejp_5606_:
{
lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5611_; 
v___x_5608_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5607_);
v___x_5609_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5609_, 0, v_a_5557_);
lean_ctor_set(v___x_5609_, 1, v_b_5558_);
lean_ctor_set(v___x_5609_, 2, v_id_5575_);
lean_ctor_set(v___x_5609_, 3, v_val_5597_);
lean_ctor_set(v___x_5609_, 4, v_val_5605_);
if (v_isShared_5582_ == 0)
{
lean_ctor_set(v___x_5581_, 1, v___x_5609_);
lean_ctor_set(v___x_5581_, 0, v___x_5608_);
v___x_5611_ = v___x_5581_;
goto v_reusejp_5610_;
}
else
{
lean_object* v_reuseFailAlloc_5613_; 
v_reuseFailAlloc_5613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5613_, 0, v___x_5608_);
lean_ctor_set(v_reuseFailAlloc_5613_, 1, v___x_5609_);
v___x_5611_ = v_reuseFailAlloc_5613_;
goto v_reusejp_5610_;
}
v_reusejp_5610_:
{
lean_object* v___x_5612_; 
v___x_5612_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5611_, v_structId_5576_, v_a_5560_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_);
return v___x_5612_;
}
}
}
else
{
lean_object* v___x_5615_; lean_object* v___x_5617_; 
lean_dec(v_a_5601_);
lean_dec(v_val_5597_);
lean_del_object(v___x_5587_);
lean_del_object(v___x_5581_);
lean_dec(v_structId_5576_);
lean_dec(v_id_5575_);
lean_dec(v_a_5569_);
lean_dec_ref(v_a_5568_);
lean_dec(v_a_5567_);
lean_dec_ref(v_a_5566_);
lean_dec(v_a_5565_);
lean_dec_ref(v_a_5564_);
lean_dec(v_a_5563_);
lean_dec_ref(v_a_5562_);
lean_dec(v_a_5561_);
lean_dec(v_a_5560_);
lean_dec_ref(v_b_5558_);
lean_dec_ref(v_a_5557_);
v___x_5615_ = lean_box(0);
if (v_isShared_5604_ == 0)
{
lean_ctor_set(v___x_5603_, 0, v___x_5615_);
v___x_5617_ = v___x_5603_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5618_; 
v_reuseFailAlloc_5618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5618_, 0, v___x_5615_);
v___x_5617_ = v_reuseFailAlloc_5618_;
goto v_reusejp_5616_;
}
v_reusejp_5616_:
{
return v___x_5617_;
}
}
}
}
else
{
lean_object* v_a_5620_; lean_object* v___x_5622_; uint8_t v_isShared_5623_; uint8_t v_isSharedCheck_5627_; 
lean_dec(v_val_5597_);
lean_del_object(v___x_5587_);
lean_del_object(v___x_5581_);
lean_dec(v_structId_5576_);
lean_dec(v_id_5575_);
lean_dec(v_a_5569_);
lean_dec_ref(v_a_5568_);
lean_dec(v_a_5567_);
lean_dec_ref(v_a_5566_);
lean_dec(v_a_5565_);
lean_dec_ref(v_a_5564_);
lean_dec(v_a_5563_);
lean_dec_ref(v_a_5562_);
lean_dec(v_a_5561_);
lean_dec(v_a_5560_);
lean_dec_ref(v_b_5558_);
lean_dec_ref(v_a_5557_);
v_a_5620_ = lean_ctor_get(v___x_5600_, 0);
v_isSharedCheck_5627_ = !lean_is_exclusive(v___x_5600_);
if (v_isSharedCheck_5627_ == 0)
{
v___x_5622_ = v___x_5600_;
v_isShared_5623_ = v_isSharedCheck_5627_;
goto v_resetjp_5621_;
}
else
{
lean_inc(v_a_5620_);
lean_dec(v___x_5600_);
v___x_5622_ = lean_box(0);
v_isShared_5623_ = v_isSharedCheck_5627_;
goto v_resetjp_5621_;
}
v_resetjp_5621_:
{
lean_object* v___x_5625_; 
if (v_isShared_5623_ == 0)
{
v___x_5625_ = v___x_5622_;
goto v_reusejp_5624_;
}
else
{
lean_object* v_reuseFailAlloc_5626_; 
v_reuseFailAlloc_5626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5626_, 0, v_a_5620_);
v___x_5625_ = v_reuseFailAlloc_5626_;
goto v_reusejp_5624_;
}
v_reusejp_5624_:
{
return v___x_5625_;
}
}
}
}
else
{
lean_object* v_a_5628_; lean_object* v___x_5630_; uint8_t v_isShared_5631_; uint8_t v_isSharedCheck_5635_; 
lean_dec(v_val_5597_);
lean_del_object(v___x_5587_);
lean_dec(v_fst_5585_);
lean_del_object(v___x_5581_);
lean_dec(v_structId_5576_);
lean_dec(v_id_5575_);
lean_dec(v_a_5569_);
lean_dec_ref(v_a_5568_);
lean_dec(v_a_5567_);
lean_dec_ref(v_a_5566_);
lean_dec(v_a_5565_);
lean_dec_ref(v_a_5564_);
lean_dec(v_a_5563_);
lean_dec_ref(v_a_5562_);
lean_dec(v_a_5561_);
lean_dec(v_a_5560_);
lean_dec_ref(v_b_5558_);
lean_dec_ref(v_a_5557_);
v_a_5628_ = lean_ctor_get(v___x_5598_, 0);
v_isSharedCheck_5635_ = !lean_is_exclusive(v___x_5598_);
if (v_isSharedCheck_5635_ == 0)
{
v___x_5630_ = v___x_5598_;
v_isShared_5631_ = v_isSharedCheck_5635_;
goto v_resetjp_5629_;
}
else
{
lean_inc(v_a_5628_);
lean_dec(v___x_5598_);
v___x_5630_ = lean_box(0);
v_isShared_5631_ = v_isSharedCheck_5635_;
goto v_resetjp_5629_;
}
v_resetjp_5629_:
{
lean_object* v___x_5633_; 
if (v_isShared_5631_ == 0)
{
v___x_5633_ = v___x_5630_;
goto v_reusejp_5632_;
}
else
{
lean_object* v_reuseFailAlloc_5634_; 
v_reuseFailAlloc_5634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5634_, 0, v_a_5628_);
v___x_5633_ = v_reuseFailAlloc_5634_;
goto v_reusejp_5632_;
}
v_reusejp_5632_:
{
return v___x_5633_;
}
}
}
}
else
{
lean_object* v___x_5636_; lean_object* v___x_5638_; 
lean_dec(v_a_5593_);
lean_del_object(v___x_5587_);
lean_dec(v_fst_5585_);
lean_del_object(v___x_5581_);
lean_dec(v_structId_5576_);
lean_dec(v_id_5575_);
lean_dec(v_a_5569_);
lean_dec_ref(v_a_5568_);
lean_dec(v_a_5567_);
lean_dec_ref(v_a_5566_);
lean_dec(v_a_5565_);
lean_dec_ref(v_a_5564_);
lean_dec(v_a_5563_);
lean_dec_ref(v_a_5562_);
lean_dec(v_a_5561_);
lean_dec(v_a_5560_);
lean_dec_ref(v_b_5558_);
lean_dec_ref(v_a_5557_);
v___x_5636_ = lean_box(0);
if (v_isShared_5596_ == 0)
{
lean_ctor_set(v___x_5595_, 0, v___x_5636_);
v___x_5638_ = v___x_5595_;
goto v_reusejp_5637_;
}
else
{
lean_object* v_reuseFailAlloc_5639_; 
v_reuseFailAlloc_5639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5639_, 0, v___x_5636_);
v___x_5638_ = v_reuseFailAlloc_5639_;
goto v_reusejp_5637_;
}
v_reusejp_5637_:
{
return v___x_5638_;
}
}
}
}
else
{
lean_object* v_a_5641_; lean_object* v___x_5643_; uint8_t v_isShared_5644_; uint8_t v_isSharedCheck_5648_; 
lean_del_object(v___x_5587_);
lean_dec(v_fst_5585_);
lean_del_object(v___x_5581_);
lean_dec(v_structId_5576_);
lean_dec(v_id_5575_);
lean_dec(v_a_5569_);
lean_dec_ref(v_a_5568_);
lean_dec(v_a_5567_);
lean_dec_ref(v_a_5566_);
lean_dec(v_a_5565_);
lean_dec_ref(v_a_5564_);
lean_dec(v_a_5563_);
lean_dec_ref(v_a_5562_);
lean_dec(v_a_5561_);
lean_dec(v_a_5560_);
lean_dec_ref(v_b_5558_);
lean_dec_ref(v_a_5557_);
v_a_5641_ = lean_ctor_get(v___x_5592_, 0);
v_isSharedCheck_5648_ = !lean_is_exclusive(v___x_5592_);
if (v_isSharedCheck_5648_ == 0)
{
v___x_5643_ = v___x_5592_;
v_isShared_5644_ = v_isSharedCheck_5648_;
goto v_resetjp_5642_;
}
else
{
lean_inc(v_a_5641_);
lean_dec(v___x_5592_);
v___x_5643_ = lean_box(0);
v_isShared_5644_ = v_isSharedCheck_5648_;
goto v_resetjp_5642_;
}
v_resetjp_5642_:
{
lean_object* v___x_5646_; 
if (v_isShared_5644_ == 0)
{
v___x_5646_ = v___x_5643_;
goto v_reusejp_5645_;
}
else
{
lean_object* v_reuseFailAlloc_5647_; 
v_reuseFailAlloc_5647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5647_, 0, v_a_5641_);
v___x_5646_ = v_reuseFailAlloc_5647_;
goto v_reusejp_5645_;
}
v_reusejp_5645_:
{
return v___x_5646_;
}
}
}
}
else
{
lean_object* v_a_5649_; lean_object* v___x_5651_; uint8_t v_isShared_5652_; uint8_t v_isSharedCheck_5656_; 
lean_del_object(v___x_5587_);
lean_dec(v_fst_5585_);
lean_del_object(v___x_5581_);
lean_dec(v_fst_5579_);
lean_dec(v_structId_5576_);
lean_dec(v_id_5575_);
lean_dec(v_a_5569_);
lean_dec_ref(v_a_5568_);
lean_dec(v_a_5567_);
lean_dec_ref(v_a_5566_);
lean_dec(v_a_5565_);
lean_dec_ref(v_a_5564_);
lean_dec(v_a_5563_);
lean_dec_ref(v_a_5562_);
lean_dec(v_a_5561_);
lean_dec(v_a_5560_);
lean_dec_ref(v_b_5558_);
lean_dec_ref(v_a_5557_);
v_a_5649_ = lean_ctor_get(v___x_5589_, 0);
v_isSharedCheck_5656_ = !lean_is_exclusive(v___x_5589_);
if (v_isSharedCheck_5656_ == 0)
{
v___x_5651_ = v___x_5589_;
v_isShared_5652_ = v_isSharedCheck_5656_;
goto v_resetjp_5650_;
}
else
{
lean_inc(v_a_5649_);
lean_dec(v___x_5589_);
v___x_5651_ = lean_box(0);
v_isShared_5652_ = v_isSharedCheck_5656_;
goto v_resetjp_5650_;
}
v_resetjp_5650_:
{
lean_object* v___x_5654_; 
if (v_isShared_5652_ == 0)
{
v___x_5654_ = v___x_5651_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5655_; 
v_reuseFailAlloc_5655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5655_, 0, v_a_5649_);
v___x_5654_ = v_reuseFailAlloc_5655_;
goto v_reusejp_5653_;
}
v_reusejp_5653_:
{
return v___x_5654_;
}
}
}
}
}
else
{
lean_object* v_a_5659_; lean_object* v___x_5661_; uint8_t v_isShared_5662_; uint8_t v_isSharedCheck_5666_; 
lean_del_object(v___x_5581_);
lean_dec(v_fst_5579_);
lean_dec(v_structId_5576_);
lean_dec(v_id_5575_);
lean_dec(v_a_5569_);
lean_dec_ref(v_a_5568_);
lean_dec(v_a_5567_);
lean_dec_ref(v_a_5566_);
lean_dec(v_a_5565_);
lean_dec_ref(v_a_5564_);
lean_dec(v_a_5563_);
lean_dec_ref(v_a_5562_);
lean_dec(v_a_5561_);
lean_dec(v_a_5560_);
lean_dec_ref(v_b_5558_);
lean_dec_ref(v_a_5557_);
v_a_5659_ = lean_ctor_get(v___x_5583_, 0);
v_isSharedCheck_5666_ = !lean_is_exclusive(v___x_5583_);
if (v_isSharedCheck_5666_ == 0)
{
v___x_5661_ = v___x_5583_;
v_isShared_5662_ = v_isSharedCheck_5666_;
goto v_resetjp_5660_;
}
else
{
lean_inc(v_a_5659_);
lean_dec(v___x_5583_);
v___x_5661_ = lean_box(0);
v_isShared_5662_ = v_isSharedCheck_5666_;
goto v_resetjp_5660_;
}
v_resetjp_5660_:
{
lean_object* v___x_5664_; 
if (v_isShared_5662_ == 0)
{
v___x_5664_ = v___x_5661_;
goto v_reusejp_5663_;
}
else
{
lean_object* v_reuseFailAlloc_5665_; 
v_reuseFailAlloc_5665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5665_, 0, v_a_5659_);
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
}
else
{
lean_object* v_a_5669_; lean_object* v___x_5671_; uint8_t v_isShared_5672_; uint8_t v_isSharedCheck_5676_; 
lean_dec(v_structId_5576_);
lean_dec(v_id_5575_);
lean_dec(v_a_5569_);
lean_dec_ref(v_a_5568_);
lean_dec(v_a_5567_);
lean_dec_ref(v_a_5566_);
lean_dec(v_a_5565_);
lean_dec_ref(v_a_5564_);
lean_dec(v_a_5563_);
lean_dec_ref(v_a_5562_);
lean_dec(v_a_5561_);
lean_dec(v_a_5560_);
lean_dec(v_a_5559_);
lean_dec_ref(v_b_5558_);
lean_dec_ref(v_a_5557_);
v_a_5669_ = lean_ctor_get(v___x_5577_, 0);
v_isSharedCheck_5676_ = !lean_is_exclusive(v___x_5577_);
if (v_isSharedCheck_5676_ == 0)
{
v___x_5671_ = v___x_5577_;
v_isShared_5672_ = v_isSharedCheck_5676_;
goto v_resetjp_5670_;
}
else
{
lean_inc(v_a_5669_);
lean_dec(v___x_5577_);
v___x_5671_ = lean_box(0);
v_isShared_5672_ = v_isSharedCheck_5676_;
goto v_resetjp_5670_;
}
v_resetjp_5670_:
{
lean_object* v___x_5674_; 
if (v_isShared_5672_ == 0)
{
v___x_5674_ = v___x_5671_;
goto v_reusejp_5673_;
}
else
{
lean_object* v_reuseFailAlloc_5675_; 
v_reuseFailAlloc_5675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_a_5669_);
v___x_5674_ = v_reuseFailAlloc_5675_;
goto v_reusejp_5673_;
}
v_reusejp_5673_:
{
return v___x_5674_;
}
}
}
}
}
else
{
lean_object* v_a_5677_; lean_object* v___x_5679_; uint8_t v_isShared_5680_; uint8_t v_isSharedCheck_5684_; 
lean_dec(v_a_5569_);
lean_dec_ref(v_a_5568_);
lean_dec(v_a_5567_);
lean_dec_ref(v_a_5566_);
lean_dec(v_a_5565_);
lean_dec_ref(v_a_5564_);
lean_dec(v_a_5563_);
lean_dec_ref(v_a_5562_);
lean_dec(v_a_5561_);
lean_dec(v_a_5560_);
lean_dec(v_a_5559_);
lean_dec_ref(v_b_5558_);
lean_dec_ref(v_a_5557_);
v_a_5677_ = lean_ctor_get(v___x_5571_, 0);
v_isSharedCheck_5684_ = !lean_is_exclusive(v___x_5571_);
if (v_isSharedCheck_5684_ == 0)
{
v___x_5679_ = v___x_5571_;
v_isShared_5680_ = v_isSharedCheck_5684_;
goto v_resetjp_5678_;
}
else
{
lean_inc(v_a_5677_);
lean_dec(v___x_5571_);
v___x_5679_ = lean_box(0);
v_isShared_5680_ = v_isSharedCheck_5684_;
goto v_resetjp_5678_;
}
v_resetjp_5678_:
{
lean_object* v___x_5682_; 
if (v_isShared_5680_ == 0)
{
v___x_5682_ = v___x_5679_;
goto v_reusejp_5681_;
}
else
{
lean_object* v_reuseFailAlloc_5683_; 
v_reuseFailAlloc_5683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5683_, 0, v_a_5677_);
v___x_5682_ = v_reuseFailAlloc_5683_;
goto v_reusejp_5681_;
}
v_reusejp_5681_:
{
return v___x_5682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq___boxed(lean_object* v_a_5685_, lean_object* v_b_5686_, lean_object* v_a_5687_, lean_object* v_a_5688_, lean_object* v_a_5689_, lean_object* v_a_5690_, lean_object* v_a_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_){
_start:
{
lean_object* v_res_5699_; 
v_res_5699_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5685_, v_b_5686_, v_a_5687_, v_a_5688_, v_a_5689_, v_a_5690_, v_a_5691_, v_a_5692_, v_a_5693_, v_a_5694_, v_a_5695_, v_a_5696_, v_a_5697_);
return v_res_5699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(lean_object* v_a_5700_, lean_object* v_b_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_, lean_object* v_a_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_){
_start:
{
lean_object* v___x_5713_; 
v___x_5713_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5700_, v_b_5701_, v_a_5702_, v_a_5710_);
if (lean_obj_tag(v___x_5713_) == 0)
{
lean_object* v_a_5714_; 
v_a_5714_ = lean_ctor_get(v___x_5713_, 0);
lean_inc(v_a_5714_);
lean_dec_ref(v___x_5713_);
if (lean_obj_tag(v_a_5714_) == 1)
{
lean_object* v_val_5715_; lean_object* v___x_5716_; 
v_val_5715_ = lean_ctor_get(v_a_5714_, 0);
lean_inc(v_val_5715_);
lean_dec_ref(v_a_5714_);
v___x_5716_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5715_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_, v_a_5711_);
if (lean_obj_tag(v___x_5716_) == 0)
{
lean_object* v_a_5717_; uint8_t v___x_5718_; 
v_a_5717_ = lean_ctor_get(v___x_5716_, 0);
lean_inc(v_a_5717_);
lean_dec_ref(v___x_5716_);
v___x_5718_ = lean_unbox(v_a_5717_);
lean_dec(v_a_5717_);
if (v___x_5718_ == 0)
{
lean_object* v___x_5719_; 
v___x_5719_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5700_, v_b_5701_, v_val_5715_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_, v_a_5711_);
return v___x_5719_;
}
else
{
lean_object* v___x_5720_; 
v___x_5720_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5700_, v_b_5701_, v_val_5715_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_, v_a_5711_);
return v___x_5720_;
}
}
else
{
lean_object* v_a_5721_; lean_object* v___x_5723_; uint8_t v_isShared_5724_; uint8_t v_isSharedCheck_5728_; 
lean_dec(v_val_5715_);
lean_dec(v_a_5711_);
lean_dec_ref(v_a_5710_);
lean_dec(v_a_5709_);
lean_dec_ref(v_a_5708_);
lean_dec(v_a_5707_);
lean_dec_ref(v_a_5706_);
lean_dec(v_a_5705_);
lean_dec_ref(v_a_5704_);
lean_dec(v_a_5703_);
lean_dec(v_a_5702_);
lean_dec_ref(v_b_5701_);
lean_dec_ref(v_a_5700_);
v_a_5721_ = lean_ctor_get(v___x_5716_, 0);
v_isSharedCheck_5728_ = !lean_is_exclusive(v___x_5716_);
if (v_isSharedCheck_5728_ == 0)
{
v___x_5723_ = v___x_5716_;
v_isShared_5724_ = v_isSharedCheck_5728_;
goto v_resetjp_5722_;
}
else
{
lean_inc(v_a_5721_);
lean_dec(v___x_5716_);
v___x_5723_ = lean_box(0);
v_isShared_5724_ = v_isSharedCheck_5728_;
goto v_resetjp_5722_;
}
v_resetjp_5722_:
{
lean_object* v___x_5726_; 
if (v_isShared_5724_ == 0)
{
v___x_5726_ = v___x_5723_;
goto v_reusejp_5725_;
}
else
{
lean_object* v_reuseFailAlloc_5727_; 
v_reuseFailAlloc_5727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5727_, 0, v_a_5721_);
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
lean_object* v___x_5729_; 
lean_dec(v_a_5714_);
v___x_5729_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5700_, v_b_5701_, v_a_5702_, v_a_5710_);
if (lean_obj_tag(v___x_5729_) == 0)
{
lean_object* v_a_5730_; lean_object* v___x_5732_; uint8_t v_isShared_5733_; uint8_t v_isSharedCheck_5740_; 
v_a_5730_ = lean_ctor_get(v___x_5729_, 0);
v_isSharedCheck_5740_ = !lean_is_exclusive(v___x_5729_);
if (v_isSharedCheck_5740_ == 0)
{
v___x_5732_ = v___x_5729_;
v_isShared_5733_ = v_isSharedCheck_5740_;
goto v_resetjp_5731_;
}
else
{
lean_inc(v_a_5730_);
lean_dec(v___x_5729_);
v___x_5732_ = lean_box(0);
v_isShared_5733_ = v_isSharedCheck_5740_;
goto v_resetjp_5731_;
}
v_resetjp_5731_:
{
if (lean_obj_tag(v_a_5730_) == 1)
{
lean_object* v_val_5734_; lean_object* v___x_5735_; 
lean_del_object(v___x_5732_);
v_val_5734_ = lean_ctor_get(v_a_5730_, 0);
lean_inc(v_val_5734_);
lean_dec_ref(v_a_5730_);
v___x_5735_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5700_, v_b_5701_, v_val_5734_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_, v_a_5711_);
return v___x_5735_;
}
else
{
lean_object* v___x_5736_; lean_object* v___x_5738_; 
lean_dec(v_a_5730_);
lean_dec(v_a_5711_);
lean_dec_ref(v_a_5710_);
lean_dec(v_a_5709_);
lean_dec_ref(v_a_5708_);
lean_dec(v_a_5707_);
lean_dec_ref(v_a_5706_);
lean_dec(v_a_5705_);
lean_dec_ref(v_a_5704_);
lean_dec(v_a_5703_);
lean_dec(v_a_5702_);
lean_dec_ref(v_b_5701_);
lean_dec_ref(v_a_5700_);
v___x_5736_ = lean_box(0);
if (v_isShared_5733_ == 0)
{
lean_ctor_set(v___x_5732_, 0, v___x_5736_);
v___x_5738_ = v___x_5732_;
goto v_reusejp_5737_;
}
else
{
lean_object* v_reuseFailAlloc_5739_; 
v_reuseFailAlloc_5739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5739_, 0, v___x_5736_);
v___x_5738_ = v_reuseFailAlloc_5739_;
goto v_reusejp_5737_;
}
v_reusejp_5737_:
{
return v___x_5738_;
}
}
}
}
else
{
lean_object* v_a_5741_; lean_object* v___x_5743_; uint8_t v_isShared_5744_; uint8_t v_isSharedCheck_5748_; 
lean_dec(v_a_5711_);
lean_dec_ref(v_a_5710_);
lean_dec(v_a_5709_);
lean_dec_ref(v_a_5708_);
lean_dec(v_a_5707_);
lean_dec_ref(v_a_5706_);
lean_dec(v_a_5705_);
lean_dec_ref(v_a_5704_);
lean_dec(v_a_5703_);
lean_dec(v_a_5702_);
lean_dec_ref(v_b_5701_);
lean_dec_ref(v_a_5700_);
v_a_5741_ = lean_ctor_get(v___x_5729_, 0);
v_isSharedCheck_5748_ = !lean_is_exclusive(v___x_5729_);
if (v_isSharedCheck_5748_ == 0)
{
v___x_5743_ = v___x_5729_;
v_isShared_5744_ = v_isSharedCheck_5748_;
goto v_resetjp_5742_;
}
else
{
lean_inc(v_a_5741_);
lean_dec(v___x_5729_);
v___x_5743_ = lean_box(0);
v_isShared_5744_ = v_isSharedCheck_5748_;
goto v_resetjp_5742_;
}
v_resetjp_5742_:
{
lean_object* v___x_5746_; 
if (v_isShared_5744_ == 0)
{
v___x_5746_ = v___x_5743_;
goto v_reusejp_5745_;
}
else
{
lean_object* v_reuseFailAlloc_5747_; 
v_reuseFailAlloc_5747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5747_, 0, v_a_5741_);
v___x_5746_ = v_reuseFailAlloc_5747_;
goto v_reusejp_5745_;
}
v_reusejp_5745_:
{
return v___x_5746_;
}
}
}
}
}
else
{
lean_object* v_a_5749_; lean_object* v___x_5751_; uint8_t v_isShared_5752_; uint8_t v_isSharedCheck_5756_; 
lean_dec(v_a_5711_);
lean_dec_ref(v_a_5710_);
lean_dec(v_a_5709_);
lean_dec_ref(v_a_5708_);
lean_dec(v_a_5707_);
lean_dec_ref(v_a_5706_);
lean_dec(v_a_5705_);
lean_dec_ref(v_a_5704_);
lean_dec(v_a_5703_);
lean_dec(v_a_5702_);
lean_dec_ref(v_b_5701_);
lean_dec_ref(v_a_5700_);
v_a_5749_ = lean_ctor_get(v___x_5713_, 0);
v_isSharedCheck_5756_ = !lean_is_exclusive(v___x_5713_);
if (v_isSharedCheck_5756_ == 0)
{
v___x_5751_ = v___x_5713_;
v_isShared_5752_ = v_isSharedCheck_5756_;
goto v_resetjp_5750_;
}
else
{
lean_inc(v_a_5749_);
lean_dec(v___x_5713_);
v___x_5751_ = lean_box(0);
v_isShared_5752_ = v_isSharedCheck_5756_;
goto v_resetjp_5750_;
}
v_resetjp_5750_:
{
lean_object* v___x_5754_; 
if (v_isShared_5752_ == 0)
{
v___x_5754_ = v___x_5751_;
goto v_reusejp_5753_;
}
else
{
lean_object* v_reuseFailAlloc_5755_; 
v_reuseFailAlloc_5755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5755_, 0, v_a_5749_);
v___x_5754_ = v_reuseFailAlloc_5755_;
goto v_reusejp_5753_;
}
v_reusejp_5753_:
{
return v___x_5754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed(lean_object* v_a_5757_, lean_object* v_b_5758_, lean_object* v_a_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_, lean_object* v_a_5762_, lean_object* v_a_5763_, lean_object* v_a_5764_, lean_object* v_a_5765_, lean_object* v_a_5766_, lean_object* v_a_5767_, lean_object* v_a_5768_, lean_object* v_a_5769_){
_start:
{
lean_object* v_res_5770_; 
v_res_5770_ = l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(v_a_5757_, v_b_5758_, v_a_5759_, v_a_5760_, v_a_5761_, v_a_5762_, v_a_5763_, v_a_5764_, v_a_5765_, v_a_5766_, v_a_5767_, v_a_5768_);
return v_res_5770_;
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
