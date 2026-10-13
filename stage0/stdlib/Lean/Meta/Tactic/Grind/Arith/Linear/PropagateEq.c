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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Grind_Linarith_Poly_coeff(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default___redArg();
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_updateOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Expr_toPoly(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_toIntModuleExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs(lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_div(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateImpEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__3_value),LEAN_SCALAR_PTR_LITERAL(206, 233, 164, 186, 216, 210, 242, 163)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2;
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "unsat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 205, 246, 167, 183, 132, 208, 174)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "store"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 36, 82, 219, 127, 154, 201, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__3_value),LEAN_SCALAR_PTR_LITERAL(108, 151, 24, 43, 11, 190, 144, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 36, 82, 219, 127, 154, 201, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__1_value),LEAN_SCALAR_PTR_LITERAL(96, 234, 54, 186, 23, 232, 175, 83)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2;
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0(lean_object* v_k_3_, lean_object* v_x_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_17_ = l_Lean_instInhabitedExpr;
v___x_18_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_19_ = lean_int_dec_eq(v_k_3_, v___x_18_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v_a_21_; lean_object* v___x_22_; 
v_a_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_a_21_);
lean_dec_ref_known(v___x_20_, 1);
v___x_22_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_);
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_40_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_40_ == 0)
{
v___x_25_ = v___x_22_;
v_isShared_26_ = v_isSharedCheck_40_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v___x_22_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_40_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v_vars_27_; lean_object* v_zsmulFn_28_; lean_object* v_size_29_; lean_object* v___x_30_; lean_object* v___y_32_; uint8_t v___x_37_; 
v_vars_27_ = lean_ctor_get(v_a_23_, 30);
lean_inc_ref(v_vars_27_);
lean_dec(v_a_23_);
v_zsmulFn_28_ = lean_ctor_get(v_a_21_, 23);
lean_inc_ref(v_zsmulFn_28_);
lean_dec(v_a_21_);
v_size_29_ = lean_ctor_get(v_vars_27_, 2);
v___x_30_ = l_Lean_mkIntLit(v_k_3_);
v___x_37_ = lean_nat_dec_lt(v_x_4_, v_size_29_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; 
lean_dec_ref(v_vars_27_);
v___x_38_ = l_outOfBounds___redArg(v___x_17_);
v___y_32_ = v___x_38_;
goto v___jp_31_;
}
else
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_PersistentArray_get_x21___redArg(v___x_17_, v_vars_27_, v_x_4_);
lean_dec_ref(v_vars_27_);
v___y_32_ = v___x_39_;
goto v___jp_31_;
}
v___jp_31_:
{
lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_33_ = l_Lean_mkAppB(v_zsmulFn_28_, v___x_30_, v___y_32_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 0, v___x_33_);
v___x_35_ = v___x_25_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_33_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
else
{
lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_48_; 
lean_dec(v_a_21_);
v_a_41_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_48_ == 0)
{
v___x_43_ = v___x_22_;
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_dec(v___x_22_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_46_; 
if (v_isShared_44_ == 0)
{
v___x_46_ = v___x_43_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_a_41_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
else
{
lean_object* v_a_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_56_; 
v_a_49_ = lean_ctor_get(v___x_20_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_56_ == 0)
{
v___x_51_ = v___x_20_;
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_a_49_);
lean_dec(v___x_20_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_54_; 
if (v_isShared_52_ == 0)
{
v___x_54_ = v___x_51_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_a_49_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
else
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_73_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_73_ == 0)
{
v___x_60_ = v___x_57_;
v_isShared_61_ = v_isSharedCheck_73_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_57_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_73_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v_vars_62_; lean_object* v_size_63_; uint8_t v___x_64_; 
v_vars_62_ = lean_ctor_get(v_a_58_, 30);
lean_inc_ref(v_vars_62_);
lean_dec(v_a_58_);
v_size_63_ = lean_ctor_get(v_vars_62_, 2);
v___x_64_ = lean_nat_dec_lt(v_x_4_, v_size_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_67_; 
lean_dec_ref(v_vars_62_);
v___x_65_ = l_outOfBounds___redArg(v___x_17_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v___x_65_);
v___x_67_ = v___x_60_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_65_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
else
{
lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_69_ = l_Lean_PersistentArray_get_x21___redArg(v___x_17_, v_vars_62_, v_x_4_);
lean_dec_ref(v_vars_62_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v___x_69_);
v___x_71_ = v___x_60_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_69_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
}
else
{
lean_object* v_a_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_81_; 
v_a_74_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_81_ == 0)
{
v___x_76_ = v___x_57_;
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_a_74_);
lean_dec(v___x_57_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_79_; 
if (v_isShared_77_ == 0)
{
v___x_79_ = v___x_76_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_a_74_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___boxed(lean_object* v_k_82_, lean_object* v_x_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0(v_k_82_, v_x_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec(v___y_85_);
lean_dec(v___y_84_);
lean_dec(v_x_83_);
lean_dec(v_k_82_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__1(lean_object* v_p_97_, lean_object* v_acc_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
if (lean_obj_tag(v_p_97_) == 0)
{
lean_object* v___x_111_; 
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v_acc_98_);
return v___x_111_;
}
else
{
lean_object* v_k_112_; lean_object* v_v_113_; lean_object* v_p_114_; lean_object* v___x_115_; 
v_k_112_ = lean_ctor_get(v_p_97_, 0);
v_v_113_ = lean_ctor_get(v_p_97_, 1);
v_p_114_ = lean_ctor_get(v_p_97_, 2);
v___x_115_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_117_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_a_116_);
lean_dec_ref_known(v___x_115_, 1);
v___x_117_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0(v_k_112_, v_v_113_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; lean_object* v_addFn_119_; lean_object* v___x_120_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_a_118_);
lean_dec_ref_known(v___x_117_, 1);
v_addFn_119_ = lean_ctor_get(v_a_116_, 22);
lean_inc_ref(v_addFn_119_);
lean_dec(v_a_116_);
v___x_120_ = l_Lean_mkAppB(v_addFn_119_, v_acc_98_, v_a_118_);
v_p_97_ = v_p_114_;
v_acc_98_ = v___x_120_;
goto _start;
}
else
{
lean_dec(v_a_116_);
lean_dec_ref(v_acc_98_);
return v___x_117_;
}
}
else
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
lean_dec_ref(v_acc_98_);
v_a_122_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___x_115_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_115_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__1___boxed(lean_object* v_p_130_, lean_object* v_acc_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__1(v_p_130_, v_acc_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec(v___y_133_);
lean_dec(v___y_132_);
lean_dec(v_p_130_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(lean_object* v_p_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
if (lean_obj_tag(v_p_145_) == 0)
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_167_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_167_ == 0)
{
v___x_161_ = v___x_158_;
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v_zero_163_; lean_object* v___x_165_; 
v_zero_163_ = lean_ctor_get(v_a_159_, 17);
lean_inc_ref(v_zero_163_);
lean_dec(v_a_159_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v_zero_163_);
v___x_165_ = v___x_161_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_zero_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
v_a_168_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_175_ == 0)
{
v___x_170_ = v___x_158_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_158_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
else
{
lean_object* v_k_176_; lean_object* v_v_177_; lean_object* v_p_178_; lean_object* v___x_179_; 
v_k_176_ = lean_ctor_get(v_p_145_, 0);
v_v_177_ = lean_ctor_get(v_p_145_, 1);
v_p_178_ = lean_ctor_get(v_p_145_, 2);
v___x_179_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0(v_k_176_, v_v_177_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_181_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_179_, 1);
v___x_181_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__1(v_p_178_, v_a_180_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
return v___x_181_;
}
else
{
return v___x_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___boxed(lean_object* v_p_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec(v___y_184_);
lean_dec(v___y_183_);
lean_dec(v_p_182_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3(lean_object* v_a_199_, lean_object* v_b_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_229_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_229_ == 0)
{
v___x_216_ = v___x_213_;
v_isShared_217_ = v_isSharedCheck_229_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_213_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_229_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v_type_218_; lean_object* v_u_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
v_type_218_ = lean_ctor_get(v_a_214_, 2);
lean_inc_ref(v_type_218_);
v_u_219_ = lean_ctor_get(v_a_214_, 3);
lean_inc(v_u_219_);
lean_dec(v_a_214_);
v___x_220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3___closed__1));
v___x_221_ = l_Lean_Level_succ___override(v_u_219_);
v___x_222_ = lean_box(0);
v___x_223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = l_Lean_mkConst(v___x_220_, v___x_223_);
v___x_225_ = l_Lean_mkApp3(v___x_224_, v_type_218_, v_a_199_, v_b_200_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_225_);
v___x_227_ = v___x_216_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
lean_dec_ref(v_b_200_);
lean_dec_ref(v_a_199_);
v_a_230_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_213_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_213_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3___boxed(lean_object* v_a_238_, lean_object* v_b_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3(v_a_238_, v_b_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec(v___y_241_);
lean_dec(v___y_240_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(lean_object* v_c_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_p_266_; lean_object* v___x_267_; 
v_p_266_ = lean_ctor_get(v_c_253_, 0);
v___x_267_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_266_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_269_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
lean_dec_ref_known(v___x_267_, 1);
v___x_269_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v_ofNatZero_271_; lean_object* v___x_272_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_a_270_);
lean_dec_ref_known(v___x_269_, 1);
v_ofNatZero_271_ = lean_ctor_get(v_a_270_, 18);
lean_inc_ref(v_ofNatZero_271_);
lean_dec(v_a_270_);
v___x_272_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3(v_a_268_, v_ofNatZero_271_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
return v___x_272_;
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_dec(v_a_268_);
v_a_273_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_269_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_269_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
else
{
return v___x_267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1___boxed(lean_object* v_c_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v_c_281_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(lean_object* v_msgData_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; lean_object* v_env_302_; uint8_t v___x_303_; lean_object* v_env_304_; lean_object* v___x_305_; lean_object* v_toCold_306_; lean_object* v_mctx_307_; lean_object* v_lctx_308_; lean_object* v_options_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_301_ = lean_st_ref_get(v___y_299_);
v_env_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc_ref(v_env_302_);
lean_dec(v___x_301_);
v___x_303_ = 0;
v_env_304_ = l_Lean_Environment_setRecordingDeps(v_env_302_, v___x_303_);
v___x_305_ = lean_st_ref_get(v___y_297_);
v_toCold_306_ = lean_ctor_get(v___y_298_, 0);
v_mctx_307_ = lean_ctor_get(v___x_305_, 0);
lean_inc_ref(v_mctx_307_);
lean_dec(v___x_305_);
v_lctx_308_ = lean_ctor_get(v___y_296_, 2);
v_options_309_ = lean_ctor_get(v_toCold_306_, 2);
lean_inc_ref(v_options_309_);
lean_inc_ref(v_lctx_308_);
v___x_310_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_310_, 0, v_env_304_);
lean_ctor_set(v___x_310_, 1, v_mctx_307_);
lean_ctor_set(v___x_310_, 2, v_lctx_308_);
lean_ctor_set(v___x_310_, 3, v_options_309_);
v___x_311_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v_msgData_295_);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5___boxed(lean_object* v_msgData_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msgData_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_319_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_320_; double v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = lean_float_of_nat(v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(lean_object* v_cls_325_, lean_object* v_msg_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_ref_332_; lean_object* v___x_333_; lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_379_; 
v_ref_332_ = lean_ctor_get(v___y_329_, 2);
v___x_333_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msg_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
v_a_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_379_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_379_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_379_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v_traceState_339_; lean_object* v_env_340_; lean_object* v_nextMacroScope_341_; lean_object* v_ngen_342_; lean_object* v_auxDeclNGen_343_; lean_object* v_cache_344_; lean_object* v_recordedDeps_345_; lean_object* v_messages_346_; lean_object* v_infoState_347_; lean_object* v_snapshotTasks_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_378_; 
v___x_338_ = lean_st_ref_take(v___y_330_);
v_traceState_339_ = lean_ctor_get(v___x_338_, 4);
v_env_340_ = lean_ctor_get(v___x_338_, 0);
v_nextMacroScope_341_ = lean_ctor_get(v___x_338_, 1);
v_ngen_342_ = lean_ctor_get(v___x_338_, 2);
v_auxDeclNGen_343_ = lean_ctor_get(v___x_338_, 3);
v_cache_344_ = lean_ctor_get(v___x_338_, 5);
v_recordedDeps_345_ = lean_ctor_get(v___x_338_, 6);
v_messages_346_ = lean_ctor_get(v___x_338_, 7);
v_infoState_347_ = lean_ctor_get(v___x_338_, 8);
v_snapshotTasks_348_ = lean_ctor_get(v___x_338_, 9);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_378_ == 0)
{
v___x_350_ = v___x_338_;
v_isShared_351_ = v_isSharedCheck_378_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_snapshotTasks_348_);
lean_inc(v_infoState_347_);
lean_inc(v_messages_346_);
lean_inc(v_recordedDeps_345_);
lean_inc(v_cache_344_);
lean_inc(v_traceState_339_);
lean_inc(v_auxDeclNGen_343_);
lean_inc(v_ngen_342_);
lean_inc(v_nextMacroScope_341_);
lean_inc(v_env_340_);
lean_dec(v___x_338_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_378_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
uint64_t v_tid_352_; lean_object* v_traces_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_377_; 
v_tid_352_ = lean_ctor_get_uint64(v_traceState_339_, sizeof(void*)*1);
v_traces_353_ = lean_ctor_get(v_traceState_339_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v_traceState_339_);
if (v_isSharedCheck_377_ == 0)
{
v___x_355_ = v_traceState_339_;
v_isShared_356_ = v_isSharedCheck_377_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_traces_353_);
lean_dec(v_traceState_339_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_377_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_358_; double v___x_359_; uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_357_ = lean_box(0);
v___x_358_ = lean_box(0);
v___x_359_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0);
v___x_360_ = 0;
v___x_361_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__1));
v___x_362_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_362_, 0, v_cls_325_);
lean_ctor_set(v___x_362_, 1, v___x_358_);
lean_ctor_set(v___x_362_, 2, v___x_361_);
lean_ctor_set_float(v___x_362_, sizeof(void*)*3, v___x_359_);
lean_ctor_set_float(v___x_362_, sizeof(void*)*3 + 8, v___x_359_);
lean_ctor_set_uint8(v___x_362_, sizeof(void*)*3 + 16, v___x_360_);
v___x_363_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__2));
v___x_364_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_364_, 0, v___x_362_);
lean_ctor_set(v___x_364_, 1, v_a_334_);
lean_ctor_set(v___x_364_, 2, v___x_363_);
lean_inc(v_ref_332_);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v_ref_332_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = l_Lean_PersistentArray_push___redArg(v_traces_353_, v___x_365_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_366_);
v___x_368_ = v___x_355_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_366_);
lean_ctor_set_uint64(v_reuseFailAlloc_376_, sizeof(void*)*1, v_tid_352_);
v___x_368_ = v_reuseFailAlloc_376_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_370_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 4, v___x_368_);
v___x_370_ = v___x_350_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_env_340_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_nextMacroScope_341_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_ngen_342_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v_auxDeclNGen_343_);
lean_ctor_set(v_reuseFailAlloc_375_, 4, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_375_, 5, v_cache_344_);
lean_ctor_set(v_reuseFailAlloc_375_, 6, v_recordedDeps_345_);
lean_ctor_set(v_reuseFailAlloc_375_, 7, v_messages_346_);
lean_ctor_set(v_reuseFailAlloc_375_, 8, v_infoState_347_);
lean_ctor_set(v_reuseFailAlloc_375_, 9, v_snapshotTasks_348_);
v___x_370_ = v_reuseFailAlloc_375_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_371_ = lean_st_ref_put(v___y_330_, v___x_370_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_357_);
v___x_373_ = v___x_336_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_357_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___boxed(lean_object* v_cls_380_, lean_object* v_msg_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_380_, v_msg_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
return v_res_387_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_401_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_402_ = l_Lean_Name_append(v___x_401_, v___x_400_);
return v___x_402_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8));
v___x_405_ = l_Lean_stringToMessageData(v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(lean_object* v_p_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_543_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_543_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_543_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_543_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
if (lean_obj_tag(v_a_420_) == 1)
{
lean_object* v_val_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_538_; 
v_val_424_ = lean_ctor_get(v_a_420_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v_a_420_);
if (v_isSharedCheck_538_ == 0)
{
v___x_426_ = v_a_420_;
v_isShared_427_ = v_isSharedCheck_538_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_val_424_);
lean_dec(v_a_420_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_538_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_snd_428_; lean_object* v_snd_429_; lean_object* v_toCold_430_; lean_object* v_options_431_; lean_object* v_fst_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_536_; 
v_snd_428_ = lean_ctor_get(v_val_424_, 1);
lean_inc(v_snd_428_);
v_snd_429_ = lean_ctor_get(v_snd_428_, 1);
lean_inc(v_snd_429_);
v_toCold_430_ = lean_ctor_get(v_a_416_, 0);
v_options_431_ = lean_ctor_get(v_toCold_430_, 2);
v_fst_432_ = lean_ctor_get(v_val_424_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v_val_424_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; 
v_unused_537_ = lean_ctor_get(v_val_424_, 1);
lean_dec(v_unused_537_);
v___x_434_ = v_val_424_;
v_isShared_435_ = v_isSharedCheck_536_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_fst_432_);
lean_dec(v_val_424_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_536_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v_fst_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_534_; 
v_fst_436_ = lean_ctor_get(v_snd_428_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v_snd_428_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; 
v_unused_535_ = lean_ctor_get(v_snd_428_, 1);
lean_dec(v_unused_535_);
v___x_438_ = v_snd_428_;
v_isShared_439_ = v_isSharedCheck_534_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_fst_436_);
lean_dec(v_snd_428_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_534_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v_p_440_; lean_object* v_inheritedTraceOptions_441_; uint8_t v_hasTrace_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_p_440_ = lean_ctor_get(v_snd_429_, 0);
v_inheritedTraceOptions_441_ = lean_ctor_get(v_toCold_430_, 11);
v_hasTrace_442_ = lean_ctor_get_uint8(v_options_431_, sizeof(void*)*1);
v___x_443_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_440_, v_fst_436_);
lean_inc(v_p_406_);
v___x_444_ = l_Lean_Grind_Linarith_Poly_mul(v_p_406_, v___x_443_);
v___x_445_ = lean_int_neg(v_fst_432_);
lean_inc(v_p_440_);
v___x_446_ = l_Lean_Grind_Linarith_Poly_mul(v_p_440_, v___x_445_);
lean_dec(v___x_445_);
v___x_447_ = l_Lean_Grind_Linarith_Poly_combine(v___x_444_, v___x_446_);
if (v_hasTrace_442_ == 0)
{
lean_dec(v___x_443_);
lean_dec(v_fst_432_);
lean_dec(v_p_406_);
goto v___jp_448_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_461_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_462_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_463_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_441_, v_options_431_, v___x_462_);
if (v___x_463_ == 0)
{
lean_dec(v___x_443_);
lean_dec(v_fst_432_);
lean_dec(v_p_406_);
goto v___jp_448_;
}
else
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
lean_dec(v_p_406_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_466_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 1);
v___x_466_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_436_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_468_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_467_);
lean_dec_ref_known(v___x_466_, 1);
v___x_468_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_429_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_470_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
v___x_470_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v___x_447_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref_known(v___x_470_, 1);
v___x_472_ = l_Lean_MessageData_ofExpr(v_a_465_);
v___x_473_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_472_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = l_Int_repr(v_fst_432_);
lean_dec(v_fst_432_);
v___x_476_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
v___x_477_ = l_Lean_MessageData_ofFormat(v___x_476_);
v___x_478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_474_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v___x_473_);
v___x_480_ = l_Lean_MessageData_ofExpr(v_a_467_);
v___x_481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_479_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v___x_473_);
v___x_483_ = l_Lean_MessageData_ofExpr(v_a_469_);
v___x_484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_482_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v___x_473_);
v___x_486_ = l_Int_repr(v___x_443_);
lean_dec(v___x_443_);
v___x_487_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
v___x_488_ = l_Lean_MessageData_ofFormat(v___x_487_);
v___x_489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_485_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v___x_473_);
v___x_491_ = l_Lean_MessageData_ofExpr(v_a_471_);
v___x_492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_461_, v___x_492_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_dec_ref_known(v___x_493_, 1);
goto v___jp_448_;
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec(v___x_447_);
lean_del_object(v___x_438_);
lean_dec(v_fst_436_);
lean_del_object(v___x_434_);
lean_dec(v_snd_429_);
lean_del_object(v___x_426_);
lean_del_object(v___x_422_);
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
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
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_dec(v_a_469_);
lean_dec(v_a_467_);
lean_dec(v_a_465_);
lean_dec(v___x_447_);
lean_dec(v___x_443_);
lean_del_object(v___x_438_);
lean_dec(v_fst_436_);
lean_del_object(v___x_434_);
lean_dec(v_fst_432_);
lean_dec(v_snd_429_);
lean_del_object(v___x_426_);
lean_del_object(v___x_422_);
v_a_502_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_470_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_470_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec(v_a_467_);
lean_dec(v_a_465_);
lean_dec(v___x_447_);
lean_dec(v___x_443_);
lean_del_object(v___x_438_);
lean_dec(v_fst_436_);
lean_del_object(v___x_434_);
lean_dec(v_fst_432_);
lean_dec(v_snd_429_);
lean_del_object(v___x_426_);
lean_del_object(v___x_422_);
v_a_510_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_468_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_468_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec(v_a_465_);
lean_dec(v___x_447_);
lean_dec(v___x_443_);
lean_del_object(v___x_438_);
lean_dec(v_fst_436_);
lean_del_object(v___x_434_);
lean_dec(v_fst_432_);
lean_dec(v_snd_429_);
lean_del_object(v___x_426_);
lean_del_object(v___x_422_);
v_a_518_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_466_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_466_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v___x_447_);
lean_dec(v___x_443_);
lean_del_object(v___x_438_);
lean_dec(v_fst_436_);
lean_del_object(v___x_434_);
lean_dec(v_fst_432_);
lean_dec(v_snd_429_);
lean_del_object(v___x_426_);
lean_del_object(v___x_422_);
v_a_526_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_464_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_464_);
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
}
v___jp_448_:
{
lean_object* v___x_450_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v___x_447_);
lean_ctor_set(v___x_438_, 0, v_snd_429_);
v___x_450_ = v___x_438_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_snd_429_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_447_);
v___x_450_ = v_reuseFailAlloc_460_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_452_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v___x_450_);
lean_ctor_set(v___x_434_, 0, v_fst_436_);
v___x_452_ = v___x_434_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_fst_436_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v___x_450_);
v___x_452_ = v_reuseFailAlloc_459_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_454_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_452_);
v___x_454_ = v___x_426_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_458_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_456_; 
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_454_);
v___x_456_ = v___x_422_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
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
}
}
}
}
}
else
{
lean_object* v___x_539_; lean_object* v___x_541_; 
lean_dec(v_a_420_);
lean_dec(v_p_406_);
v___x_539_ = lean_box(0);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_539_);
v___x_541_ = v___x_422_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_dec(v_p_406_);
v_a_544_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_419_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_419_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___boxed(lean_object* v_p_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec(v_a_554_);
lean_dec(v_a_553_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(lean_object* v_cls_566_, lean_object* v_msg_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_566_, v_msg_567_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___boxed(lean_object* v_cls_581_, lean_object* v_msg_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_cls_581_, v_msg_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec(v___y_584_);
lean_dec(v___y_583_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(lean_object* v_c_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_p_609_; lean_object* v___x_610_; 
v_p_609_ = lean_ctor_get(v_c_596_, 0);
v___x_610_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_609_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_612_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 1);
v___x_612_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v_ofNatZero_614_; lean_object* v___x_615_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref_known(v___x_612_, 1);
v_ofNatZero_614_ = lean_ctor_get(v_a_613_, 18);
lean_inc_ref(v_ofNatZero_614_);
lean_dec(v_a_613_);
v___x_615_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3(v_a_611_, v_ofNatZero_614_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_624_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_624_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_624_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_624_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_620_ = l_Lean_mkNot(v_a_616_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_620_);
v___x_622_ = v___x_618_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
else
{
return v___x_615_;
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec(v_a_611_);
v_a_625_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_612_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_612_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
else
{
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0___boxed(lean_object* v_c_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v_c_633_);
return v_res_646_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_nat_to_int(v___x_647_);
return v___x_648_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2(void){
_start:
{
lean_object* v_cls_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_cls_653_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_654_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_655_ = l_Lean_Name_append(v___x_654_, v_cls_653_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(lean_object* v_a_656_, lean_object* v_x_657_, lean_object* v_c_u2081_658_, lean_object* v_b_659_, lean_object* v_c_u2082_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v_toCold_727_; lean_object* v_options_728_; uint8_t v_hasTrace_729_; 
v_toCold_727_ = lean_ctor_get(v_a_670_, 0);
v_options_728_ = lean_ctor_get(v_toCold_727_, 2);
v_hasTrace_729_ = lean_ctor_get_uint8(v_options_728_, sizeof(void*)*1);
if (v_hasTrace_729_ == 0)
{
v___y_674_ = v_a_661_;
v___y_675_ = v_a_662_;
v___y_676_ = v_a_663_;
v___y_677_ = v_a_664_;
v___y_678_ = v_a_665_;
v___y_679_ = v_a_666_;
v___y_680_ = v_a_667_;
v___y_681_ = v_a_668_;
v___y_682_ = v_a_669_;
v___y_683_ = v_a_670_;
v___y_684_ = v_a_671_;
goto v___jp_673_;
}
else
{
lean_object* v_inheritedTraceOptions_730_; lean_object* v_cls_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v_inheritedTraceOptions_730_ = lean_ctor_get(v_toCold_727_, 11);
v_cls_731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_732_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2);
v___x_733_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_730_, v_options_728_, v___x_732_);
if (v___x_733_ == 0)
{
v___y_674_ = v_a_661_;
v___y_675_ = v_a_662_;
v___y_676_ = v_a_663_;
v___y_677_ = v_a_664_;
v___y_678_ = v_a_665_;
v___y_679_ = v_a_666_;
v___y_680_ = v_a_667_;
v___y_681_ = v_a_668_;
v___y_682_ = v_a_669_;
v___y_683_ = v_a_670_;
v___y_684_ = v_a_671_;
goto v___jp_673_;
}
else
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_657_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_736_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
v___x_736_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_658_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_738_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref_known(v___x_736_, 1);
v___x_738_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_u2082_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
v___x_740_ = l_Lean_MessageData_ofExpr(v_a_735_);
v___x_741_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_Lean_MessageData_ofExpr(v_a_737_);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
lean_ctor_set(v___x_745_, 1, v___x_741_);
v___x_746_ = l_Lean_MessageData_ofExpr(v_a_739_);
v___x_747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_731_, v___x_747_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_dec_ref_known(v___x_748_, 1);
v___y_674_ = v_a_661_;
v___y_675_ = v_a_662_;
v___y_676_ = v_a_663_;
v___y_677_ = v_a_664_;
v___y_678_ = v_a_665_;
v___y_679_ = v_a_666_;
v___y_680_ = v_a_667_;
v___y_681_ = v_a_668_;
v___y_682_ = v_a_669_;
v___y_683_ = v_a_670_;
v___y_684_ = v_a_671_;
goto v___jp_673_;
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec_ref(v_c_u2082_660_);
lean_dec(v_b_659_);
lean_dec_ref(v_c_u2081_658_);
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec(v_a_737_);
lean_dec(v_a_735_);
lean_dec_ref(v_c_u2082_660_);
lean_dec(v_b_659_);
lean_dec_ref(v_c_u2081_658_);
v_a_757_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_738_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_738_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec(v_a_735_);
lean_dec_ref(v_c_u2082_660_);
lean_dec(v_b_659_);
lean_dec_ref(v_c_u2081_658_);
v_a_765_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_736_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_736_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec_ref(v_c_u2082_660_);
lean_dec(v_b_659_);
lean_dec_ref(v_c_u2081_658_);
v_a_773_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_734_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_734_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
v___jp_673_:
{
lean_object* v_p_685_; lean_object* v_p_686_; lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v_p_685_ = lean_ctor_get(v_c_u2081_658_, 0);
v_p_686_ = lean_ctor_get(v_c_u2082_660_, 0);
v___x_687_ = lean_int_emod(v_b_659_, v_a_656_);
v___x_688_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_689_ = lean_int_dec_eq(v___x_687_, v___x_688_);
lean_dec(v___x_687_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_710_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_710_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_710_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_710_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
uint8_t v___x_695_; 
v___x_695_ = lean_unbox(v_a_691_);
lean_dec(v_a_691_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_698_; 
lean_dec_ref(v_c_u2082_660_);
lean_dec(v_b_659_);
lean_dec_ref(v_c_u2081_658_);
v___x_696_ = lean_box(0);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_696_);
v___x_698_ = v___x_693_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
lean_inc(v_p_685_);
v___x_700_ = l_Lean_Grind_Linarith_Poly_mul(v_p_685_, v_b_659_);
v___x_701_ = lean_int_neg(v_a_656_);
lean_inc(v_p_686_);
v___x_702_ = l_Lean_Grind_Linarith_Poly_mul(v_p_686_, v___x_701_);
v___x_703_ = l_Lean_Grind_Linarith_Poly_combine(v___x_700_, v___x_702_);
v___x_704_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_704_, 0, v___x_701_);
lean_ctor_set(v___x_704_, 1, v_b_659_);
lean_ctor_set(v___x_704_, 2, v_c_u2081_658_);
lean_ctor_set(v___x_704_, 3, v_c_u2082_660_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_706_);
v___x_708_ = v___x_693_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref(v_c_u2082_660_);
lean_dec(v_b_659_);
lean_dec_ref(v_c_u2081_658_);
v_a_711_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_690_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_690_);
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
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_719_ = lean_int_neg(v_b_659_);
lean_dec(v_b_659_);
v___x_720_ = lean_int_ediv(v___x_719_, v_a_656_);
lean_dec(v___x_719_);
lean_inc(v_p_685_);
v___x_721_ = l_Lean_Grind_Linarith_Poly_mul(v_p_685_, v___x_720_);
lean_inc(v_p_686_);
v___x_722_ = l_Lean_Grind_Linarith_Poly_combine(v___x_721_, v_p_686_);
v___x_723_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_723_, 0, v___x_720_);
lean_ctor_set(v___x_723_, 1, v_c_u2081_658_);
lean_ctor_set(v___x_723_, 2, v_c_u2082_660_);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_722_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v___x_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___boxed(lean_object** _args){
lean_object* v_a_781_ = _args[0];
lean_object* v_x_782_ = _args[1];
lean_object* v_c_u2081_783_ = _args[2];
lean_object* v_b_784_ = _args[3];
lean_object* v_c_u2082_785_ = _args[4];
lean_object* v_a_786_ = _args[5];
lean_object* v_a_787_ = _args[6];
lean_object* v_a_788_ = _args[7];
lean_object* v_a_789_ = _args[8];
lean_object* v_a_790_ = _args[9];
lean_object* v_a_791_ = _args[10];
lean_object* v_a_792_ = _args[11];
lean_object* v_a_793_ = _args[12];
lean_object* v_a_794_ = _args[13];
lean_object* v_a_795_ = _args[14];
lean_object* v_a_796_ = _args[15];
lean_object* v_a_797_ = _args[16];
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_781_, v_x_782_, v_c_u2081_783_, v_b_784_, v_c_u2082_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec(v_a_787_);
lean_dec(v_a_786_);
lean_dec(v_x_782_);
lean_dec(v_a_781_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(lean_object* v_a_799_, lean_object* v_b_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_a_799_, v_a_801_, v_a_802_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_833_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_833_ == 0)
{
v___x_807_ = v___x_804_;
v_isShared_808_ = v_isSharedCheck_833_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_804_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_833_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
if (lean_obj_tag(v_a_805_) == 1)
{
lean_object* v_val_809_; lean_object* v___x_810_; 
lean_del_object(v___x_807_);
v_val_809_ = lean_ctor_get(v_a_805_, 0);
v___x_810_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_b_800_, v_a_801_, v_a_802_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_828_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_828_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_828_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_828_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
if (lean_obj_tag(v_a_811_) == 1)
{
lean_object* v_val_815_; uint8_t v___x_816_; 
v_val_815_ = lean_ctor_get(v_a_811_, 0);
lean_inc(v_val_815_);
lean_dec_ref_known(v_a_811_, 1);
v___x_816_ = lean_nat_dec_eq(v_val_809_, v_val_815_);
lean_dec(v_val_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; lean_object* v___x_819_; 
lean_dec_ref_known(v_a_805_, 1);
v___x_817_ = lean_box(0);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_817_);
v___x_819_ = v___x_813_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
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
lean_object* v___x_822_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v_a_805_);
v___x_822_ = v___x_813_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_805_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
else
{
lean_object* v___x_824_; lean_object* v___x_826_; 
lean_dec(v_a_811_);
lean_dec_ref_known(v_a_805_, 1);
v___x_824_ = lean_box(0);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_824_);
v___x_826_ = v___x_813_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_805_, 1);
return v___x_810_;
}
}
else
{
lean_object* v___x_829_; lean_object* v___x_831_; 
lean_dec(v_a_805_);
v___x_829_ = lean_box(0);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_829_);
v___x_831_ = v___x_807_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
else
{
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg___boxed(lean_object* v_a_834_, lean_object* v_b_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_834_, v_b_835_, v_a_836_, v_a_837_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
lean_dec_ref(v_b_835_);
lean_dec_ref(v_a_834_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(lean_object* v_a_840_, lean_object* v_b_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_840_, v_b_841_, v_a_842_, v_a_850_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___boxed(lean_object* v_a_854_, lean_object* v_b_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(v_a_854_, v_b_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec(v_a_856_);
lean_dec_ref(v_b_855_);
lean_dec_ref(v_a_854_);
return v_res_867_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_869_ = lean_int_neg(v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(lean_object* v_a_870_, lean_object* v_b_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
uint8_t v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_884_ = 0;
v___x_885_ = lean_box(v___x_884_);
lean_inc_ref(v_a_870_);
v___x_886_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 2);
lean_closure_set(v___x_886_, 0, v_a_870_);
lean_closure_set(v___x_886_, 1, v___x_885_);
v___x_887_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_886_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_1039_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_1039_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_1039_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
if (lean_obj_tag(v_a_888_) == 1)
{
lean_object* v_val_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
lean_del_object(v___x_890_);
v_val_892_ = lean_ctor_get(v_a_888_, 0);
lean_inc(v_val_892_);
lean_dec_ref_known(v_a_888_, 1);
v___x_893_ = lean_box(v___x_884_);
lean_inc_ref(v_b_871_);
v___x_894_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 2);
lean_closure_set(v___x_894_, 0, v_b_871_);
lean_closure_set(v___x_894_, 1, v___x_893_);
v___x_895_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_894_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_1026_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_898_ = v___x_895_;
v_isShared_899_ = v_isSharedCheck_1026_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_895_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_1026_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
if (lean_obj_tag(v_a_896_) == 1)
{
lean_object* v_val_900_; lean_object* v___x_901_; 
lean_del_object(v___x_898_);
v_val_900_ = lean_ctor_get(v_a_896_, 0);
lean_inc(v_val_900_);
lean_dec_ref_known(v_a_896_, 1);
v___x_901_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_870_, v_a_873_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_903_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v___x_901_, 1);
v___x_903_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_871_, v_a_873_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v___y_906_; uint8_t v___x_1005_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
lean_dec_ref_known(v___x_903_, 1);
v___x_1005_ = lean_nat_dec_le(v_a_902_, v_a_904_);
if (v___x_1005_ == 0)
{
lean_dec(v_a_904_);
v___y_906_ = v_a_902_;
goto v___jp_905_;
}
else
{
lean_dec(v_a_902_);
v___y_906_ = v_a_904_;
goto v___jp_905_;
}
v___jp_905_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
lean_inc(v_val_900_);
lean_inc(v_val_892_);
v___x_907_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_907_, 0, v_val_892_);
lean_ctor_set(v___x_907_, 1, v_val_900_);
v___x_908_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_907_);
v___x_909_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_909_, 0, v_a_870_);
lean_ctor_set(v___x_909_, 1, v_b_871_);
lean_ctor_set(v___x_909_, 2, v_val_892_);
lean_ctor_set(v___x_909_, 3, v_val_900_);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(v___x_910_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v_p_913_; lean_object* v___x_914_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 1);
v_p_913_ = lean_ctor_get(v_a_912_, 0);
lean_inc(v___y_906_);
lean_inc_ref(v_p_913_);
v___x_914_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_913_, v___y_906_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_916_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_914_, 1);
v___x_916_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_915_, v___x_884_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_980_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_980_ == 0)
{
v___x_919_ = v___x_916_;
v_isShared_920_ = v_isSharedCheck_980_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_916_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_980_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
if (lean_obj_tag(v_a_917_) == 1)
{
lean_object* v_val_921_; lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v_val_921_ = lean_ctor_get(v_a_917_, 0);
lean_inc_n(v_val_921_, 2);
lean_dec_ref_known(v_a_917_, 1);
v___x_922_ = l_Lean_Grind_Linarith_Expr_norm(v_val_921_);
v___x_923_ = lean_box(0);
v___x_924_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_922_, v___x_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
lean_del_object(v___x_919_);
lean_inc(v_a_912_);
v___x_925_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_925_, 0, v_a_912_);
lean_ctor_set(v___x_925_, 1, v_val_921_);
lean_inc(v___x_922_);
v___x_926_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_926_, 0, v___x_922_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
lean_ctor_set_uint8(v___x_926_, sizeof(void*)*2, v___x_884_);
v___x_927_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_926_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_970_; 
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_970_ == 0)
{
lean_object* v_unused_971_; 
v_unused_971_ = lean_ctor_get(v___x_927_, 0);
lean_dec(v_unused_971_);
v___x_929_ = v___x_927_;
v_isShared_930_ = v_isSharedCheck_970_;
goto v_resetjp_928_;
}
else
{
lean_dec(v___x_927_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_970_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_931_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_913_);
v___x_932_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_931_, v_p_913_);
if (v_isShared_930_ == 0)
{
lean_ctor_set_tag(v___x_929_, 1);
lean_ctor_set(v___x_929_, 0, v_a_912_);
v___x_934_ = v___x_929_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_912_);
v___x_934_ = v_reuseFailAlloc_969_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
lean_inc_ref(v___x_932_);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_932_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = l_Lean_Grind_Linarith_Poly_mul(v___x_922_, v___x_931_);
v___x_937_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v___x_932_, v___y_906_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_939_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
lean_dec_ref_known(v___x_937_, 1);
v___x_939_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_938_, v___x_884_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_952_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_952_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_952_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_952_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
if (lean_obj_tag(v_a_940_) == 1)
{
lean_object* v_val_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
lean_del_object(v___x_942_);
v_val_944_ = lean_ctor_get(v_a_940_, 0);
lean_inc(v_val_944_);
lean_dec_ref_known(v_a_940_, 1);
v___x_945_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_935_);
lean_ctor_set(v___x_945_, 1, v_val_944_);
v___x_946_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_946_, 0, v___x_936_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
lean_ctor_set_uint8(v___x_946_, sizeof(void*)*2, v___x_884_);
v___x_947_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_946_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
return v___x_947_;
}
else
{
lean_object* v___x_948_; lean_object* v___x_950_; 
lean_dec(v_a_940_);
lean_dec(v___x_936_);
lean_dec_ref_known(v___x_935_, 2);
v___x_948_ = lean_box(0);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_948_);
v___x_950_ = v___x_942_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec(v___x_936_);
lean_dec_ref_known(v___x_935_, 2);
v_a_953_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_939_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_939_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
lean_dec(v___x_936_);
lean_dec_ref_known(v___x_935_, 2);
v_a_961_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_937_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_937_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
}
else
{
lean_dec(v___x_922_);
lean_dec(v_a_912_);
lean_dec(v___y_906_);
return v___x_927_;
}
}
else
{
lean_object* v___x_972_; lean_object* v___x_974_; 
lean_dec(v___x_922_);
lean_dec(v_val_921_);
lean_dec(v_a_912_);
lean_dec(v___y_906_);
v___x_972_ = lean_box(0);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v___x_972_);
v___x_974_ = v___x_919_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
else
{
lean_object* v___x_976_; lean_object* v___x_978_; 
lean_dec(v_a_917_);
lean_dec(v_a_912_);
lean_dec(v___y_906_);
v___x_976_ = lean_box(0);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v___x_976_);
v___x_978_ = v___x_919_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
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
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec(v_a_912_);
lean_dec(v___y_906_);
v_a_981_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_916_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_916_);
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
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec(v_a_912_);
lean_dec(v___y_906_);
v_a_989_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_914_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_914_);
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
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v___y_906_);
v_a_997_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_911_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_911_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec(v_a_902_);
lean_dec(v_val_900_);
lean_dec(v_val_892_);
lean_dec_ref(v_b_871_);
lean_dec_ref(v_a_870_);
v_a_1006_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_903_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_903_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
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
lean_dec(v_val_900_);
lean_dec(v_val_892_);
lean_dec_ref(v_b_871_);
lean_dec_ref(v_a_870_);
v_a_1014_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_901_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_901_);
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
lean_object* v___x_1022_; lean_object* v___x_1024_; 
lean_dec(v_a_896_);
lean_dec(v_val_892_);
lean_dec_ref(v_b_871_);
lean_dec_ref(v_a_870_);
v___x_1022_ = lean_box(0);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_1022_);
v___x_1024_ = v___x_898_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v_val_892_);
lean_dec_ref(v_b_871_);
lean_dec_ref(v_a_870_);
v_a_1027_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_895_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_895_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
else
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
lean_dec(v_a_888_);
lean_dec_ref(v_b_871_);
lean_dec_ref(v_a_870_);
v___x_1035_ = lean_box(0);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_1035_);
v___x_1037_ = v___x_890_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
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
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_dec_ref(v_b_871_);
lean_dec_ref(v_a_870_);
v_a_1040_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_887_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_887_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___boxed(lean_object* v_a_1048_, lean_object* v_b_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_1048_, v_b_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec(v_a_1050_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(lean_object* v_a_1063_, lean_object* v_b_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
uint8_t v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = 0;
lean_inc_ref(v_a_1063_);
v___x_1078_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1063_, v___x_1077_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1123_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1123_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1123_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
if (lean_obj_tag(v_a_1079_) == 1)
{
lean_object* v_val_1083_; lean_object* v___x_1084_; 
lean_del_object(v___x_1081_);
v_val_1083_ = lean_ctor_get(v_a_1079_, 0);
lean_inc(v_val_1083_);
lean_dec_ref_known(v_a_1079_, 1);
lean_inc_ref(v_b_1064_);
v___x_1084_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_1064_, v___x_1077_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1110_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1110_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1110_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
if (lean_obj_tag(v_a_1085_) == 1)
{
lean_object* v_val_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v_val_1089_ = lean_ctor_get(v_a_1085_, 0);
lean_inc_n(v_val_1089_, 2);
lean_dec_ref_known(v_a_1085_, 1);
lean_inc(v_val_1083_);
v___x_1090_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1090_, 0, v_val_1083_);
lean_ctor_set(v___x_1090_, 1, v_val_1089_);
v___x_1091_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1090_);
v___x_1092_ = lean_box(0);
v___x_1093_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_1091_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_del_object(v___x_1087_);
lean_inc(v_val_1089_);
lean_inc(v_val_1083_);
lean_inc_ref(v_b_1064_);
lean_inc_ref(v_a_1063_);
v___x_1094_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1094_, 0, v_a_1063_);
lean_ctor_set(v___x_1094_, 1, v_b_1064_);
lean_ctor_set(v___x_1094_, 2, v_val_1083_);
lean_ctor_set(v___x_1094_, 3, v_val_1089_);
lean_inc(v___x_1091_);
v___x_1095_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1095_, 0, v___x_1091_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*2, v___x_1077_);
v___x_1096_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1095_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec_ref_known(v___x_1096_, 1);
v___x_1097_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_1098_ = l_Lean_Grind_Linarith_Poly_mul(v___x_1091_, v___x_1097_);
v___x_1099_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1099_, 0, v_b_1064_);
lean_ctor_set(v___x_1099_, 1, v_a_1063_);
lean_ctor_set(v___x_1099_, 2, v_val_1089_);
lean_ctor_set(v___x_1099_, 3, v_val_1083_);
v___x_1100_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
lean_ctor_set_uint8(v___x_1100_, sizeof(void*)*2, v___x_1077_);
v___x_1101_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1100_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_);
return v___x_1101_;
}
else
{
lean_dec(v___x_1091_);
lean_dec(v_val_1089_);
lean_dec(v_val_1083_);
lean_dec_ref(v_b_1064_);
lean_dec_ref(v_a_1063_);
return v___x_1096_;
}
}
else
{
lean_object* v___x_1102_; lean_object* v___x_1104_; 
lean_dec(v___x_1091_);
lean_dec(v_val_1089_);
lean_dec(v_val_1083_);
lean_dec_ref(v_b_1064_);
lean_dec_ref(v_a_1063_);
v___x_1102_ = lean_box(0);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1102_);
v___x_1104_ = v___x_1087_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1108_; 
lean_dec(v_a_1085_);
lean_dec(v_val_1083_);
lean_dec_ref(v_b_1064_);
lean_dec_ref(v_a_1063_);
v___x_1106_ = lean_box(0);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1106_);
v___x_1108_ = v___x_1087_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v_val_1083_);
lean_dec_ref(v_b_1064_);
lean_dec_ref(v_a_1063_);
v_a_1111_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1084_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1084_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1121_; 
lean_dec(v_a_1079_);
lean_dec_ref(v_b_1064_);
lean_dec_ref(v_a_1063_);
v___x_1119_ = lean_box(0);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1119_);
v___x_1121_ = v___x_1081_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec_ref(v_b_1064_);
lean_dec_ref(v_a_1063_);
v_a_1124_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1078_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1078_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27___boxed(lean_object* v_a_1132_, lean_object* v_b_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_1132_, v_b_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec(v_a_1134_);
return v_res_1146_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(lean_object* v_msg_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1161_; lean_object* v___f_1162_; lean_object* v___x_2795__overap_1163_; lean_object* v___x_1164_; 
v___x_1161_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0);
v___f_1162_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1162_, 0, v___x_1161_);
v___x_2795__overap_1163_ = lean_panic_fn_borrowed(v___f_1162_, v_msg_1148_);
lean_dec_ref(v___f_1162_);
lean_inc(v___y_1159_);
lean_inc_ref(v___y_1158_);
lean_inc(v___y_1157_);
lean_inc_ref(v___y_1156_);
lean_inc(v___y_1155_);
lean_inc_ref(v___y_1154_);
lean_inc(v___y_1153_);
lean_inc_ref(v___y_1152_);
lean_inc(v___y_1151_);
lean_inc(v___y_1150_);
lean_inc(v___y_1149_);
v___x_1164_ = lean_apply_12(v___x_2795__overap_1163_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, lean_box(0));
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___boxed(lean_object* v_msg_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v_msg_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec(v___y_1166_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__1(lean_object* v_a_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_nat_to_int(v_a_1179_);
return v___x_1180_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2));
v___x_1185_ = lean_unsigned_to_nat(42u);
v___x_1186_ = lean_unsigned_to_nat(87u);
v___x_1187_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1));
v___x_1188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0));
v___x_1189_ = l_mkPanicMessageWithDecl(v___x_1188_, v___x_1187_, v___x_1186_, v___x_1185_, v___x_1184_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(lean_object* v_c_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v_c_1206_; lean_object* v_c_1212_; lean_object* v_p_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; uint8_t v___x_1251_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___x_1249_, 1);
v___x_1251_ = lean_unbox(v_a_1250_);
lean_dec(v_a_1250_);
if (v___x_1251_ == 0)
{
lean_object* v_p_1252_; 
v_p_1252_ = lean_ctor_get(v_c_1190_, 0);
lean_inc(v_p_1252_);
v_c_1212_ = v_c_1190_;
v_p_1213_ = v_p_1252_;
v___y_1214_ = v_a_1191_;
v___y_1215_ = v_a_1192_;
v___y_1216_ = v_a_1193_;
v___y_1217_ = v_a_1194_;
v___y_1218_ = v_a_1195_;
v___y_1219_ = v_a_1196_;
v___y_1220_ = v_a_1197_;
v___y_1221_ = v_a_1198_;
v___y_1222_ = v_a_1199_;
v___y_1223_ = v_a_1200_;
v___y_1224_ = v_a_1201_;
goto v___jp_1211_;
}
else
{
lean_object* v_p_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v_p_1253_ = lean_ctor_get(v_c_1190_, 0);
v___x_1254_ = l_Lean_Grind_Linarith_Poly_gcdCoeffs(v_p_1253_);
v___x_1255_ = lean_unsigned_to_nat(1u);
v___x_1256_ = lean_nat_dec_eq(v___x_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_inc(v___x_1254_);
v___x_1257_ = lean_nat_to_int(v___x_1254_);
lean_inc(v_p_1253_);
v___x_1258_ = l_Lean_Grind_Linarith_Poly_div(v_p_1253_, v___x_1257_);
lean_dec(v___x_1257_);
v___x_1259_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1254_);
lean_ctor_set(v___x_1259_, 1, v_c_1190_);
lean_inc(v___x_1258_);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v_c_1212_ = v___x_1260_;
v_p_1213_ = v___x_1258_;
v___y_1214_ = v_a_1191_;
v___y_1215_ = v_a_1192_;
v___y_1216_ = v_a_1193_;
v___y_1217_ = v_a_1194_;
v___y_1218_ = v_a_1195_;
v___y_1219_ = v_a_1196_;
v___y_1220_ = v_a_1197_;
v___y_1221_ = v_a_1198_;
v___y_1222_ = v_a_1199_;
v___y_1223_ = v_a_1200_;
v___y_1224_ = v_a_1201_;
goto v___jp_1211_;
}
else
{
lean_inc(v_p_1253_);
lean_dec(v___x_1254_);
v_c_1212_ = v_c_1190_;
v_p_1213_ = v_p_1253_;
v___y_1214_ = v_a_1191_;
v___y_1215_ = v_a_1192_;
v___y_1216_ = v_a_1193_;
v___y_1217_ = v_a_1194_;
v___y_1218_ = v_a_1195_;
v___y_1219_ = v_a_1196_;
v___y_1220_ = v_a_1197_;
v___y_1221_ = v_a_1198_;
v___y_1222_ = v_a_1199_;
v___y_1223_ = v_a_1200_;
v___y_1224_ = v_a_1201_;
goto v___jp_1211_;
}
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_dec_ref(v_c_1190_);
v_a_1261_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1249_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1249_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
v___jp_1203_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1207_ = lean_nat_abs(v___y_1204_);
lean_dec(v___y_1204_);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___y_1205_);
lean_ctor_set(v___x_1208_, 1, v_c_1206_);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1207_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
return v___x_1210_;
}
v___jp_1211_:
{
lean_object* v___x_1225_; 
lean_inc(v_p_1213_);
v___x_1225_ = l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(v_p_1213_);
if (lean_obj_tag(v___x_1225_) == 1)
{
lean_object* v_val_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1246_; 
v_val_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1246_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_val_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1246_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v_fst_1230_; lean_object* v_snd_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1245_; 
v_fst_1230_ = lean_ctor_get(v_val_1226_, 0);
v_snd_1231_ = lean_ctor_get(v_val_1226_, 1);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_val_1226_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1233_ = v_val_1226_;
v_isShared_1234_ = v_isSharedCheck_1245_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_snd_1231_);
lean_inc(v_fst_1230_);
lean_dec(v_val_1226_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1245_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_1236_ = lean_int_dec_lt(v_fst_1230_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_del_object(v___x_1233_);
lean_del_object(v___x_1228_);
lean_dec(v_p_1213_);
v___y_1204_ = v_fst_1230_;
v___y_1205_ = v_snd_1231_;
v_c_1206_ = v_c_1212_;
goto v___jp_1203_;
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1237_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_1238_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1213_, v___x_1237_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set_tag(v___x_1228_, 3);
lean_ctor_set(v___x_1228_, 0, v_c_1212_);
v___x_1240_ = v___x_1228_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_c_1212_);
v___x_1240_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
lean_object* v___x_1242_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 1, v___x_1240_);
lean_ctor_set(v___x_1233_, 0, v___x_1238_);
v___x_1242_ = v___x_1233_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
v___y_1204_ = v_fst_1230_;
v___y_1205_ = v_snd_1231_;
v_c_1206_ = v___x_1242_;
goto v___jp_1203_;
}
}
}
}
}
}
else
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
lean_dec(v___x_1225_);
lean_dec(v_p_1213_);
lean_dec_ref(v_c_1212_);
v___x_1247_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3);
v___x_1248_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v___x_1247_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
return v___x_1248_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___boxed(lean_object* v_c_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_c_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec(v_a_1270_);
return v_res_1282_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = l_Lean_maxRecDepthErrorMessage;
v___x_1289_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
return v___x_1289_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_1291_ = l_Lean_MessageData_ofFormat(v___x_1290_);
return v___x_1291_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_1293_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_1294_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
lean_ctor_set(v___x_1294_, 1, v___x_1292_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_1295_){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1297_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1298_, 0, v_ref_1295_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1300_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_1303_, lean_object* v_ref_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1304_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_1318_, lean_object* v_ref_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(v_00_u03b1_1318_, v_ref_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec(v___y_1320_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(lean_object* v_c_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v_toCold_1364_; lean_object* v_p_1365_; lean_object* v_currRecDepth_1366_; lean_object* v_ref_1367_; uint16_t v_optionFlags_1368_; uint8_t v_suppressElabErrors_1369_; uint8_t v_isRecordingDeps_1370_; lean_object* v_options_1371_; lean_object* v_maxRecDepth_1372_; lean_object* v_inheritedTraceOptions_1373_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v_toCold_1364_ = lean_ctor_get(v_a_1343_, 0);
lean_inc_ref(v_toCold_1364_);
v_p_1365_ = lean_ctor_get(v_c_1333_, 0);
v_currRecDepth_1366_ = lean_ctor_get(v_a_1343_, 1);
lean_inc(v_currRecDepth_1366_);
v_ref_1367_ = lean_ctor_get(v_a_1343_, 2);
lean_inc(v_ref_1367_);
v_optionFlags_1368_ = lean_ctor_get_uint16(v_a_1343_, sizeof(void*)*3);
v_suppressElabErrors_1369_ = lean_ctor_get_uint8(v_a_1343_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1370_ = lean_ctor_get_uint8(v_a_1343_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_1343_);
v_options_1371_ = lean_ctor_get(v_toCold_1364_, 2);
lean_inc_ref(v_options_1371_);
v_maxRecDepth_1372_ = lean_ctor_get(v_toCold_1364_, 3);
v_inheritedTraceOptions_1373_ = lean_ctor_get(v_toCold_1364_, 11);
lean_inc_ref(v_inheritedTraceOptions_1373_);
v___x_1467_ = lean_unsigned_to_nat(0u);
v___x_1468_ = lean_nat_dec_eq(v_maxRecDepth_1372_, v___x_1467_);
if (v___x_1468_ == 0)
{
uint8_t v___x_1469_; 
v___x_1469_ = lean_nat_dec_eq(v_currRecDepth_1366_, v_maxRecDepth_1372_);
if (v___x_1469_ == 0)
{
goto v___jp_1374_;
}
else
{
lean_object* v___x_1470_; 
lean_dec_ref(v_inheritedTraceOptions_1373_);
lean_dec_ref(v_options_1371_);
lean_dec(v_currRecDepth_1366_);
lean_dec_ref(v_toCold_1364_);
lean_dec_ref(v_c_1333_);
v___x_1470_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1367_);
return v___x_1470_;
}
}
else
{
goto v___jp_1374_;
}
v___jp_1346_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_1361_, 0, v___y_1349_);
lean_ctor_set(v___x_1361_, 1, v___y_1347_);
lean_ctor_set(v___x_1361_, 2, v_c_1333_);
v___x_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___y_1348_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
v_c_1333_ = v___x_1362_;
v_a_1334_ = v___y_1350_;
v_a_1335_ = v___y_1351_;
v_a_1336_ = v___y_1352_;
v_a_1337_ = v___y_1353_;
v_a_1338_ = v___y_1354_;
v_a_1339_ = v___y_1355_;
v_a_1340_ = v___y_1356_;
v_a_1341_ = v___y_1357_;
v_a_1342_ = v___y_1358_;
v_a_1343_ = v___y_1359_;
v_a_1344_ = v___y_1360_;
goto _start;
}
v___jp_1374_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1375_ = lean_unsigned_to_nat(1u);
v___x_1376_ = lean_nat_add(v_currRecDepth_1366_, v___x_1375_);
lean_dec(v_currRecDepth_1366_);
v___x_1377_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1377_, 0, v_toCold_1364_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
lean_ctor_set(v___x_1377_, 2, v_ref_1367_);
lean_ctor_set_uint16(v___x_1377_, sizeof(void*)*3, v_optionFlags_1368_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 2, v_suppressElabErrors_1369_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 3, v_isRecordingDeps_1370_);
lean_inc(v_p_1365_);
v___x_1378_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_1365_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v___x_1377_, v_a_1344_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1458_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1381_ = v___x_1378_;
v_isShared_1382_ = v_isSharedCheck_1458_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1378_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1458_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
if (lean_obj_tag(v_a_1379_) == 1)
{
lean_object* v_val_1383_; lean_object* v_snd_1384_; uint8_t v_hasTrace_1385_; 
lean_del_object(v___x_1381_);
v_val_1383_ = lean_ctor_get(v_a_1379_, 0);
lean_inc(v_val_1383_);
lean_dec_ref_known(v_a_1379_, 1);
v_snd_1384_ = lean_ctor_get(v_val_1383_, 1);
lean_inc(v_snd_1384_);
v_hasTrace_1385_ = lean_ctor_get_uint8(v_options_1371_, sizeof(void*)*1);
if (v_hasTrace_1385_ == 0)
{
lean_object* v_fst_1386_; lean_object* v_fst_1387_; lean_object* v_snd_1388_; 
lean_dec_ref(v_inheritedTraceOptions_1373_);
lean_dec_ref(v_options_1371_);
v_fst_1386_ = lean_ctor_get(v_val_1383_, 0);
lean_inc(v_fst_1386_);
lean_dec(v_val_1383_);
v_fst_1387_ = lean_ctor_get(v_snd_1384_, 0);
lean_inc(v_fst_1387_);
v_snd_1388_ = lean_ctor_get(v_snd_1384_, 1);
lean_inc(v_snd_1388_);
lean_dec(v_snd_1384_);
v___y_1347_ = v_fst_1387_;
v___y_1348_ = v_snd_1388_;
v___y_1349_ = v_fst_1386_;
v___y_1350_ = v_a_1334_;
v___y_1351_ = v_a_1335_;
v___y_1352_ = v_a_1336_;
v___y_1353_ = v_a_1337_;
v___y_1354_ = v_a_1338_;
v___y_1355_ = v_a_1339_;
v___y_1356_ = v_a_1340_;
v___y_1357_ = v_a_1341_;
v___y_1358_ = v_a_1342_;
v___y_1359_ = v___x_1377_;
v___y_1360_ = v_a_1344_;
goto v___jp_1346_;
}
else
{
lean_object* v_fst_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1453_; 
v_fst_1389_ = lean_ctor_get(v_val_1383_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_val_1383_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v_val_1383_, 1);
lean_dec(v_unused_1454_);
v___x_1391_ = v_val_1383_;
v_isShared_1392_ = v_isSharedCheck_1453_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_fst_1389_);
lean_dec(v_val_1383_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1453_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v_fst_1393_; lean_object* v_snd_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1452_; 
v_fst_1393_ = lean_ctor_get(v_snd_1384_, 0);
v_snd_1394_ = lean_ctor_get(v_snd_1384_, 1);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_snd_1384_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1396_ = v_snd_1384_;
v_isShared_1397_ = v_isSharedCheck_1452_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_snd_1394_);
lean_inc(v_fst_1393_);
lean_dec(v_snd_1384_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1452_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_1399_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_1400_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1373_, v_options_1371_, v___x_1399_);
lean_dec_ref(v_options_1371_);
lean_dec_ref(v_inheritedTraceOptions_1373_);
if (v___x_1400_ == 0)
{
lean_del_object(v___x_1396_);
lean_del_object(v___x_1391_);
v___y_1347_ = v_fst_1393_;
v___y_1348_ = v_snd_1394_;
v___y_1349_ = v_fst_1389_;
v___y_1350_ = v_a_1334_;
v___y_1351_ = v_a_1335_;
v___y_1352_ = v_a_1336_;
v___y_1353_ = v_a_1337_;
v___y_1354_ = v_a_1338_;
v___y_1355_ = v_a_1339_;
v___y_1356_ = v_a_1340_;
v___y_1357_ = v_a_1341_;
v___y_1358_ = v_a_1342_;
v___y_1359_ = v___x_1377_;
v___y_1360_ = v_a_1344_;
goto v___jp_1346_;
}
else
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_1389_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v___x_1377_, v_a_1344_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1403_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1402_);
lean_dec_ref_known(v___x_1401_, 1);
v___x_1403_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v___x_1377_, v_a_1344_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v___x_1405_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v___x_1403_, 1);
v___x_1405_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_fst_1393_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v___x_1377_, v_a_1344_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1405_, 1);
v___x_1407_ = l_Lean_MessageData_ofExpr(v_a_1402_);
v___x_1408_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_1397_ == 0)
{
lean_ctor_set_tag(v___x_1396_, 7);
lean_ctor_set(v___x_1396_, 1, v___x_1408_);
lean_ctor_set(v___x_1396_, 0, v___x_1407_);
v___x_1410_ = v___x_1396_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = l_Lean_MessageData_ofExpr(v_a_1404_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set_tag(v___x_1391_, 7);
lean_ctor_set(v___x_1391_, 1, v___x_1411_);
lean_ctor_set(v___x_1391_, 0, v___x_1410_);
v___x_1413_ = v___x_1391_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
lean_ctor_set(v___x_1414_, 1, v___x_1408_);
v___x_1415_ = l_Lean_MessageData_ofExpr(v_a_1406_);
v___x_1416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_1398_, v___x_1416_, v_a_1341_, v_a_1342_, v___x_1377_, v_a_1344_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_dec_ref_known(v___x_1417_, 1);
v___y_1347_ = v_fst_1393_;
v___y_1348_ = v_snd_1394_;
v___y_1349_ = v_fst_1389_;
v___y_1350_ = v_a_1334_;
v___y_1351_ = v_a_1335_;
v___y_1352_ = v_a_1336_;
v___y_1353_ = v_a_1337_;
v___y_1354_ = v_a_1338_;
v___y_1355_ = v_a_1339_;
v___y_1356_ = v_a_1340_;
v___y_1357_ = v_a_1341_;
v___y_1358_ = v_a_1342_;
v___y_1359_ = v___x_1377_;
v___y_1360_ = v_a_1344_;
goto v___jp_1346_;
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec(v_snd_1394_);
lean_dec(v_fst_1393_);
lean_dec(v_fst_1389_);
lean_dec_ref_known(v___x_1377_, 3);
lean_dec_ref(v_c_1333_);
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1417_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1417_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec(v_a_1404_);
lean_dec(v_a_1402_);
lean_del_object(v___x_1396_);
lean_dec(v_snd_1394_);
lean_dec(v_fst_1393_);
lean_del_object(v___x_1391_);
lean_dec(v_fst_1389_);
lean_dec_ref_known(v___x_1377_, 3);
lean_dec_ref(v_c_1333_);
v_a_1428_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1405_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1405_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec(v_a_1402_);
lean_del_object(v___x_1396_);
lean_dec(v_snd_1394_);
lean_dec(v_fst_1393_);
lean_del_object(v___x_1391_);
lean_dec(v_fst_1389_);
lean_dec_ref_known(v___x_1377_, 3);
lean_dec_ref(v_c_1333_);
v_a_1436_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1403_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1403_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_del_object(v___x_1396_);
lean_dec(v_snd_1394_);
lean_dec(v_fst_1393_);
lean_del_object(v___x_1391_);
lean_dec(v_fst_1389_);
lean_dec_ref_known(v___x_1377_, 3);
lean_dec_ref(v_c_1333_);
v_a_1444_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1401_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1401_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
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
lean_object* v___x_1456_; 
lean_dec(v_a_1379_);
lean_dec_ref_known(v___x_1377_, 3);
lean_dec_ref(v_inheritedTraceOptions_1373_);
lean_dec_ref(v_options_1371_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v_c_1333_);
v___x_1456_ = v___x_1381_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_c_1333_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_dec_ref_known(v___x_1377_, 3);
lean_dec_ref(v_inheritedTraceOptions_1373_);
lean_dec_ref(v_options_1371_);
lean_dec_ref(v_c_1333_);
v_a_1459_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1378_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1378_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object* v_c_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
lean_dec(v_a_1482_);
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
lean_dec(v_a_1476_);
lean_dec_ref(v_a_1475_);
lean_dec(v_a_1474_);
lean_dec(v_a_1473_);
lean_dec(v_a_1472_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_ref_1491_; lean_object* v___x_1492_; lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1501_; 
v_ref_1491_ = lean_ctor_get(v___y_1488_, 2);
v___x_1492_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msg_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1495_ = v___x_1492_;
v_isShared_1496_ = v_isSharedCheck_1501_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1492_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1501_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v___x_1499_; 
lean_inc(v_ref_1491_);
v___x_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1497_, 0, v_ref_1491_);
lean_ctor_set(v___x_1497_, 1, v_a_1493_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set_tag(v___x_1495_, 1);
lean_ctor_set(v___x_1495_, 0, v___x_1497_);
v___x_1499_ = v___x_1495_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
return v_res_1508_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0));
v___x_1511_ = l_Lean_stringToMessageData(v___x_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1536_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1536_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1536_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v_leFn_x3f_1529_; 
v_leFn_x3f_1529_ = lean_ctor_get(v_a_1525_, 20);
lean_inc(v_leFn_x3f_1529_);
lean_dec(v_a_1525_);
if (lean_obj_tag(v_leFn_x3f_1529_) == 1)
{
lean_object* v_val_1530_; lean_object* v___x_1532_; 
v_val_1530_ = lean_ctor_get(v_leFn_x3f_1529_, 0);
lean_inc(v_val_1530_);
lean_dec_ref_known(v_leFn_x3f_1529_, 1);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v_val_1530_);
v___x_1532_ = v___x_1527_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_val_1530_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
else
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_dec(v_leFn_x3f_1529_);
lean_del_object(v___x_1527_);
v___x_1534_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1);
v___x_1535_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1534_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
return v___x_1535_;
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
v_a_1537_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1524_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1524_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___boxed(lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec(v___y_1545_);
return v_res_1557_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0));
v___x_1560_ = l_Lean_stringToMessageData(v___x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1585_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1585_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1585_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v_ltFn_x3f_1578_; 
v_ltFn_x3f_1578_ = lean_ctor_get(v_a_1574_, 21);
lean_inc(v_ltFn_x3f_1578_);
lean_dec(v_a_1574_);
if (lean_obj_tag(v_ltFn_x3f_1578_) == 1)
{
lean_object* v_val_1579_; lean_object* v___x_1581_; 
v_val_1579_ = lean_ctor_get(v_ltFn_x3f_1578_, 0);
lean_inc(v_val_1579_);
lean_dec_ref_known(v_ltFn_x3f_1578_, 1);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v_val_1579_);
v___x_1581_ = v___x_1576_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_val_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_dec(v_ltFn_x3f_1578_);
lean_del_object(v___x_1576_);
v___x_1583_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1);
v___x_1584_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1583_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
return v___x_1584_;
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
v_a_1586_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1573_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1573_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___boxed(lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec(v___y_1594_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(lean_object* v_p_1607_, uint8_t v_strict_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
if (v_strict_1608_ == 0)
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1623_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v___x_1623_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1607_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1625_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 1);
v___x_1625_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1635_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1635_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1635_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v_ofNatZero_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
v_ofNatZero_1630_ = lean_ctor_get(v_a_1626_, 18);
lean_inc_ref(v_ofNatZero_1630_);
lean_dec(v_a_1626_);
v___x_1631_ = l_Lean_mkAppB(v_a_1622_, v_a_1624_, v_ofNatZero_1630_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1631_);
v___x_1633_ = v___x_1628_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v_a_1624_);
lean_dec(v_a_1622_);
v_a_1636_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1625_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1625_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
else
{
lean_dec(v_a_1622_);
return v___x_1623_;
}
}
else
{
return v___x_1621_;
}
}
else
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1646_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v___x_1644_, 1);
v___x_1646_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1607_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1648_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1647_);
lean_dec_ref_known(v___x_1646_, 1);
v___x_1648_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1658_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1651_ = v___x_1648_;
v_isShared_1652_ = v_isSharedCheck_1658_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1648_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1658_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v_ofNatZero_1653_; lean_object* v___x_1654_; lean_object* v___x_1656_; 
v_ofNatZero_1653_ = lean_ctor_get(v_a_1649_, 18);
lean_inc_ref(v_ofNatZero_1653_);
lean_dec(v_a_1649_);
v___x_1654_ = l_Lean_mkAppB(v_a_1645_, v_a_1647_, v_ofNatZero_1653_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v___x_1654_);
v___x_1656_ = v___x_1651_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec(v_a_1647_);
lean_dec(v_a_1645_);
v_a_1659_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1648_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1648_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
else
{
lean_dec(v_a_1645_);
return v___x_1646_;
}
}
else
{
return v___x_1644_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_p_1667_, lean_object* v_strict_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
uint8_t v_strict_boxed_1681_; lean_object* v_res_1682_; 
v_strict_boxed_1681_ = lean_unbox(v_strict_1668_);
v_res_1682_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1667_, v_strict_boxed_1681_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec(v_p_1667_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(lean_object* v_c_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_p_1696_; uint8_t v_strict_1697_; lean_object* v___x_1698_; 
v_p_1696_ = lean_ctor_get(v_c_1683_, 0);
v_strict_1697_ = lean_ctor_get_uint8(v_c_1683_, sizeof(void*)*2);
v___x_1698_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1696_, v_strict_1697_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0___boxed(lean_object* v_c_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v_c_1699_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object* v_a_1713_, lean_object* v_x_1714_, lean_object* v_c_u2081_1715_, lean_object* v_b_1716_, lean_object* v_c_u2082_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v_toCold_1730_; lean_object* v_options_1731_; lean_object* v_p_1732_; lean_object* v_p_1733_; uint8_t v_strict_1734_; lean_object* v_inheritedTraceOptions_1735_; uint8_t v_hasTrace_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v_p_1741_; 
v_toCold_1730_ = lean_ctor_get(v_a_1727_, 0);
v_options_1731_ = lean_ctor_get(v_toCold_1730_, 2);
v_p_1732_ = lean_ctor_get(v_c_u2081_1715_, 0);
v_p_1733_ = lean_ctor_get(v_c_u2082_1717_, 0);
v_strict_1734_ = lean_ctor_get_uint8(v_c_u2082_1717_, sizeof(void*)*2);
v_inheritedTraceOptions_1735_ = lean_ctor_get(v_toCold_1730_, 11);
v_hasTrace_1736_ = lean_ctor_get_uint8(v_options_1731_, sizeof(void*)*1);
v___x_1737_ = lean_nat_to_int(v_a_1713_);
lean_inc(v_p_1733_);
v___x_1738_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1733_, v___x_1737_);
lean_dec(v___x_1737_);
v___x_1739_ = lean_int_neg(v_b_1716_);
lean_inc(v_p_1732_);
v___x_1740_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1732_, v___x_1739_);
lean_dec(v___x_1739_);
v_p_1741_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1738_, v___x_1740_);
if (v_hasTrace_1736_ == 0)
{
goto v___jp_1742_;
}
else
{
lean_object* v_cls_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v_cls_1746_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_1747_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2);
v___x_1748_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1735_, v_options_1731_, v___x_1747_);
if (v___x_1748_ == 0)
{
goto v___jp_1742_;
}
else
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1714_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1751_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v___x_1751_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_1715_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1753_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1751_, 1);
v___x_1753_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_u2082_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref_known(v___x_1753_, 1);
v___x_1755_ = l_Lean_MessageData_ofExpr(v_a_1750_);
v___x_1756_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_1757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1755_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
v___x_1758_ = l_Lean_MessageData_ofExpr(v_a_1752_);
v___x_1759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1757_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v___x_1760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
lean_ctor_set(v___x_1760_, 1, v___x_1756_);
v___x_1761_ = l_Lean_MessageData_ofExpr(v_a_1754_);
v___x_1762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1760_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
v___x_1763_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_1746_, v___x_1762_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_dec_ref_known(v___x_1763_, 1);
goto v___jp_1742_;
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec(v_p_1741_);
lean_dec_ref(v_c_u2082_1717_);
lean_dec_ref(v_c_u2081_1715_);
lean_dec(v_x_1714_);
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1763_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1763_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec(v_a_1752_);
lean_dec(v_a_1750_);
lean_dec(v_p_1741_);
lean_dec_ref(v_c_u2082_1717_);
lean_dec_ref(v_c_u2081_1715_);
lean_dec(v_x_1714_);
v_a_1772_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1753_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1753_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec(v_a_1750_);
lean_dec(v_p_1741_);
lean_dec_ref(v_c_u2082_1717_);
lean_dec_ref(v_c_u2081_1715_);
lean_dec(v_x_1714_);
v_a_1780_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1751_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1751_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec(v_p_1741_);
lean_dec_ref(v_c_u2082_1717_);
lean_dec_ref(v_c_u2081_1715_);
lean_dec(v_x_1714_);
v_a_1788_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1749_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1749_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
v___jp_1742_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1743_ = lean_alloc_ctor(13, 3, 0);
lean_ctor_set(v___x_1743_, 0, v_x_1714_);
lean_ctor_set(v___x_1743_, 1, v_c_u2081_1715_);
lean_ctor_set(v___x_1743_, 2, v_c_u2082_1717_);
v___x_1744_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1744_, 0, v_p_1741_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
lean_ctor_set_uint8(v___x_1744_, sizeof(void*)*2, v_strict_1734_);
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
return v___x_1745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object** _args){
lean_object* v_a_1796_ = _args[0];
lean_object* v_x_1797_ = _args[1];
lean_object* v_c_u2081_1798_ = _args[2];
lean_object* v_b_1799_ = _args[3];
lean_object* v_c_u2082_1800_ = _args[4];
lean_object* v_a_1801_ = _args[5];
lean_object* v_a_1802_ = _args[6];
lean_object* v_a_1803_ = _args[7];
lean_object* v_a_1804_ = _args[8];
lean_object* v_a_1805_ = _args[9];
lean_object* v_a_1806_ = _args[10];
lean_object* v_a_1807_ = _args[11];
lean_object* v_a_1808_ = _args[12];
lean_object* v_a_1809_ = _args[13];
lean_object* v_a_1810_ = _args[14];
lean_object* v_a_1811_ = _args[15];
lean_object* v_a_1812_ = _args[16];
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1796_, v_x_1797_, v_c_u2081_1798_, v_b_1799_, v_c_u2082_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_);
lean_dec(v_a_1811_);
lean_dec_ref(v_a_1810_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec(v_a_1805_);
lean_dec_ref(v_a_1804_);
lean_dec(v_a_1803_);
lean_dec(v_a_1802_);
lean_dec(v_a_1801_);
lean_dec(v_b_1799_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1814_, lean_object* v_msg_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1815_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1829_, lean_object* v_msg_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1829_, v_msg_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec(v___y_1831_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(lean_object* v_a_1852_, lean_object* v_x_1853_, lean_object* v_c_u2081_1854_, lean_object* v_as_1855_, size_t v_sz_1856_, size_t v_i_1857_, lean_object* v_b_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
uint8_t v___x_1871_; 
v___x_1871_ = lean_usize_dec_lt(v_i_1857_, v_sz_1856_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; 
lean_dec_ref(v_c_u2081_1854_);
lean_dec(v_x_1853_);
lean_dec(v_a_1852_);
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_b_1858_);
return v___x_1872_;
}
else
{
lean_object* v_a_1873_; lean_object* v_fst_1874_; lean_object* v_snd_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_dec_ref(v_b_1858_);
v_a_1873_ = lean_array_uget_borrowed(v_as_1855_, v_i_1857_);
v_fst_1874_ = lean_ctor_get(v_a_1873_, 0);
v_snd_1875_ = lean_ctor_get(v_a_1873_, 1);
v___x_1876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
lean_inc(v_snd_1875_);
lean_inc_ref(v_c_u2081_1854_);
lean_inc(v_x_1853_);
lean_inc(v_a_1852_);
v___x_1877_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1852_, v_x_1853_, v_c_u2081_1854_, v_fst_1874_, v_snd_1875_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v___x_1879_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref_known(v___x_1877_, 1);
v___x_1879_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_a_1878_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v___x_1880_; 
lean_dec_ref_known(v___x_1879_, 1);
v___x_1880_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1893_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1883_ = v___x_1880_;
v_isShared_1884_ = v_isSharedCheck_1893_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1880_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1893_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
uint8_t v___x_1885_; 
v___x_1885_ = lean_unbox(v_a_1881_);
lean_dec(v_a_1881_);
if (v___x_1885_ == 0)
{
size_t v___x_1886_; size_t v___x_1887_; 
lean_del_object(v___x_1883_);
v___x_1886_ = ((size_t)1ULL);
v___x_1887_ = lean_usize_add(v_i_1857_, v___x_1886_);
v_i_1857_ = v___x_1887_;
v_b_1858_ = v___x_1876_;
goto _start;
}
else
{
lean_object* v___x_1889_; lean_object* v___x_1891_; 
lean_dec_ref(v_c_u2081_1854_);
lean_dec(v_x_1853_);
lean_dec(v_a_1852_);
v___x_1889_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1889_);
v___x_1891_ = v___x_1883_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec_ref(v_c_u2081_1854_);
lean_dec(v_x_1853_);
lean_dec(v_a_1852_);
v_a_1894_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1880_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1880_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec_ref(v_c_u2081_1854_);
lean_dec(v_x_1853_);
lean_dec(v_a_1852_);
v_a_1902_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1879_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1879_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_dec_ref(v_c_u2081_1854_);
lean_dec(v_x_1853_);
lean_dec(v_a_1852_);
v_a_1910_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1877_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1877_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___boxed(lean_object** _args){
lean_object* v_a_1918_ = _args[0];
lean_object* v_x_1919_ = _args[1];
lean_object* v_c_u2081_1920_ = _args[2];
lean_object* v_as_1921_ = _args[3];
lean_object* v_sz_1922_ = _args[4];
lean_object* v_i_1923_ = _args[5];
lean_object* v_b_1924_ = _args[6];
lean_object* v___y_1925_ = _args[7];
lean_object* v___y_1926_ = _args[8];
lean_object* v___y_1927_ = _args[9];
lean_object* v___y_1928_ = _args[10];
lean_object* v___y_1929_ = _args[11];
lean_object* v___y_1930_ = _args[12];
lean_object* v___y_1931_ = _args[13];
lean_object* v___y_1932_ = _args[14];
lean_object* v___y_1933_ = _args[15];
lean_object* v___y_1934_ = _args[16];
lean_object* v___y_1935_ = _args[17];
lean_object* v___y_1936_ = _args[18];
_start:
{
size_t v_sz_boxed_1937_; size_t v_i_boxed_1938_; lean_object* v_res_1939_; 
v_sz_boxed_1937_ = lean_unbox_usize(v_sz_1922_);
lean_dec(v_sz_1922_);
v_i_boxed_1938_ = lean_unbox_usize(v_i_1923_);
lean_dec(v_i_1923_);
v_res_1939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1918_, v_x_1919_, v_c_u2081_1920_, v_as_1921_, v_sz_boxed_1937_, v_i_boxed_1938_, v_b_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v_as_1921_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(lean_object* v_a_1940_, lean_object* v_x_1941_, lean_object* v_c_u2081_1942_, lean_object* v_todo_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; size_t v_sz_1958_; size_t v___x_1959_; lean_object* v___x_1960_; 
v___x_1956_ = lean_box(0);
v___x_1957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_1958_ = lean_array_size(v_todo_1943_);
v___x_1959_ = ((size_t)0ULL);
v___x_1960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1940_, v_x_1941_, v_c_u2081_1942_, v_todo_1943_, v_sz_1958_, v___x_1959_, v___x_1957_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1973_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_1973_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1973_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v_fst_1965_; 
v_fst_1965_ = lean_ctor_get(v_a_1961_, 0);
lean_inc(v_fst_1965_);
lean_dec(v_a_1961_);
if (lean_obj_tag(v_fst_1965_) == 0)
{
lean_object* v___x_1967_; 
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1956_);
v___x_1967_ = v___x_1963_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1956_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
else
{
lean_object* v_val_1969_; lean_object* v___x_1971_; 
v_val_1969_ = lean_ctor_get(v_fst_1965_, 0);
lean_inc(v_val_1969_);
lean_dec_ref_known(v_fst_1965_, 1);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v_val_1969_);
v___x_1971_ = v___x_1963_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_val_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
v_a_1974_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1960_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1960_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object* v_a_1982_, lean_object* v_x_1983_, lean_object* v_c_u2081_1984_, lean_object* v_todo_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_1982_, v_x_1983_, v_c_u2081_1984_, v_todo_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
lean_dec(v_a_1996_);
lean_dec_ref(v_a_1995_);
lean_dec(v_a_1994_);
lean_dec_ref(v_a_1993_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
lean_dec(v_a_1988_);
lean_dec(v_a_1987_);
lean_dec(v_a_1986_);
lean_dec_ref(v_todo_1985_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_1999_, lean_object* v_as_2000_, size_t v_sz_2001_, size_t v_i_2002_, lean_object* v_b_2003_){
_start:
{
uint8_t v___x_2004_; 
v___x_2004_ = lean_usize_dec_lt(v_i_2002_, v_sz_2001_);
if (v___x_2004_ == 0)
{
return v_b_2003_;
}
else
{
lean_object* v_snd_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2038_; 
v_snd_2005_ = lean_ctor_get(v_b_2003_, 1);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_b_2003_);
if (v_isSharedCheck_2038_ == 0)
{
lean_object* v_unused_2039_; 
v_unused_2039_ = lean_ctor_get(v_b_2003_, 0);
lean_dec(v_unused_2039_);
v___x_2007_ = v_b_2003_;
v_isShared_2008_ = v_isSharedCheck_2038_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_snd_2005_);
lean_dec(v_b_2003_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2038_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v_fst_2009_; lean_object* v_snd_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2037_; 
v_fst_2009_ = lean_ctor_get(v_snd_2005_, 0);
v_snd_2010_ = lean_ctor_get(v_snd_2005_, 1);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_snd_2005_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2012_ = v_snd_2005_;
v_isShared_2013_ = v_isSharedCheck_2037_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_snd_2010_);
lean_inc(v_fst_2009_);
lean_dec(v_snd_2005_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2037_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v_a_2014_; lean_object* v_p_2015_; lean_object* v___x_2016_; lean_object* v_a_2018_; lean_object* v_b_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v_a_2014_ = lean_array_uget_borrowed(v_as_2000_, v_i_2002_);
v_p_2015_ = lean_ctor_get(v_a_2014_, 0);
v___x_2016_ = lean_box(0);
v_b_2025_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2015_, v_x_1999_);
v___x_2026_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2027_ = lean_int_dec_eq(v_b_2025_, v___x_2026_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2029_; 
lean_inc(v_a_2014_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 1, v_a_2014_);
lean_ctor_set(v___x_2007_, 0, v_b_2025_);
v___x_2029_ = v___x_2007_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_b_2025_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_a_2014_);
v___x_2029_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v_todo_2030_; lean_object* v___x_2031_; 
v_todo_2030_ = lean_array_push(v_snd_2010_, v___x_2029_);
v___x_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2031_, 0, v_fst_2009_);
lean_ctor_set(v___x_2031_, 1, v_todo_2030_);
v_a_2018_ = v___x_2031_;
goto v___jp_2017_;
}
}
else
{
lean_object* v_cs_x27_2033_; lean_object* v___x_2035_; 
lean_dec(v_b_2025_);
lean_inc(v_a_2014_);
v_cs_x27_2033_ = l_Lean_PersistentArray_push___redArg(v_fst_2009_, v_a_2014_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 1, v_snd_2010_);
lean_ctor_set(v___x_2007_, 0, v_cs_x27_2033_);
v___x_2035_ = v___x_2007_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_cs_x27_2033_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_snd_2010_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
v_a_2018_ = v___x_2035_;
goto v___jp_2017_;
}
}
v___jp_2017_:
{
lean_object* v___x_2020_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 1, v_a_2018_);
lean_ctor_set(v___x_2012_, 0, v___x_2016_);
v___x_2020_ = v___x_2012_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2016_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_a_2018_);
v___x_2020_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
size_t v___x_2021_; size_t v___x_2022_; 
v___x_2021_ = ((size_t)1ULL);
v___x_2022_ = lean_usize_add(v_i_2002_, v___x_2021_);
v_i_2002_ = v___x_2022_;
v_b_2003_ = v___x_2020_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_2040_, lean_object* v_as_2041_, lean_object* v_sz_2042_, lean_object* v_i_2043_, lean_object* v_b_2044_){
_start:
{
size_t v_sz_boxed_2045_; size_t v_i_boxed_2046_; lean_object* v_res_2047_; 
v_sz_boxed_2045_ = lean_unbox_usize(v_sz_2042_);
lean_dec(v_sz_2042_);
v_i_boxed_2046_ = lean_unbox_usize(v_i_2043_);
lean_dec(v_i_2043_);
v_res_2047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2040_, v_as_2041_, v_sz_boxed_2045_, v_i_boxed_2046_, v_b_2044_);
lean_dec_ref(v_as_2041_);
lean_dec(v_x_2040_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(lean_object* v_x_2048_, lean_object* v_as_2049_, size_t v_sz_2050_, size_t v_i_2051_, lean_object* v_b_2052_){
_start:
{
uint8_t v___x_2053_; 
v___x_2053_ = lean_usize_dec_lt(v_i_2051_, v_sz_2050_);
if (v___x_2053_ == 0)
{
return v_b_2052_;
}
else
{
lean_object* v_snd_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2087_; 
v_snd_2054_ = lean_ctor_get(v_b_2052_, 1);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_b_2052_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; 
v_unused_2088_ = lean_ctor_get(v_b_2052_, 0);
lean_dec(v_unused_2088_);
v___x_2056_ = v_b_2052_;
v_isShared_2057_ = v_isSharedCheck_2087_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_snd_2054_);
lean_dec(v_b_2052_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2087_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v_fst_2058_; lean_object* v_snd_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2086_; 
v_fst_2058_ = lean_ctor_get(v_snd_2054_, 0);
v_snd_2059_ = lean_ctor_get(v_snd_2054_, 1);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_snd_2054_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2061_ = v_snd_2054_;
v_isShared_2062_ = v_isSharedCheck_2086_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_snd_2059_);
lean_inc(v_fst_2058_);
lean_dec(v_snd_2054_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2086_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v_a_2063_; lean_object* v_p_2064_; lean_object* v___x_2065_; lean_object* v_a_2067_; lean_object* v_b_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v_a_2063_ = lean_array_uget_borrowed(v_as_2049_, v_i_2051_);
v_p_2064_ = lean_ctor_get(v_a_2063_, 0);
v___x_2065_ = lean_box(0);
v_b_2074_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2064_, v_x_2048_);
v___x_2075_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2076_ = lean_int_dec_eq(v_b_2074_, v___x_2075_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2078_; 
lean_inc(v_a_2063_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 1, v_a_2063_);
lean_ctor_set(v___x_2056_, 0, v_b_2074_);
v___x_2078_ = v___x_2056_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_b_2074_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v_a_2063_);
v___x_2078_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v_todo_2079_; lean_object* v___x_2080_; 
v_todo_2079_ = lean_array_push(v_snd_2059_, v___x_2078_);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v_fst_2058_);
lean_ctor_set(v___x_2080_, 1, v_todo_2079_);
v_a_2067_ = v___x_2080_;
goto v___jp_2066_;
}
}
else
{
lean_object* v_cs_x27_2082_; lean_object* v___x_2084_; 
lean_dec(v_b_2074_);
lean_inc(v_a_2063_);
v_cs_x27_2082_ = l_Lean_PersistentArray_push___redArg(v_fst_2058_, v_a_2063_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 1, v_snd_2059_);
lean_ctor_set(v___x_2056_, 0, v_cs_x27_2082_);
v___x_2084_ = v___x_2056_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_cs_x27_2082_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_snd_2059_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
v_a_2067_ = v___x_2084_;
goto v___jp_2066_;
}
}
v___jp_2066_:
{
lean_object* v___x_2069_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 1, v_a_2067_);
lean_ctor_set(v___x_2061_, 0, v___x_2065_);
v___x_2069_ = v___x_2061_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v_a_2067_);
v___x_2069_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
size_t v___x_2070_; size_t v___x_2071_; lean_object* v___x_2072_; 
v___x_2070_ = ((size_t)1ULL);
v___x_2071_ = lean_usize_add(v_i_2051_, v___x_2070_);
v___x_2072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2048_, v_as_2049_, v_sz_2050_, v___x_2071_, v___x_2069_);
return v___x_2072_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2089_, lean_object* v_as_2090_, lean_object* v_sz_2091_, lean_object* v_i_2092_, lean_object* v_b_2093_){
_start:
{
size_t v_sz_boxed_2094_; size_t v_i_boxed_2095_; lean_object* v_res_2096_; 
v_sz_boxed_2094_ = lean_unbox_usize(v_sz_2091_);
lean_dec(v_sz_2091_);
v_i_boxed_2095_ = lean_unbox_usize(v_i_2092_);
lean_dec(v_i_2092_);
v_res_2096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2089_, v_as_2090_, v_sz_boxed_2094_, v_i_boxed_2095_, v_b_2093_);
lean_dec_ref(v_as_2090_);
lean_dec(v_x_2089_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_2097_, lean_object* v_as_2098_, size_t v_sz_2099_, size_t v_i_2100_, lean_object* v_b_2101_){
_start:
{
uint8_t v___x_2102_; 
v___x_2102_ = lean_usize_dec_lt(v_i_2100_, v_sz_2099_);
if (v___x_2102_ == 0)
{
return v_b_2101_;
}
else
{
lean_object* v_snd_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2136_; 
v_snd_2103_ = lean_ctor_get(v_b_2101_, 1);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_b_2101_);
if (v_isSharedCheck_2136_ == 0)
{
lean_object* v_unused_2137_; 
v_unused_2137_ = lean_ctor_get(v_b_2101_, 0);
lean_dec(v_unused_2137_);
v___x_2105_ = v_b_2101_;
v_isShared_2106_ = v_isSharedCheck_2136_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_snd_2103_);
lean_dec(v_b_2101_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2136_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v_fst_2107_; lean_object* v_snd_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2135_; 
v_fst_2107_ = lean_ctor_get(v_snd_2103_, 0);
v_snd_2108_ = lean_ctor_get(v_snd_2103_, 1);
v_isSharedCheck_2135_ = !lean_is_exclusive(v_snd_2103_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2110_ = v_snd_2103_;
v_isShared_2111_ = v_isSharedCheck_2135_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_snd_2108_);
lean_inc(v_fst_2107_);
lean_dec(v_snd_2103_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2135_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v_a_2112_; lean_object* v_p_2113_; lean_object* v___x_2114_; lean_object* v_a_2116_; lean_object* v_b_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; 
v_a_2112_ = lean_array_uget_borrowed(v_as_2098_, v_i_2100_);
v_p_2113_ = lean_ctor_get(v_a_2112_, 0);
v___x_2114_ = lean_box(0);
v_b_2123_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2113_, v_x_2097_);
v___x_2124_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2125_ = lean_int_dec_eq(v_b_2123_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2127_; 
lean_inc(v_a_2112_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 1, v_a_2112_);
lean_ctor_set(v___x_2105_, 0, v_b_2123_);
v___x_2127_ = v___x_2105_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_b_2123_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_a_2112_);
v___x_2127_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v_todo_2128_; lean_object* v___x_2129_; 
v_todo_2128_ = lean_array_push(v_snd_2108_, v___x_2127_);
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v_fst_2107_);
lean_ctor_set(v___x_2129_, 1, v_todo_2128_);
v_a_2116_ = v___x_2129_;
goto v___jp_2115_;
}
}
else
{
lean_object* v_cs_x27_2131_; lean_object* v___x_2133_; 
lean_dec(v_b_2123_);
lean_inc(v_a_2112_);
v_cs_x27_2131_ = l_Lean_PersistentArray_push___redArg(v_fst_2107_, v_a_2112_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 1, v_snd_2108_);
lean_ctor_set(v___x_2105_, 0, v_cs_x27_2131_);
v___x_2133_ = v___x_2105_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_cs_x27_2131_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_snd_2108_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
v_a_2116_ = v___x_2133_;
goto v___jp_2115_;
}
}
v___jp_2115_:
{
lean_object* v___x_2118_; 
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 1, v_a_2116_);
lean_ctor_set(v___x_2110_, 0, v___x_2114_);
v___x_2118_ = v___x_2110_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2114_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_a_2116_);
v___x_2118_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
size_t v___x_2119_; size_t v___x_2120_; 
v___x_2119_ = ((size_t)1ULL);
v___x_2120_ = lean_usize_add(v_i_2100_, v___x_2119_);
v_i_2100_ = v___x_2120_;
v_b_2101_ = v___x_2118_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_2138_, lean_object* v_as_2139_, lean_object* v_sz_2140_, lean_object* v_i_2141_, lean_object* v_b_2142_){
_start:
{
size_t v_sz_boxed_2143_; size_t v_i_boxed_2144_; lean_object* v_res_2145_; 
v_sz_boxed_2143_ = lean_unbox_usize(v_sz_2140_);
lean_dec(v_sz_2140_);
v_i_boxed_2144_ = lean_unbox_usize(v_i_2141_);
lean_dec(v_i_2141_);
v_res_2145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2138_, v_as_2139_, v_sz_boxed_2143_, v_i_boxed_2144_, v_b_2142_);
lean_dec_ref(v_as_2139_);
lean_dec(v_x_2138_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2146_, lean_object* v_as_2147_, size_t v_sz_2148_, size_t v_i_2149_, lean_object* v_b_2150_){
_start:
{
uint8_t v___x_2151_; 
v___x_2151_ = lean_usize_dec_lt(v_i_2149_, v_sz_2148_);
if (v___x_2151_ == 0)
{
return v_b_2150_;
}
else
{
lean_object* v_snd_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2185_; 
v_snd_2152_ = lean_ctor_get(v_b_2150_, 1);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_b_2150_);
if (v_isSharedCheck_2185_ == 0)
{
lean_object* v_unused_2186_; 
v_unused_2186_ = lean_ctor_get(v_b_2150_, 0);
lean_dec(v_unused_2186_);
v___x_2154_ = v_b_2150_;
v_isShared_2155_ = v_isSharedCheck_2185_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_snd_2152_);
lean_dec(v_b_2150_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2185_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v_fst_2156_; lean_object* v_snd_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2184_; 
v_fst_2156_ = lean_ctor_get(v_snd_2152_, 0);
v_snd_2157_ = lean_ctor_get(v_snd_2152_, 1);
v_isSharedCheck_2184_ = !lean_is_exclusive(v_snd_2152_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2159_ = v_snd_2152_;
v_isShared_2160_ = v_isSharedCheck_2184_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_snd_2157_);
lean_inc(v_fst_2156_);
lean_dec(v_snd_2152_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2184_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v_a_2161_; lean_object* v_p_2162_; lean_object* v___x_2163_; lean_object* v_a_2165_; lean_object* v_b_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; 
v_a_2161_ = lean_array_uget_borrowed(v_as_2147_, v_i_2149_);
v_p_2162_ = lean_ctor_get(v_a_2161_, 0);
v___x_2163_ = lean_box(0);
v_b_2172_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2162_, v_x_2146_);
v___x_2173_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2174_ = lean_int_dec_eq(v_b_2172_, v___x_2173_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2176_; 
lean_inc(v_a_2161_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 1, v_a_2161_);
lean_ctor_set(v___x_2154_, 0, v_b_2172_);
v___x_2176_ = v___x_2154_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_b_2172_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_a_2161_);
v___x_2176_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
lean_object* v_todo_2177_; lean_object* v___x_2178_; 
v_todo_2177_ = lean_array_push(v_snd_2157_, v___x_2176_);
v___x_2178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2178_, 0, v_fst_2156_);
lean_ctor_set(v___x_2178_, 1, v_todo_2177_);
v_a_2165_ = v___x_2178_;
goto v___jp_2164_;
}
}
else
{
lean_object* v_cs_x27_2180_; lean_object* v___x_2182_; 
lean_dec(v_b_2172_);
lean_inc(v_a_2161_);
v_cs_x27_2180_ = l_Lean_PersistentArray_push___redArg(v_fst_2156_, v_a_2161_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 1, v_snd_2157_);
lean_ctor_set(v___x_2154_, 0, v_cs_x27_2180_);
v___x_2182_ = v___x_2154_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_cs_x27_2180_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_snd_2157_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
v_a_2165_ = v___x_2182_;
goto v___jp_2164_;
}
}
v___jp_2164_:
{
lean_object* v___x_2167_; 
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 1, v_a_2165_);
lean_ctor_set(v___x_2159_, 0, v___x_2163_);
v___x_2167_ = v___x_2159_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_a_2165_);
v___x_2167_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
size_t v___x_2168_; size_t v___x_2169_; lean_object* v___x_2170_; 
v___x_2168_ = ((size_t)1ULL);
v___x_2169_ = lean_usize_add(v_i_2149_, v___x_2168_);
v___x_2170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2146_, v_as_2147_, v_sz_2148_, v___x_2169_, v___x_2167_);
return v___x_2170_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_2187_, lean_object* v_as_2188_, lean_object* v_sz_2189_, lean_object* v_i_2190_, lean_object* v_b_2191_){
_start:
{
size_t v_sz_boxed_2192_; size_t v_i_boxed_2193_; lean_object* v_res_2194_; 
v_sz_boxed_2192_ = lean_unbox_usize(v_sz_2189_);
lean_dec(v_sz_2189_);
v_i_boxed_2193_ = lean_unbox_usize(v_i_2190_);
lean_dec(v_i_2190_);
v_res_2194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2187_, v_as_2188_, v_sz_boxed_2192_, v_i_boxed_2193_, v_b_2191_);
lean_dec_ref(v_as_2188_);
lean_dec(v_x_2187_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(lean_object* v_init_2195_, lean_object* v_x_2196_, lean_object* v_n_2197_, lean_object* v_b_2198_){
_start:
{
if (lean_obj_tag(v_n_2197_) == 0)
{
lean_object* v_cs_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; size_t v_sz_2202_; size_t v___x_2203_; lean_object* v___x_2204_; lean_object* v_fst_2205_; 
v_cs_2199_ = lean_ctor_get(v_n_2197_, 0);
v___x_2200_ = lean_box(0);
v___x_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
lean_ctor_set(v___x_2201_, 1, v_b_2198_);
v_sz_2202_ = lean_array_size(v_cs_2199_);
v___x_2203_ = ((size_t)0ULL);
v___x_2204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2195_, v_x_2196_, v_cs_2199_, v_sz_2202_, v___x_2203_, v___x_2201_);
v_fst_2205_ = lean_ctor_get(v___x_2204_, 0);
if (lean_obj_tag(v_fst_2205_) == 0)
{
lean_object* v_snd_2206_; lean_object* v___x_2207_; 
v_snd_2206_ = lean_ctor_get(v___x_2204_, 1);
lean_inc(v_snd_2206_);
lean_dec_ref(v___x_2204_);
v___x_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2207_, 0, v_snd_2206_);
return v___x_2207_;
}
else
{
lean_object* v_val_2208_; 
lean_inc_ref(v_fst_2205_);
lean_dec_ref(v___x_2204_);
v_val_2208_ = lean_ctor_get(v_fst_2205_, 0);
lean_inc(v_val_2208_);
lean_dec_ref_known(v_fst_2205_, 1);
return v_val_2208_;
}
}
else
{
lean_object* v_vs_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; size_t v_sz_2212_; size_t v___x_2213_; lean_object* v___x_2214_; lean_object* v_fst_2215_; 
v_vs_2209_ = lean_ctor_get(v_n_2197_, 0);
v___x_2210_ = lean_box(0);
v___x_2211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
lean_ctor_set(v___x_2211_, 1, v_b_2198_);
v_sz_2212_ = lean_array_size(v_vs_2209_);
v___x_2213_ = ((size_t)0ULL);
v___x_2214_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2196_, v_vs_2209_, v_sz_2212_, v___x_2213_, v___x_2211_);
v_fst_2215_ = lean_ctor_get(v___x_2214_, 0);
if (lean_obj_tag(v_fst_2215_) == 0)
{
lean_object* v_snd_2216_; lean_object* v___x_2217_; 
v_snd_2216_ = lean_ctor_get(v___x_2214_, 1);
lean_inc(v_snd_2216_);
lean_dec_ref(v___x_2214_);
v___x_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2217_, 0, v_snd_2216_);
return v___x_2217_;
}
else
{
lean_object* v_val_2218_; 
lean_inc_ref(v_fst_2215_);
lean_dec_ref(v___x_2214_);
v_val_2218_ = lean_ctor_get(v_fst_2215_, 0);
lean_inc(v_val_2218_);
lean_dec_ref_known(v_fst_2215_, 1);
return v_val_2218_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_2219_, lean_object* v_x_2220_, lean_object* v_as_2221_, size_t v_sz_2222_, size_t v_i_2223_, lean_object* v_b_2224_){
_start:
{
uint8_t v___x_2225_; 
v___x_2225_ = lean_usize_dec_lt(v_i_2223_, v_sz_2222_);
if (v___x_2225_ == 0)
{
return v_b_2224_;
}
else
{
lean_object* v_snd_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2244_; 
v_snd_2226_ = lean_ctor_get(v_b_2224_, 1);
v_isSharedCheck_2244_ = !lean_is_exclusive(v_b_2224_);
if (v_isSharedCheck_2244_ == 0)
{
lean_object* v_unused_2245_; 
v_unused_2245_ = lean_ctor_get(v_b_2224_, 0);
lean_dec(v_unused_2245_);
v___x_2228_ = v_b_2224_;
v_isShared_2229_ = v_isSharedCheck_2244_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_snd_2226_);
lean_dec(v_b_2224_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2244_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v_a_2230_; lean_object* v___x_2231_; 
v_a_2230_ = lean_array_uget_borrowed(v_as_2221_, v_i_2223_);
lean_inc(v_snd_2226_);
v___x_2231_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2219_, v_x_2220_, v_a_2230_, v_snd_2226_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v___x_2232_);
v___x_2234_ = v___x_2228_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_snd_2226_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
lean_dec(v_snd_2226_);
v_a_2236_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2231_, 1);
v___x_2237_ = lean_box(0);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 1, v_a_2236_);
lean_ctor_set(v___x_2228_, 0, v___x_2237_);
v___x_2239_ = v___x_2228_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_a_2236_);
v___x_2239_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
size_t v___x_2240_; size_t v___x_2241_; 
v___x_2240_ = ((size_t)1ULL);
v___x_2241_ = lean_usize_add(v_i_2223_, v___x_2240_);
v_i_2223_ = v___x_2241_;
v_b_2224_ = v___x_2239_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_2246_, lean_object* v_x_2247_, lean_object* v_as_2248_, lean_object* v_sz_2249_, lean_object* v_i_2250_, lean_object* v_b_2251_){
_start:
{
size_t v_sz_boxed_2252_; size_t v_i_boxed_2253_; lean_object* v_res_2254_; 
v_sz_boxed_2252_ = lean_unbox_usize(v_sz_2249_);
lean_dec(v_sz_2249_);
v_i_boxed_2253_ = lean_unbox_usize(v_i_2250_);
lean_dec(v_i_2250_);
v_res_2254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2246_, v_x_2247_, v_as_2248_, v_sz_boxed_2252_, v_i_boxed_2253_, v_b_2251_);
lean_dec_ref(v_as_2248_);
lean_dec(v_x_2247_);
lean_dec_ref(v_init_2246_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_2255_, lean_object* v_x_2256_, lean_object* v_n_2257_, lean_object* v_b_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2255_, v_x_2256_, v_n_2257_, v_b_2258_);
lean_dec_ref(v_n_2257_);
lean_dec(v_x_2256_);
lean_dec_ref(v_init_2255_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(lean_object* v_x_2260_, lean_object* v_t_2261_, lean_object* v_init_2262_){
_start:
{
lean_object* v_root_2263_; lean_object* v_tail_2264_; lean_object* v___x_2265_; 
v_root_2263_ = lean_ctor_get(v_t_2261_, 0);
v_tail_2264_ = lean_ctor_get(v_t_2261_, 1);
lean_inc_ref(v_init_2262_);
v___x_2265_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2262_, v_x_2260_, v_root_2263_, v_init_2262_);
lean_dec_ref(v_init_2262_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref_known(v___x_2265_, 1);
return v_a_2266_;
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; size_t v_sz_2270_; size_t v___x_2271_; lean_object* v___x_2272_; lean_object* v_fst_2273_; 
v_a_2267_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2265_, 1);
v___x_2268_ = lean_box(0);
v___x_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
lean_ctor_set(v___x_2269_, 1, v_a_2267_);
v_sz_2270_ = lean_array_size(v_tail_2264_);
v___x_2271_ = ((size_t)0ULL);
v___x_2272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2260_, v_tail_2264_, v_sz_2270_, v___x_2271_, v___x_2269_);
v_fst_2273_ = lean_ctor_get(v___x_2272_, 0);
if (lean_obj_tag(v_fst_2273_) == 0)
{
lean_object* v_snd_2274_; 
v_snd_2274_ = lean_ctor_get(v___x_2272_, 1);
lean_inc(v_snd_2274_);
lean_dec_ref(v___x_2272_);
return v_snd_2274_;
}
else
{
lean_object* v_val_2275_; 
lean_inc_ref(v_fst_2273_);
lean_dec_ref(v___x_2272_);
v_val_2275_ = lean_ctor_get(v_fst_2273_, 0);
lean_inc(v_val_2275_);
lean_dec_ref_known(v_fst_2273_, 1);
return v_val_2275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0___boxed(lean_object* v_x_2276_, lean_object* v_t_2277_, lean_object* v_init_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2276_, v_t_2277_, v_init_2278_);
lean_dec_ref(v_t_2277_);
lean_dec(v_x_2276_);
return v_res_2279_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = lean_unsigned_to_nat(32u);
v___x_2281_ = lean_mk_empty_array_with_capacity(v___x_2280_);
v___x_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
return v___x_2282_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1(void){
_start:
{
size_t v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v_cs_x27_2288_; 
v___x_2283_ = ((size_t)5ULL);
v___x_2284_ = lean_unsigned_to_nat(0u);
v___x_2285_ = lean_unsigned_to_nat(32u);
v___x_2286_ = lean_mk_empty_array_with_capacity(v___x_2285_);
v___x_2287_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0);
v_cs_x27_2288_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_2288_, 0, v___x_2287_);
lean_ctor_set(v_cs_x27_2288_, 1, v___x_2286_);
lean_ctor_set(v_cs_x27_2288_, 2, v___x_2284_);
lean_ctor_set(v_cs_x27_2288_, 3, v___x_2284_);
lean_ctor_set_usize(v_cs_x27_2288_, 4, v___x_2283_);
return v_cs_x27_2288_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_2291_; lean_object* v_cs_x27_2292_; lean_object* v___x_2293_; 
v_todo_2291_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2));
v_cs_x27_2292_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1);
v___x_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2293_, 0, v_cs_x27_2292_);
lean_ctor_set(v___x_2293_, 1, v_todo_2291_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(lean_object* v_x_2294_, lean_object* v_cs_2295_){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v_fst_2298_; lean_object* v_snd_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
v___x_2296_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3);
v___x_2297_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2294_, v_cs_2295_, v___x_2296_);
v_fst_2298_ = lean_ctor_get(v___x_2297_, 0);
v_snd_2299_ = lean_ctor_get(v___x_2297_, 1);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2297_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_snd_2299_);
lean_inc(v_fst_2298_);
lean_dec(v___x_2297_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_fst_2298_);
lean_ctor_set(v_reuseFailAlloc_2305_, 1, v_snd_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___boxed(lean_object* v_x_2307_, lean_object* v_cs_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2307_, v_cs_2308_);
lean_dec_ref(v_cs_2308_);
lean_dec(v_x_2307_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object* v_x_2310_, lean_object* v_cs_2311_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2310_, v_cs_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___boxed(lean_object* v_x_2313_, lean_object* v_cs_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(v_x_2313_, v_cs_2314_);
lean_dec_ref(v_cs_2314_);
lean_dec(v_x_2313_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(lean_object* v_a_2316_, lean_object* v_y_2317_, lean_object* v_fst_2318_, lean_object* v_s_2319_){
_start:
{
lean_object* v_structs_2320_; lean_object* v_typeIdOf_2321_; lean_object* v_exprToStructId_2322_; lean_object* v_exprToStructIdEntries_2323_; lean_object* v_forbiddenNatModules_2324_; lean_object* v_natStructs_2325_; lean_object* v_natTypeIdOf_2326_; lean_object* v_exprToNatStructId_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
v_structs_2320_ = lean_ctor_get(v_s_2319_, 0);
v_typeIdOf_2321_ = lean_ctor_get(v_s_2319_, 1);
v_exprToStructId_2322_ = lean_ctor_get(v_s_2319_, 2);
v_exprToStructIdEntries_2323_ = lean_ctor_get(v_s_2319_, 3);
v_forbiddenNatModules_2324_ = lean_ctor_get(v_s_2319_, 4);
v_natStructs_2325_ = lean_ctor_get(v_s_2319_, 5);
v_natTypeIdOf_2326_ = lean_ctor_get(v_s_2319_, 6);
v_exprToNatStructId_2327_ = lean_ctor_get(v_s_2319_, 7);
v___x_2328_ = lean_array_get_size(v_structs_2320_);
v___x_2329_ = lean_nat_dec_lt(v_a_2316_, v___x_2328_);
if (v___x_2329_ == 0)
{
lean_dec_ref(v_fst_2318_);
return v_s_2319_;
}
else
{
lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2391_; 
lean_inc_ref(v_exprToNatStructId_2327_);
lean_inc_ref(v_natTypeIdOf_2326_);
lean_inc_ref(v_natStructs_2325_);
lean_inc_ref(v_forbiddenNatModules_2324_);
lean_inc_ref(v_exprToStructIdEntries_2323_);
lean_inc_ref(v_exprToStructId_2322_);
lean_inc_ref(v_typeIdOf_2321_);
lean_inc_ref(v_structs_2320_);
v_isSharedCheck_2391_ = !lean_is_exclusive(v_s_2319_);
if (v_isSharedCheck_2391_ == 0)
{
lean_object* v_unused_2392_; lean_object* v_unused_2393_; lean_object* v_unused_2394_; lean_object* v_unused_2395_; lean_object* v_unused_2396_; lean_object* v_unused_2397_; lean_object* v_unused_2398_; lean_object* v_unused_2399_; 
v_unused_2392_ = lean_ctor_get(v_s_2319_, 7);
lean_dec(v_unused_2392_);
v_unused_2393_ = lean_ctor_get(v_s_2319_, 6);
lean_dec(v_unused_2393_);
v_unused_2394_ = lean_ctor_get(v_s_2319_, 5);
lean_dec(v_unused_2394_);
v_unused_2395_ = lean_ctor_get(v_s_2319_, 4);
lean_dec(v_unused_2395_);
v_unused_2396_ = lean_ctor_get(v_s_2319_, 3);
lean_dec(v_unused_2396_);
v_unused_2397_ = lean_ctor_get(v_s_2319_, 2);
lean_dec(v_unused_2397_);
v_unused_2398_ = lean_ctor_get(v_s_2319_, 1);
lean_dec(v_unused_2398_);
v_unused_2399_ = lean_ctor_get(v_s_2319_, 0);
lean_dec(v_unused_2399_);
v___x_2331_ = v_s_2319_;
v_isShared_2332_ = v_isSharedCheck_2391_;
goto v_resetjp_2330_;
}
else
{
lean_dec(v_s_2319_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2391_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v_v_2333_; lean_object* v_id_2334_; lean_object* v_ringId_x3f_2335_; lean_object* v_type_2336_; lean_object* v_u_2337_; lean_object* v_intModuleInst_2338_; lean_object* v_leInst_x3f_2339_; lean_object* v_ltInst_x3f_2340_; lean_object* v_lawfulOrderLTInst_x3f_2341_; lean_object* v_isPreorderInst_x3f_2342_; lean_object* v_orderedAddInst_x3f_2343_; lean_object* v_isLinearInst_x3f_2344_; lean_object* v_noNatDivInst_x3f_2345_; lean_object* v_ringInst_x3f_2346_; lean_object* v_commRingInst_x3f_2347_; lean_object* v_orderedRingInst_x3f_2348_; lean_object* v_fieldInst_x3f_2349_; lean_object* v_charInst_x3f_2350_; lean_object* v_zero_2351_; lean_object* v_ofNatZero_2352_; lean_object* v_one_x3f_2353_; lean_object* v_leFn_x3f_2354_; lean_object* v_ltFn_x3f_2355_; lean_object* v_addFn_2356_; lean_object* v_zsmulFn_2357_; lean_object* v_nsmulFn_2358_; lean_object* v_zsmulFn_x3f_2359_; lean_object* v_nsmulFn_x3f_2360_; lean_object* v_homomulFn_x3f_2361_; lean_object* v_subFn_2362_; lean_object* v_negFn_2363_; lean_object* v_vars_2364_; lean_object* v_varMap_2365_; lean_object* v_lowers_2366_; lean_object* v_uppers_2367_; lean_object* v_diseqs_2368_; lean_object* v_assignment_2369_; uint8_t v_caseSplits_2370_; lean_object* v_conflict_x3f_2371_; lean_object* v_diseqSplits_2372_; lean_object* v_elimEqs_2373_; lean_object* v_elimStack_2374_; lean_object* v_occurs_2375_; lean_object* v_ignored_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2390_; 
v_v_2333_ = lean_array_fget(v_structs_2320_, v_a_2316_);
v_id_2334_ = lean_ctor_get(v_v_2333_, 0);
v_ringId_x3f_2335_ = lean_ctor_get(v_v_2333_, 1);
v_type_2336_ = lean_ctor_get(v_v_2333_, 2);
v_u_2337_ = lean_ctor_get(v_v_2333_, 3);
v_intModuleInst_2338_ = lean_ctor_get(v_v_2333_, 4);
v_leInst_x3f_2339_ = lean_ctor_get(v_v_2333_, 5);
v_ltInst_x3f_2340_ = lean_ctor_get(v_v_2333_, 6);
v_lawfulOrderLTInst_x3f_2341_ = lean_ctor_get(v_v_2333_, 7);
v_isPreorderInst_x3f_2342_ = lean_ctor_get(v_v_2333_, 8);
v_orderedAddInst_x3f_2343_ = lean_ctor_get(v_v_2333_, 9);
v_isLinearInst_x3f_2344_ = lean_ctor_get(v_v_2333_, 10);
v_noNatDivInst_x3f_2345_ = lean_ctor_get(v_v_2333_, 11);
v_ringInst_x3f_2346_ = lean_ctor_get(v_v_2333_, 12);
v_commRingInst_x3f_2347_ = lean_ctor_get(v_v_2333_, 13);
v_orderedRingInst_x3f_2348_ = lean_ctor_get(v_v_2333_, 14);
v_fieldInst_x3f_2349_ = lean_ctor_get(v_v_2333_, 15);
v_charInst_x3f_2350_ = lean_ctor_get(v_v_2333_, 16);
v_zero_2351_ = lean_ctor_get(v_v_2333_, 17);
v_ofNatZero_2352_ = lean_ctor_get(v_v_2333_, 18);
v_one_x3f_2353_ = lean_ctor_get(v_v_2333_, 19);
v_leFn_x3f_2354_ = lean_ctor_get(v_v_2333_, 20);
v_ltFn_x3f_2355_ = lean_ctor_get(v_v_2333_, 21);
v_addFn_2356_ = lean_ctor_get(v_v_2333_, 22);
v_zsmulFn_2357_ = lean_ctor_get(v_v_2333_, 23);
v_nsmulFn_2358_ = lean_ctor_get(v_v_2333_, 24);
v_zsmulFn_x3f_2359_ = lean_ctor_get(v_v_2333_, 25);
v_nsmulFn_x3f_2360_ = lean_ctor_get(v_v_2333_, 26);
v_homomulFn_x3f_2361_ = lean_ctor_get(v_v_2333_, 27);
v_subFn_2362_ = lean_ctor_get(v_v_2333_, 28);
v_negFn_2363_ = lean_ctor_get(v_v_2333_, 29);
v_vars_2364_ = lean_ctor_get(v_v_2333_, 30);
v_varMap_2365_ = lean_ctor_get(v_v_2333_, 31);
v_lowers_2366_ = lean_ctor_get(v_v_2333_, 32);
v_uppers_2367_ = lean_ctor_get(v_v_2333_, 33);
v_diseqs_2368_ = lean_ctor_get(v_v_2333_, 34);
v_assignment_2369_ = lean_ctor_get(v_v_2333_, 35);
v_caseSplits_2370_ = lean_ctor_get_uint8(v_v_2333_, sizeof(void*)*42);
v_conflict_x3f_2371_ = lean_ctor_get(v_v_2333_, 36);
v_diseqSplits_2372_ = lean_ctor_get(v_v_2333_, 37);
v_elimEqs_2373_ = lean_ctor_get(v_v_2333_, 38);
v_elimStack_2374_ = lean_ctor_get(v_v_2333_, 39);
v_occurs_2375_ = lean_ctor_get(v_v_2333_, 40);
v_ignored_2376_ = lean_ctor_get(v_v_2333_, 41);
v_isSharedCheck_2390_ = !lean_is_exclusive(v_v_2333_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2378_ = v_v_2333_;
v_isShared_2379_ = v_isSharedCheck_2390_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_ignored_2376_);
lean_inc(v_occurs_2375_);
lean_inc(v_elimStack_2374_);
lean_inc(v_elimEqs_2373_);
lean_inc(v_diseqSplits_2372_);
lean_inc(v_conflict_x3f_2371_);
lean_inc(v_assignment_2369_);
lean_inc(v_diseqs_2368_);
lean_inc(v_uppers_2367_);
lean_inc(v_lowers_2366_);
lean_inc(v_varMap_2365_);
lean_inc(v_vars_2364_);
lean_inc(v_negFn_2363_);
lean_inc(v_subFn_2362_);
lean_inc(v_homomulFn_x3f_2361_);
lean_inc(v_nsmulFn_x3f_2360_);
lean_inc(v_zsmulFn_x3f_2359_);
lean_inc(v_nsmulFn_2358_);
lean_inc(v_zsmulFn_2357_);
lean_inc(v_addFn_2356_);
lean_inc(v_ltFn_x3f_2355_);
lean_inc(v_leFn_x3f_2354_);
lean_inc(v_one_x3f_2353_);
lean_inc(v_ofNatZero_2352_);
lean_inc(v_zero_2351_);
lean_inc(v_charInst_x3f_2350_);
lean_inc(v_fieldInst_x3f_2349_);
lean_inc(v_orderedRingInst_x3f_2348_);
lean_inc(v_commRingInst_x3f_2347_);
lean_inc(v_ringInst_x3f_2346_);
lean_inc(v_noNatDivInst_x3f_2345_);
lean_inc(v_isLinearInst_x3f_2344_);
lean_inc(v_orderedAddInst_x3f_2343_);
lean_inc(v_isPreorderInst_x3f_2342_);
lean_inc(v_lawfulOrderLTInst_x3f_2341_);
lean_inc(v_ltInst_x3f_2340_);
lean_inc(v_leInst_x3f_2339_);
lean_inc(v_intModuleInst_2338_);
lean_inc(v_u_2337_);
lean_inc(v_type_2336_);
lean_inc(v_ringId_x3f_2335_);
lean_inc(v_id_2334_);
lean_dec(v_v_2333_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2390_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; lean_object* v_xs_x27_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
v___x_2380_ = lean_box(0);
v_xs_x27_2381_ = lean_array_fset(v_structs_2320_, v_a_2316_, v___x_2380_);
v___x_2382_ = l_Lean_PersistentArray_set___redArg(v_lowers_2366_, v_y_2317_, v_fst_2318_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 32, v___x_2382_);
v___x_2384_ = v___x_2378_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_id_2334_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_ringId_x3f_2335_);
lean_ctor_set(v_reuseFailAlloc_2389_, 2, v_type_2336_);
lean_ctor_set(v_reuseFailAlloc_2389_, 3, v_u_2337_);
lean_ctor_set(v_reuseFailAlloc_2389_, 4, v_intModuleInst_2338_);
lean_ctor_set(v_reuseFailAlloc_2389_, 5, v_leInst_x3f_2339_);
lean_ctor_set(v_reuseFailAlloc_2389_, 6, v_ltInst_x3f_2340_);
lean_ctor_set(v_reuseFailAlloc_2389_, 7, v_lawfulOrderLTInst_x3f_2341_);
lean_ctor_set(v_reuseFailAlloc_2389_, 8, v_isPreorderInst_x3f_2342_);
lean_ctor_set(v_reuseFailAlloc_2389_, 9, v_orderedAddInst_x3f_2343_);
lean_ctor_set(v_reuseFailAlloc_2389_, 10, v_isLinearInst_x3f_2344_);
lean_ctor_set(v_reuseFailAlloc_2389_, 11, v_noNatDivInst_x3f_2345_);
lean_ctor_set(v_reuseFailAlloc_2389_, 12, v_ringInst_x3f_2346_);
lean_ctor_set(v_reuseFailAlloc_2389_, 13, v_commRingInst_x3f_2347_);
lean_ctor_set(v_reuseFailAlloc_2389_, 14, v_orderedRingInst_x3f_2348_);
lean_ctor_set(v_reuseFailAlloc_2389_, 15, v_fieldInst_x3f_2349_);
lean_ctor_set(v_reuseFailAlloc_2389_, 16, v_charInst_x3f_2350_);
lean_ctor_set(v_reuseFailAlloc_2389_, 17, v_zero_2351_);
lean_ctor_set(v_reuseFailAlloc_2389_, 18, v_ofNatZero_2352_);
lean_ctor_set(v_reuseFailAlloc_2389_, 19, v_one_x3f_2353_);
lean_ctor_set(v_reuseFailAlloc_2389_, 20, v_leFn_x3f_2354_);
lean_ctor_set(v_reuseFailAlloc_2389_, 21, v_ltFn_x3f_2355_);
lean_ctor_set(v_reuseFailAlloc_2389_, 22, v_addFn_2356_);
lean_ctor_set(v_reuseFailAlloc_2389_, 23, v_zsmulFn_2357_);
lean_ctor_set(v_reuseFailAlloc_2389_, 24, v_nsmulFn_2358_);
lean_ctor_set(v_reuseFailAlloc_2389_, 25, v_zsmulFn_x3f_2359_);
lean_ctor_set(v_reuseFailAlloc_2389_, 26, v_nsmulFn_x3f_2360_);
lean_ctor_set(v_reuseFailAlloc_2389_, 27, v_homomulFn_x3f_2361_);
lean_ctor_set(v_reuseFailAlloc_2389_, 28, v_subFn_2362_);
lean_ctor_set(v_reuseFailAlloc_2389_, 29, v_negFn_2363_);
lean_ctor_set(v_reuseFailAlloc_2389_, 30, v_vars_2364_);
lean_ctor_set(v_reuseFailAlloc_2389_, 31, v_varMap_2365_);
lean_ctor_set(v_reuseFailAlloc_2389_, 32, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2389_, 33, v_uppers_2367_);
lean_ctor_set(v_reuseFailAlloc_2389_, 34, v_diseqs_2368_);
lean_ctor_set(v_reuseFailAlloc_2389_, 35, v_assignment_2369_);
lean_ctor_set(v_reuseFailAlloc_2389_, 36, v_conflict_x3f_2371_);
lean_ctor_set(v_reuseFailAlloc_2389_, 37, v_diseqSplits_2372_);
lean_ctor_set(v_reuseFailAlloc_2389_, 38, v_elimEqs_2373_);
lean_ctor_set(v_reuseFailAlloc_2389_, 39, v_elimStack_2374_);
lean_ctor_set(v_reuseFailAlloc_2389_, 40, v_occurs_2375_);
lean_ctor_set(v_reuseFailAlloc_2389_, 41, v_ignored_2376_);
lean_ctor_set_uint8(v_reuseFailAlloc_2389_, sizeof(void*)*42, v_caseSplits_2370_);
v___x_2384_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_2385_; lean_object* v___x_2387_; 
v___x_2385_ = lean_array_fset(v_xs_x27_2381_, v_a_2316_, v___x_2384_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 0, v___x_2385_);
v___x_2387_ = v___x_2331_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_typeIdOf_2321_);
lean_ctor_set(v_reuseFailAlloc_2388_, 2, v_exprToStructId_2322_);
lean_ctor_set(v_reuseFailAlloc_2388_, 3, v_exprToStructIdEntries_2323_);
lean_ctor_set(v_reuseFailAlloc_2388_, 4, v_forbiddenNatModules_2324_);
lean_ctor_set(v_reuseFailAlloc_2388_, 5, v_natStructs_2325_);
lean_ctor_set(v_reuseFailAlloc_2388_, 6, v_natTypeIdOf_2326_);
lean_ctor_set(v_reuseFailAlloc_2388_, 7, v_exprToNatStructId_2327_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed(lean_object* v_a_2400_, lean_object* v_y_2401_, lean_object* v_fst_2402_, lean_object* v_s_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(v_a_2400_, v_y_2401_, v_fst_2402_, v_s_2403_);
lean_dec(v_y_2401_);
lean_dec(v_a_2400_);
return v_res_2404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0(void){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object* v_a_2406_, lean_object* v_x_2407_, lean_object* v_c_2408_, lean_object* v_y_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2423_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2457_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2426_ = v___x_2423_;
v_isShared_2427_ = v_isSharedCheck_2457_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2457_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
uint8_t v___x_2428_; 
v___x_2428_ = lean_unbox(v_a_2424_);
lean_dec(v_a_2424_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; 
lean_del_object(v___x_2426_);
v___x_2429_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___y_2432_; lean_object* v_lowers_2440_; lean_object* v_size_2441_; uint8_t v___x_2442_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2429_, 1);
v_lowers_2440_ = lean_ctor_get(v_a_2430_, 32);
lean_inc_ref(v_lowers_2440_);
lean_dec(v_a_2430_);
v_size_2441_ = lean_ctor_get(v_lowers_2440_, 2);
v___x_2442_ = lean_nat_dec_lt(v_y_2409_, v_size_2441_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; 
lean_dec_ref(v_lowers_2440_);
v___x_2443_ = l_outOfBounds___redArg(v___x_2422_);
v___y_2432_ = v___x_2443_;
goto v___jp_2431_;
}
else
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2422_, v_lowers_2440_, v_y_2409_);
lean_dec_ref(v_lowers_2440_);
v___y_2432_ = v___x_2444_;
goto v___jp_2431_;
}
v___jp_2431_:
{
lean_object* v___x_2433_; lean_object* v_fst_2434_; lean_object* v_snd_2435_; lean_object* v___f_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2433_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2407_, v___y_2432_);
lean_dec_ref(v___y_2432_);
v_fst_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_fst_2434_);
v_snd_2435_ = lean_ctor_get(v___x_2433_, 1);
lean_inc(v_snd_2435_);
lean_dec_ref(v___x_2433_);
lean_inc(v_a_2410_);
v___f_2436_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2436_, 0, v_a_2410_);
lean_closure_set(v___f_2436_, 1, v_y_2409_);
lean_closure_set(v___f_2436_, 2, v_fst_2434_);
v___x_2437_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2438_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2437_, v___f_2436_, v_a_2411_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v___x_2439_; 
lean_dec_ref_known(v___x_2438_, 1);
v___x_2439_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2406_, v_x_2407_, v_c_2408_, v_snd_2435_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
lean_dec(v_snd_2435_);
return v___x_2439_;
}
else
{
lean_dec(v_snd_2435_);
lean_dec_ref(v_c_2408_);
lean_dec(v_x_2407_);
lean_dec(v_a_2406_);
return v___x_2438_;
}
}
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_dec(v_y_2409_);
lean_dec_ref(v_c_2408_);
lean_dec(v_x_2407_);
lean_dec(v_a_2406_);
v_a_2445_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2429_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2429_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
else
{
lean_object* v___x_2453_; lean_object* v___x_2455_; 
lean_dec(v_y_2409_);
lean_dec_ref(v_c_2408_);
lean_dec(v_x_2407_);
lean_dec(v_a_2406_);
v___x_2453_ = lean_box(0);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2453_);
v___x_2455_ = v___x_2426_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
lean_dec(v_y_2409_);
lean_dec_ref(v_c_2408_);
lean_dec(v_x_2407_);
lean_dec(v_a_2406_);
v_a_2458_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2423_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2423_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object* v_a_2466_, lean_object* v_x_2467_, lean_object* v_c_2468_, lean_object* v_y_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_2466_, v_x_2467_, v_c_2468_, v_y_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
lean_dec(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec(v_a_2470_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(lean_object* v_a_2483_, lean_object* v_y_2484_, lean_object* v_fst_2485_, lean_object* v_s_2486_){
_start:
{
lean_object* v_structs_2487_; lean_object* v_typeIdOf_2488_; lean_object* v_exprToStructId_2489_; lean_object* v_exprToStructIdEntries_2490_; lean_object* v_forbiddenNatModules_2491_; lean_object* v_natStructs_2492_; lean_object* v_natTypeIdOf_2493_; lean_object* v_exprToNatStructId_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; 
v_structs_2487_ = lean_ctor_get(v_s_2486_, 0);
v_typeIdOf_2488_ = lean_ctor_get(v_s_2486_, 1);
v_exprToStructId_2489_ = lean_ctor_get(v_s_2486_, 2);
v_exprToStructIdEntries_2490_ = lean_ctor_get(v_s_2486_, 3);
v_forbiddenNatModules_2491_ = lean_ctor_get(v_s_2486_, 4);
v_natStructs_2492_ = lean_ctor_get(v_s_2486_, 5);
v_natTypeIdOf_2493_ = lean_ctor_get(v_s_2486_, 6);
v_exprToNatStructId_2494_ = lean_ctor_get(v_s_2486_, 7);
v___x_2495_ = lean_array_get_size(v_structs_2487_);
v___x_2496_ = lean_nat_dec_lt(v_a_2483_, v___x_2495_);
if (v___x_2496_ == 0)
{
lean_dec_ref(v_fst_2485_);
return v_s_2486_;
}
else
{
lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2558_; 
lean_inc_ref(v_exprToNatStructId_2494_);
lean_inc_ref(v_natTypeIdOf_2493_);
lean_inc_ref(v_natStructs_2492_);
lean_inc_ref(v_forbiddenNatModules_2491_);
lean_inc_ref(v_exprToStructIdEntries_2490_);
lean_inc_ref(v_exprToStructId_2489_);
lean_inc_ref(v_typeIdOf_2488_);
lean_inc_ref(v_structs_2487_);
v_isSharedCheck_2558_ = !lean_is_exclusive(v_s_2486_);
if (v_isSharedCheck_2558_ == 0)
{
lean_object* v_unused_2559_; lean_object* v_unused_2560_; lean_object* v_unused_2561_; lean_object* v_unused_2562_; lean_object* v_unused_2563_; lean_object* v_unused_2564_; lean_object* v_unused_2565_; lean_object* v_unused_2566_; 
v_unused_2559_ = lean_ctor_get(v_s_2486_, 7);
lean_dec(v_unused_2559_);
v_unused_2560_ = lean_ctor_get(v_s_2486_, 6);
lean_dec(v_unused_2560_);
v_unused_2561_ = lean_ctor_get(v_s_2486_, 5);
lean_dec(v_unused_2561_);
v_unused_2562_ = lean_ctor_get(v_s_2486_, 4);
lean_dec(v_unused_2562_);
v_unused_2563_ = lean_ctor_get(v_s_2486_, 3);
lean_dec(v_unused_2563_);
v_unused_2564_ = lean_ctor_get(v_s_2486_, 2);
lean_dec(v_unused_2564_);
v_unused_2565_ = lean_ctor_get(v_s_2486_, 1);
lean_dec(v_unused_2565_);
v_unused_2566_ = lean_ctor_get(v_s_2486_, 0);
lean_dec(v_unused_2566_);
v___x_2498_ = v_s_2486_;
v_isShared_2499_ = v_isSharedCheck_2558_;
goto v_resetjp_2497_;
}
else
{
lean_dec(v_s_2486_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2558_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v_v_2500_; lean_object* v_id_2501_; lean_object* v_ringId_x3f_2502_; lean_object* v_type_2503_; lean_object* v_u_2504_; lean_object* v_intModuleInst_2505_; lean_object* v_leInst_x3f_2506_; lean_object* v_ltInst_x3f_2507_; lean_object* v_lawfulOrderLTInst_x3f_2508_; lean_object* v_isPreorderInst_x3f_2509_; lean_object* v_orderedAddInst_x3f_2510_; lean_object* v_isLinearInst_x3f_2511_; lean_object* v_noNatDivInst_x3f_2512_; lean_object* v_ringInst_x3f_2513_; lean_object* v_commRingInst_x3f_2514_; lean_object* v_orderedRingInst_x3f_2515_; lean_object* v_fieldInst_x3f_2516_; lean_object* v_charInst_x3f_2517_; lean_object* v_zero_2518_; lean_object* v_ofNatZero_2519_; lean_object* v_one_x3f_2520_; lean_object* v_leFn_x3f_2521_; lean_object* v_ltFn_x3f_2522_; lean_object* v_addFn_2523_; lean_object* v_zsmulFn_2524_; lean_object* v_nsmulFn_2525_; lean_object* v_zsmulFn_x3f_2526_; lean_object* v_nsmulFn_x3f_2527_; lean_object* v_homomulFn_x3f_2528_; lean_object* v_subFn_2529_; lean_object* v_negFn_2530_; lean_object* v_vars_2531_; lean_object* v_varMap_2532_; lean_object* v_lowers_2533_; lean_object* v_uppers_2534_; lean_object* v_diseqs_2535_; lean_object* v_assignment_2536_; uint8_t v_caseSplits_2537_; lean_object* v_conflict_x3f_2538_; lean_object* v_diseqSplits_2539_; lean_object* v_elimEqs_2540_; lean_object* v_elimStack_2541_; lean_object* v_occurs_2542_; lean_object* v_ignored_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2557_; 
v_v_2500_ = lean_array_fget(v_structs_2487_, v_a_2483_);
v_id_2501_ = lean_ctor_get(v_v_2500_, 0);
v_ringId_x3f_2502_ = lean_ctor_get(v_v_2500_, 1);
v_type_2503_ = lean_ctor_get(v_v_2500_, 2);
v_u_2504_ = lean_ctor_get(v_v_2500_, 3);
v_intModuleInst_2505_ = lean_ctor_get(v_v_2500_, 4);
v_leInst_x3f_2506_ = lean_ctor_get(v_v_2500_, 5);
v_ltInst_x3f_2507_ = lean_ctor_get(v_v_2500_, 6);
v_lawfulOrderLTInst_x3f_2508_ = lean_ctor_get(v_v_2500_, 7);
v_isPreorderInst_x3f_2509_ = lean_ctor_get(v_v_2500_, 8);
v_orderedAddInst_x3f_2510_ = lean_ctor_get(v_v_2500_, 9);
v_isLinearInst_x3f_2511_ = lean_ctor_get(v_v_2500_, 10);
v_noNatDivInst_x3f_2512_ = lean_ctor_get(v_v_2500_, 11);
v_ringInst_x3f_2513_ = lean_ctor_get(v_v_2500_, 12);
v_commRingInst_x3f_2514_ = lean_ctor_get(v_v_2500_, 13);
v_orderedRingInst_x3f_2515_ = lean_ctor_get(v_v_2500_, 14);
v_fieldInst_x3f_2516_ = lean_ctor_get(v_v_2500_, 15);
v_charInst_x3f_2517_ = lean_ctor_get(v_v_2500_, 16);
v_zero_2518_ = lean_ctor_get(v_v_2500_, 17);
v_ofNatZero_2519_ = lean_ctor_get(v_v_2500_, 18);
v_one_x3f_2520_ = lean_ctor_get(v_v_2500_, 19);
v_leFn_x3f_2521_ = lean_ctor_get(v_v_2500_, 20);
v_ltFn_x3f_2522_ = lean_ctor_get(v_v_2500_, 21);
v_addFn_2523_ = lean_ctor_get(v_v_2500_, 22);
v_zsmulFn_2524_ = lean_ctor_get(v_v_2500_, 23);
v_nsmulFn_2525_ = lean_ctor_get(v_v_2500_, 24);
v_zsmulFn_x3f_2526_ = lean_ctor_get(v_v_2500_, 25);
v_nsmulFn_x3f_2527_ = lean_ctor_get(v_v_2500_, 26);
v_homomulFn_x3f_2528_ = lean_ctor_get(v_v_2500_, 27);
v_subFn_2529_ = lean_ctor_get(v_v_2500_, 28);
v_negFn_2530_ = lean_ctor_get(v_v_2500_, 29);
v_vars_2531_ = lean_ctor_get(v_v_2500_, 30);
v_varMap_2532_ = lean_ctor_get(v_v_2500_, 31);
v_lowers_2533_ = lean_ctor_get(v_v_2500_, 32);
v_uppers_2534_ = lean_ctor_get(v_v_2500_, 33);
v_diseqs_2535_ = lean_ctor_get(v_v_2500_, 34);
v_assignment_2536_ = lean_ctor_get(v_v_2500_, 35);
v_caseSplits_2537_ = lean_ctor_get_uint8(v_v_2500_, sizeof(void*)*42);
v_conflict_x3f_2538_ = lean_ctor_get(v_v_2500_, 36);
v_diseqSplits_2539_ = lean_ctor_get(v_v_2500_, 37);
v_elimEqs_2540_ = lean_ctor_get(v_v_2500_, 38);
v_elimStack_2541_ = lean_ctor_get(v_v_2500_, 39);
v_occurs_2542_ = lean_ctor_get(v_v_2500_, 40);
v_ignored_2543_ = lean_ctor_get(v_v_2500_, 41);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_v_2500_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2545_ = v_v_2500_;
v_isShared_2546_ = v_isSharedCheck_2557_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_ignored_2543_);
lean_inc(v_occurs_2542_);
lean_inc(v_elimStack_2541_);
lean_inc(v_elimEqs_2540_);
lean_inc(v_diseqSplits_2539_);
lean_inc(v_conflict_x3f_2538_);
lean_inc(v_assignment_2536_);
lean_inc(v_diseqs_2535_);
lean_inc(v_uppers_2534_);
lean_inc(v_lowers_2533_);
lean_inc(v_varMap_2532_);
lean_inc(v_vars_2531_);
lean_inc(v_negFn_2530_);
lean_inc(v_subFn_2529_);
lean_inc(v_homomulFn_x3f_2528_);
lean_inc(v_nsmulFn_x3f_2527_);
lean_inc(v_zsmulFn_x3f_2526_);
lean_inc(v_nsmulFn_2525_);
lean_inc(v_zsmulFn_2524_);
lean_inc(v_addFn_2523_);
lean_inc(v_ltFn_x3f_2522_);
lean_inc(v_leFn_x3f_2521_);
lean_inc(v_one_x3f_2520_);
lean_inc(v_ofNatZero_2519_);
lean_inc(v_zero_2518_);
lean_inc(v_charInst_x3f_2517_);
lean_inc(v_fieldInst_x3f_2516_);
lean_inc(v_orderedRingInst_x3f_2515_);
lean_inc(v_commRingInst_x3f_2514_);
lean_inc(v_ringInst_x3f_2513_);
lean_inc(v_noNatDivInst_x3f_2512_);
lean_inc(v_isLinearInst_x3f_2511_);
lean_inc(v_orderedAddInst_x3f_2510_);
lean_inc(v_isPreorderInst_x3f_2509_);
lean_inc(v_lawfulOrderLTInst_x3f_2508_);
lean_inc(v_ltInst_x3f_2507_);
lean_inc(v_leInst_x3f_2506_);
lean_inc(v_intModuleInst_2505_);
lean_inc(v_u_2504_);
lean_inc(v_type_2503_);
lean_inc(v_ringId_x3f_2502_);
lean_inc(v_id_2501_);
lean_dec(v_v_2500_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2557_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2547_; lean_object* v_xs_x27_2548_; lean_object* v___x_2549_; lean_object* v___x_2551_; 
v___x_2547_ = lean_box(0);
v_xs_x27_2548_ = lean_array_fset(v_structs_2487_, v_a_2483_, v___x_2547_);
v___x_2549_ = l_Lean_PersistentArray_set___redArg(v_uppers_2534_, v_y_2484_, v_fst_2485_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 33, v___x_2549_);
v___x_2551_ = v___x_2545_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_id_2501_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v_ringId_x3f_2502_);
lean_ctor_set(v_reuseFailAlloc_2556_, 2, v_type_2503_);
lean_ctor_set(v_reuseFailAlloc_2556_, 3, v_u_2504_);
lean_ctor_set(v_reuseFailAlloc_2556_, 4, v_intModuleInst_2505_);
lean_ctor_set(v_reuseFailAlloc_2556_, 5, v_leInst_x3f_2506_);
lean_ctor_set(v_reuseFailAlloc_2556_, 6, v_ltInst_x3f_2507_);
lean_ctor_set(v_reuseFailAlloc_2556_, 7, v_lawfulOrderLTInst_x3f_2508_);
lean_ctor_set(v_reuseFailAlloc_2556_, 8, v_isPreorderInst_x3f_2509_);
lean_ctor_set(v_reuseFailAlloc_2556_, 9, v_orderedAddInst_x3f_2510_);
lean_ctor_set(v_reuseFailAlloc_2556_, 10, v_isLinearInst_x3f_2511_);
lean_ctor_set(v_reuseFailAlloc_2556_, 11, v_noNatDivInst_x3f_2512_);
lean_ctor_set(v_reuseFailAlloc_2556_, 12, v_ringInst_x3f_2513_);
lean_ctor_set(v_reuseFailAlloc_2556_, 13, v_commRingInst_x3f_2514_);
lean_ctor_set(v_reuseFailAlloc_2556_, 14, v_orderedRingInst_x3f_2515_);
lean_ctor_set(v_reuseFailAlloc_2556_, 15, v_fieldInst_x3f_2516_);
lean_ctor_set(v_reuseFailAlloc_2556_, 16, v_charInst_x3f_2517_);
lean_ctor_set(v_reuseFailAlloc_2556_, 17, v_zero_2518_);
lean_ctor_set(v_reuseFailAlloc_2556_, 18, v_ofNatZero_2519_);
lean_ctor_set(v_reuseFailAlloc_2556_, 19, v_one_x3f_2520_);
lean_ctor_set(v_reuseFailAlloc_2556_, 20, v_leFn_x3f_2521_);
lean_ctor_set(v_reuseFailAlloc_2556_, 21, v_ltFn_x3f_2522_);
lean_ctor_set(v_reuseFailAlloc_2556_, 22, v_addFn_2523_);
lean_ctor_set(v_reuseFailAlloc_2556_, 23, v_zsmulFn_2524_);
lean_ctor_set(v_reuseFailAlloc_2556_, 24, v_nsmulFn_2525_);
lean_ctor_set(v_reuseFailAlloc_2556_, 25, v_zsmulFn_x3f_2526_);
lean_ctor_set(v_reuseFailAlloc_2556_, 26, v_nsmulFn_x3f_2527_);
lean_ctor_set(v_reuseFailAlloc_2556_, 27, v_homomulFn_x3f_2528_);
lean_ctor_set(v_reuseFailAlloc_2556_, 28, v_subFn_2529_);
lean_ctor_set(v_reuseFailAlloc_2556_, 29, v_negFn_2530_);
lean_ctor_set(v_reuseFailAlloc_2556_, 30, v_vars_2531_);
lean_ctor_set(v_reuseFailAlloc_2556_, 31, v_varMap_2532_);
lean_ctor_set(v_reuseFailAlloc_2556_, 32, v_lowers_2533_);
lean_ctor_set(v_reuseFailAlloc_2556_, 33, v___x_2549_);
lean_ctor_set(v_reuseFailAlloc_2556_, 34, v_diseqs_2535_);
lean_ctor_set(v_reuseFailAlloc_2556_, 35, v_assignment_2536_);
lean_ctor_set(v_reuseFailAlloc_2556_, 36, v_conflict_x3f_2538_);
lean_ctor_set(v_reuseFailAlloc_2556_, 37, v_diseqSplits_2539_);
lean_ctor_set(v_reuseFailAlloc_2556_, 38, v_elimEqs_2540_);
lean_ctor_set(v_reuseFailAlloc_2556_, 39, v_elimStack_2541_);
lean_ctor_set(v_reuseFailAlloc_2556_, 40, v_occurs_2542_);
lean_ctor_set(v_reuseFailAlloc_2556_, 41, v_ignored_2543_);
lean_ctor_set_uint8(v_reuseFailAlloc_2556_, sizeof(void*)*42, v_caseSplits_2537_);
v___x_2551_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2552_; lean_object* v___x_2554_; 
v___x_2552_ = lean_array_fset(v_xs_x27_2548_, v_a_2483_, v___x_2551_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v___x_2552_);
v___x_2554_ = v___x_2498_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2552_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v_typeIdOf_2488_);
lean_ctor_set(v_reuseFailAlloc_2555_, 2, v_exprToStructId_2489_);
lean_ctor_set(v_reuseFailAlloc_2555_, 3, v_exprToStructIdEntries_2490_);
lean_ctor_set(v_reuseFailAlloc_2555_, 4, v_forbiddenNatModules_2491_);
lean_ctor_set(v_reuseFailAlloc_2555_, 5, v_natStructs_2492_);
lean_ctor_set(v_reuseFailAlloc_2555_, 6, v_natTypeIdOf_2493_);
lean_ctor_set(v_reuseFailAlloc_2555_, 7, v_exprToNatStructId_2494_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed(lean_object* v_a_2567_, lean_object* v_y_2568_, lean_object* v_fst_2569_, lean_object* v_s_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(v_a_2567_, v_y_2568_, v_fst_2569_, v_s_2570_);
lean_dec(v_y_2568_);
lean_dec(v_a_2567_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object* v_a_2572_, lean_object* v_x_2573_, lean_object* v_c_2574_, lean_object* v_y_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2589_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2623_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2592_ = v___x_2589_;
v_isShared_2593_ = v_isSharedCheck_2623_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2623_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
uint8_t v___x_2594_; 
v___x_2594_ = lean_unbox(v_a_2590_);
lean_dec(v_a_2590_);
if (v___x_2594_ == 0)
{
lean_object* v___x_2595_; 
lean_del_object(v___x_2592_);
v___x_2595_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___y_2598_; lean_object* v_uppers_2606_; lean_object* v_size_2607_; uint8_t v___x_2608_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
v_uppers_2606_ = lean_ctor_get(v_a_2596_, 33);
lean_inc_ref(v_uppers_2606_);
lean_dec(v_a_2596_);
v_size_2607_ = lean_ctor_get(v_uppers_2606_, 2);
v___x_2608_ = lean_nat_dec_lt(v_y_2575_, v_size_2607_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; 
lean_dec_ref(v_uppers_2606_);
v___x_2609_ = l_outOfBounds___redArg(v___x_2588_);
v___y_2598_ = v___x_2609_;
goto v___jp_2597_;
}
else
{
lean_object* v___x_2610_; 
v___x_2610_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2588_, v_uppers_2606_, v_y_2575_);
lean_dec_ref(v_uppers_2606_);
v___y_2598_ = v___x_2610_;
goto v___jp_2597_;
}
v___jp_2597_:
{
lean_object* v___x_2599_; lean_object* v_fst_2600_; lean_object* v_snd_2601_; lean_object* v___f_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2599_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2573_, v___y_2598_);
lean_dec_ref(v___y_2598_);
v_fst_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_fst_2600_);
v_snd_2601_ = lean_ctor_get(v___x_2599_, 1);
lean_inc(v_snd_2601_);
lean_dec_ref(v___x_2599_);
lean_inc(v_a_2576_);
v___f_2602_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2602_, 0, v_a_2576_);
lean_closure_set(v___f_2602_, 1, v_y_2575_);
lean_closure_set(v___f_2602_, 2, v_fst_2600_);
v___x_2603_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2604_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2603_, v___f_2602_, v_a_2577_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v___x_2605_; 
lean_dec_ref_known(v___x_2604_, 1);
v___x_2605_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2572_, v_x_2573_, v_c_2574_, v_snd_2601_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
lean_dec(v_snd_2601_);
return v___x_2605_;
}
else
{
lean_dec(v_snd_2601_);
lean_dec_ref(v_c_2574_);
lean_dec(v_x_2573_);
lean_dec(v_a_2572_);
return v___x_2604_;
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_dec(v_y_2575_);
lean_dec_ref(v_c_2574_);
lean_dec(v_x_2573_);
lean_dec(v_a_2572_);
v_a_2611_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2595_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2595_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
else
{
lean_object* v___x_2619_; lean_object* v___x_2621_; 
lean_dec(v_y_2575_);
lean_dec_ref(v_c_2574_);
lean_dec(v_x_2573_);
lean_dec(v_a_2572_);
v___x_2619_ = lean_box(0);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 0, v___x_2619_);
v___x_2621_ = v___x_2592_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec(v_y_2575_);
lean_dec_ref(v_c_2574_);
lean_dec(v_x_2573_);
lean_dec(v_a_2572_);
v_a_2624_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2589_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2589_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object* v_a_2632_, lean_object* v_x_2633_, lean_object* v_c_2634_, lean_object* v_y_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_2632_, v_x_2633_, v_c_2634_, v_y_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec(v_a_2640_);
lean_dec_ref(v_a_2639_);
lean_dec(v_a_2638_);
lean_dec(v_a_2637_);
lean_dec(v_a_2636_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(lean_object* v___y_2649_, lean_object* v_a_2650_, lean_object* v_s_2651_){
_start:
{
lean_object* v_structs_2652_; lean_object* v_typeIdOf_2653_; lean_object* v_exprToStructId_2654_; lean_object* v_exprToStructIdEntries_2655_; lean_object* v_forbiddenNatModules_2656_; lean_object* v_natStructs_2657_; lean_object* v_natTypeIdOf_2658_; lean_object* v_exprToNatStructId_2659_; lean_object* v___x_2660_; uint8_t v___x_2661_; 
v_structs_2652_ = lean_ctor_get(v_s_2651_, 0);
v_typeIdOf_2653_ = lean_ctor_get(v_s_2651_, 1);
v_exprToStructId_2654_ = lean_ctor_get(v_s_2651_, 2);
v_exprToStructIdEntries_2655_ = lean_ctor_get(v_s_2651_, 3);
v_forbiddenNatModules_2656_ = lean_ctor_get(v_s_2651_, 4);
v_natStructs_2657_ = lean_ctor_get(v_s_2651_, 5);
v_natTypeIdOf_2658_ = lean_ctor_get(v_s_2651_, 6);
v_exprToNatStructId_2659_ = lean_ctor_get(v_s_2651_, 7);
v___x_2660_ = lean_array_get_size(v_structs_2652_);
v___x_2661_ = lean_nat_dec_lt(v___y_2649_, v___x_2660_);
if (v___x_2661_ == 0)
{
lean_dec_ref(v_a_2650_);
return v_s_2651_;
}
else
{
lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2723_; 
lean_inc_ref(v_exprToNatStructId_2659_);
lean_inc_ref(v_natTypeIdOf_2658_);
lean_inc_ref(v_natStructs_2657_);
lean_inc_ref(v_forbiddenNatModules_2656_);
lean_inc_ref(v_exprToStructIdEntries_2655_);
lean_inc_ref(v_exprToStructId_2654_);
lean_inc_ref(v_typeIdOf_2653_);
lean_inc_ref(v_structs_2652_);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_s_2651_);
if (v_isSharedCheck_2723_ == 0)
{
lean_object* v_unused_2724_; lean_object* v_unused_2725_; lean_object* v_unused_2726_; lean_object* v_unused_2727_; lean_object* v_unused_2728_; lean_object* v_unused_2729_; lean_object* v_unused_2730_; lean_object* v_unused_2731_; 
v_unused_2724_ = lean_ctor_get(v_s_2651_, 7);
lean_dec(v_unused_2724_);
v_unused_2725_ = lean_ctor_get(v_s_2651_, 6);
lean_dec(v_unused_2725_);
v_unused_2726_ = lean_ctor_get(v_s_2651_, 5);
lean_dec(v_unused_2726_);
v_unused_2727_ = lean_ctor_get(v_s_2651_, 4);
lean_dec(v_unused_2727_);
v_unused_2728_ = lean_ctor_get(v_s_2651_, 3);
lean_dec(v_unused_2728_);
v_unused_2729_ = lean_ctor_get(v_s_2651_, 2);
lean_dec(v_unused_2729_);
v_unused_2730_ = lean_ctor_get(v_s_2651_, 1);
lean_dec(v_unused_2730_);
v_unused_2731_ = lean_ctor_get(v_s_2651_, 0);
lean_dec(v_unused_2731_);
v___x_2663_ = v_s_2651_;
v_isShared_2664_ = v_isSharedCheck_2723_;
goto v_resetjp_2662_;
}
else
{
lean_dec(v_s_2651_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2723_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v_v_2665_; lean_object* v_id_2666_; lean_object* v_ringId_x3f_2667_; lean_object* v_type_2668_; lean_object* v_u_2669_; lean_object* v_intModuleInst_2670_; lean_object* v_leInst_x3f_2671_; lean_object* v_ltInst_x3f_2672_; lean_object* v_lawfulOrderLTInst_x3f_2673_; lean_object* v_isPreorderInst_x3f_2674_; lean_object* v_orderedAddInst_x3f_2675_; lean_object* v_isLinearInst_x3f_2676_; lean_object* v_noNatDivInst_x3f_2677_; lean_object* v_ringInst_x3f_2678_; lean_object* v_commRingInst_x3f_2679_; lean_object* v_orderedRingInst_x3f_2680_; lean_object* v_fieldInst_x3f_2681_; lean_object* v_charInst_x3f_2682_; lean_object* v_zero_2683_; lean_object* v_ofNatZero_2684_; lean_object* v_one_x3f_2685_; lean_object* v_leFn_x3f_2686_; lean_object* v_ltFn_x3f_2687_; lean_object* v_addFn_2688_; lean_object* v_zsmulFn_2689_; lean_object* v_nsmulFn_2690_; lean_object* v_zsmulFn_x3f_2691_; lean_object* v_nsmulFn_x3f_2692_; lean_object* v_homomulFn_x3f_2693_; lean_object* v_subFn_2694_; lean_object* v_negFn_2695_; lean_object* v_vars_2696_; lean_object* v_varMap_2697_; lean_object* v_lowers_2698_; lean_object* v_uppers_2699_; lean_object* v_diseqs_2700_; lean_object* v_assignment_2701_; uint8_t v_caseSplits_2702_; lean_object* v_conflict_x3f_2703_; lean_object* v_diseqSplits_2704_; lean_object* v_elimEqs_2705_; lean_object* v_elimStack_2706_; lean_object* v_occurs_2707_; lean_object* v_ignored_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2722_; 
v_v_2665_ = lean_array_fget(v_structs_2652_, v___y_2649_);
v_id_2666_ = lean_ctor_get(v_v_2665_, 0);
v_ringId_x3f_2667_ = lean_ctor_get(v_v_2665_, 1);
v_type_2668_ = lean_ctor_get(v_v_2665_, 2);
v_u_2669_ = lean_ctor_get(v_v_2665_, 3);
v_intModuleInst_2670_ = lean_ctor_get(v_v_2665_, 4);
v_leInst_x3f_2671_ = lean_ctor_get(v_v_2665_, 5);
v_ltInst_x3f_2672_ = lean_ctor_get(v_v_2665_, 6);
v_lawfulOrderLTInst_x3f_2673_ = lean_ctor_get(v_v_2665_, 7);
v_isPreorderInst_x3f_2674_ = lean_ctor_get(v_v_2665_, 8);
v_orderedAddInst_x3f_2675_ = lean_ctor_get(v_v_2665_, 9);
v_isLinearInst_x3f_2676_ = lean_ctor_get(v_v_2665_, 10);
v_noNatDivInst_x3f_2677_ = lean_ctor_get(v_v_2665_, 11);
v_ringInst_x3f_2678_ = lean_ctor_get(v_v_2665_, 12);
v_commRingInst_x3f_2679_ = lean_ctor_get(v_v_2665_, 13);
v_orderedRingInst_x3f_2680_ = lean_ctor_get(v_v_2665_, 14);
v_fieldInst_x3f_2681_ = lean_ctor_get(v_v_2665_, 15);
v_charInst_x3f_2682_ = lean_ctor_get(v_v_2665_, 16);
v_zero_2683_ = lean_ctor_get(v_v_2665_, 17);
v_ofNatZero_2684_ = lean_ctor_get(v_v_2665_, 18);
v_one_x3f_2685_ = lean_ctor_get(v_v_2665_, 19);
v_leFn_x3f_2686_ = lean_ctor_get(v_v_2665_, 20);
v_ltFn_x3f_2687_ = lean_ctor_get(v_v_2665_, 21);
v_addFn_2688_ = lean_ctor_get(v_v_2665_, 22);
v_zsmulFn_2689_ = lean_ctor_get(v_v_2665_, 23);
v_nsmulFn_2690_ = lean_ctor_get(v_v_2665_, 24);
v_zsmulFn_x3f_2691_ = lean_ctor_get(v_v_2665_, 25);
v_nsmulFn_x3f_2692_ = lean_ctor_get(v_v_2665_, 26);
v_homomulFn_x3f_2693_ = lean_ctor_get(v_v_2665_, 27);
v_subFn_2694_ = lean_ctor_get(v_v_2665_, 28);
v_negFn_2695_ = lean_ctor_get(v_v_2665_, 29);
v_vars_2696_ = lean_ctor_get(v_v_2665_, 30);
v_varMap_2697_ = lean_ctor_get(v_v_2665_, 31);
v_lowers_2698_ = lean_ctor_get(v_v_2665_, 32);
v_uppers_2699_ = lean_ctor_get(v_v_2665_, 33);
v_diseqs_2700_ = lean_ctor_get(v_v_2665_, 34);
v_assignment_2701_ = lean_ctor_get(v_v_2665_, 35);
v_caseSplits_2702_ = lean_ctor_get_uint8(v_v_2665_, sizeof(void*)*42);
v_conflict_x3f_2703_ = lean_ctor_get(v_v_2665_, 36);
v_diseqSplits_2704_ = lean_ctor_get(v_v_2665_, 37);
v_elimEqs_2705_ = lean_ctor_get(v_v_2665_, 38);
v_elimStack_2706_ = lean_ctor_get(v_v_2665_, 39);
v_occurs_2707_ = lean_ctor_get(v_v_2665_, 40);
v_ignored_2708_ = lean_ctor_get(v_v_2665_, 41);
v_isSharedCheck_2722_ = !lean_is_exclusive(v_v_2665_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2710_ = v_v_2665_;
v_isShared_2711_ = v_isSharedCheck_2722_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_ignored_2708_);
lean_inc(v_occurs_2707_);
lean_inc(v_elimStack_2706_);
lean_inc(v_elimEqs_2705_);
lean_inc(v_diseqSplits_2704_);
lean_inc(v_conflict_x3f_2703_);
lean_inc(v_assignment_2701_);
lean_inc(v_diseqs_2700_);
lean_inc(v_uppers_2699_);
lean_inc(v_lowers_2698_);
lean_inc(v_varMap_2697_);
lean_inc(v_vars_2696_);
lean_inc(v_negFn_2695_);
lean_inc(v_subFn_2694_);
lean_inc(v_homomulFn_x3f_2693_);
lean_inc(v_nsmulFn_x3f_2692_);
lean_inc(v_zsmulFn_x3f_2691_);
lean_inc(v_nsmulFn_2690_);
lean_inc(v_zsmulFn_2689_);
lean_inc(v_addFn_2688_);
lean_inc(v_ltFn_x3f_2687_);
lean_inc(v_leFn_x3f_2686_);
lean_inc(v_one_x3f_2685_);
lean_inc(v_ofNatZero_2684_);
lean_inc(v_zero_2683_);
lean_inc(v_charInst_x3f_2682_);
lean_inc(v_fieldInst_x3f_2681_);
lean_inc(v_orderedRingInst_x3f_2680_);
lean_inc(v_commRingInst_x3f_2679_);
lean_inc(v_ringInst_x3f_2678_);
lean_inc(v_noNatDivInst_x3f_2677_);
lean_inc(v_isLinearInst_x3f_2676_);
lean_inc(v_orderedAddInst_x3f_2675_);
lean_inc(v_isPreorderInst_x3f_2674_);
lean_inc(v_lawfulOrderLTInst_x3f_2673_);
lean_inc(v_ltInst_x3f_2672_);
lean_inc(v_leInst_x3f_2671_);
lean_inc(v_intModuleInst_2670_);
lean_inc(v_u_2669_);
lean_inc(v_type_2668_);
lean_inc(v_ringId_x3f_2667_);
lean_inc(v_id_2666_);
lean_dec(v_v_2665_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2722_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2712_; lean_object* v_xs_x27_2713_; lean_object* v___x_2714_; lean_object* v___x_2716_; 
v___x_2712_ = lean_box(0);
v_xs_x27_2713_ = lean_array_fset(v_structs_2652_, v___y_2649_, v___x_2712_);
v___x_2714_ = l_Lean_PersistentArray_push___redArg(v_ignored_2708_, v_a_2650_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 41, v___x_2714_);
v___x_2716_ = v___x_2710_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_id_2666_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v_ringId_x3f_2667_);
lean_ctor_set(v_reuseFailAlloc_2721_, 2, v_type_2668_);
lean_ctor_set(v_reuseFailAlloc_2721_, 3, v_u_2669_);
lean_ctor_set(v_reuseFailAlloc_2721_, 4, v_intModuleInst_2670_);
lean_ctor_set(v_reuseFailAlloc_2721_, 5, v_leInst_x3f_2671_);
lean_ctor_set(v_reuseFailAlloc_2721_, 6, v_ltInst_x3f_2672_);
lean_ctor_set(v_reuseFailAlloc_2721_, 7, v_lawfulOrderLTInst_x3f_2673_);
lean_ctor_set(v_reuseFailAlloc_2721_, 8, v_isPreorderInst_x3f_2674_);
lean_ctor_set(v_reuseFailAlloc_2721_, 9, v_orderedAddInst_x3f_2675_);
lean_ctor_set(v_reuseFailAlloc_2721_, 10, v_isLinearInst_x3f_2676_);
lean_ctor_set(v_reuseFailAlloc_2721_, 11, v_noNatDivInst_x3f_2677_);
lean_ctor_set(v_reuseFailAlloc_2721_, 12, v_ringInst_x3f_2678_);
lean_ctor_set(v_reuseFailAlloc_2721_, 13, v_commRingInst_x3f_2679_);
lean_ctor_set(v_reuseFailAlloc_2721_, 14, v_orderedRingInst_x3f_2680_);
lean_ctor_set(v_reuseFailAlloc_2721_, 15, v_fieldInst_x3f_2681_);
lean_ctor_set(v_reuseFailAlloc_2721_, 16, v_charInst_x3f_2682_);
lean_ctor_set(v_reuseFailAlloc_2721_, 17, v_zero_2683_);
lean_ctor_set(v_reuseFailAlloc_2721_, 18, v_ofNatZero_2684_);
lean_ctor_set(v_reuseFailAlloc_2721_, 19, v_one_x3f_2685_);
lean_ctor_set(v_reuseFailAlloc_2721_, 20, v_leFn_x3f_2686_);
lean_ctor_set(v_reuseFailAlloc_2721_, 21, v_ltFn_x3f_2687_);
lean_ctor_set(v_reuseFailAlloc_2721_, 22, v_addFn_2688_);
lean_ctor_set(v_reuseFailAlloc_2721_, 23, v_zsmulFn_2689_);
lean_ctor_set(v_reuseFailAlloc_2721_, 24, v_nsmulFn_2690_);
lean_ctor_set(v_reuseFailAlloc_2721_, 25, v_zsmulFn_x3f_2691_);
lean_ctor_set(v_reuseFailAlloc_2721_, 26, v_nsmulFn_x3f_2692_);
lean_ctor_set(v_reuseFailAlloc_2721_, 27, v_homomulFn_x3f_2693_);
lean_ctor_set(v_reuseFailAlloc_2721_, 28, v_subFn_2694_);
lean_ctor_set(v_reuseFailAlloc_2721_, 29, v_negFn_2695_);
lean_ctor_set(v_reuseFailAlloc_2721_, 30, v_vars_2696_);
lean_ctor_set(v_reuseFailAlloc_2721_, 31, v_varMap_2697_);
lean_ctor_set(v_reuseFailAlloc_2721_, 32, v_lowers_2698_);
lean_ctor_set(v_reuseFailAlloc_2721_, 33, v_uppers_2699_);
lean_ctor_set(v_reuseFailAlloc_2721_, 34, v_diseqs_2700_);
lean_ctor_set(v_reuseFailAlloc_2721_, 35, v_assignment_2701_);
lean_ctor_set(v_reuseFailAlloc_2721_, 36, v_conflict_x3f_2703_);
lean_ctor_set(v_reuseFailAlloc_2721_, 37, v_diseqSplits_2704_);
lean_ctor_set(v_reuseFailAlloc_2721_, 38, v_elimEqs_2705_);
lean_ctor_set(v_reuseFailAlloc_2721_, 39, v_elimStack_2706_);
lean_ctor_set(v_reuseFailAlloc_2721_, 40, v_occurs_2707_);
lean_ctor_set(v_reuseFailAlloc_2721_, 41, v___x_2714_);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, sizeof(void*)*42, v_caseSplits_2702_);
v___x_2716_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2717_ = lean_array_fset(v_xs_x27_2713_, v___y_2649_, v___x_2716_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 0, v___x_2717_);
v___x_2719_ = v___x_2663_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2717_);
lean_ctor_set(v_reuseFailAlloc_2720_, 1, v_typeIdOf_2653_);
lean_ctor_set(v_reuseFailAlloc_2720_, 2, v_exprToStructId_2654_);
lean_ctor_set(v_reuseFailAlloc_2720_, 3, v_exprToStructIdEntries_2655_);
lean_ctor_set(v_reuseFailAlloc_2720_, 4, v_forbiddenNatModules_2656_);
lean_ctor_set(v_reuseFailAlloc_2720_, 5, v_natStructs_2657_);
lean_ctor_set(v_reuseFailAlloc_2720_, 6, v_natTypeIdOf_2658_);
lean_ctor_set(v_reuseFailAlloc_2720_, 7, v_exprToNatStructId_2659_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed(lean_object* v___y_2732_, lean_object* v_a_2733_, lean_object* v_s_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(v___y_2732_, v_a_2733_, v_s_2734_);
lean_dec(v___y_2732_);
return v_res_2735_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3(void){
_start:
{
lean_object* v_cls_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v_cls_2743_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2744_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_2745_ = l_Lean_Name_append(v___x_2744_, v_cls_2743_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object* v_c_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_){
_start:
{
lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v_toCold_2784_; lean_object* v_options_2785_; uint8_t v_hasTrace_2786_; 
v_toCold_2784_ = lean_ctor_get(v_a_2756_, 0);
v_options_2785_ = lean_ctor_get(v_toCold_2784_, 2);
v_hasTrace_2786_ = lean_ctor_get_uint8(v_options_2785_, sizeof(void*)*1);
if (v_hasTrace_2786_ == 0)
{
v___y_2760_ = v_a_2747_;
v___y_2761_ = v_a_2748_;
v___y_2762_ = v_a_2749_;
v___y_2763_ = v_a_2750_;
v___y_2764_ = v_a_2751_;
v___y_2765_ = v_a_2752_;
v___y_2766_ = v_a_2753_;
v___y_2767_ = v_a_2754_;
v___y_2768_ = v_a_2755_;
v___y_2769_ = v_a_2756_;
v___y_2770_ = v_a_2757_;
goto v___jp_2759_;
}
else
{
lean_object* v_inheritedTraceOptions_2787_; lean_object* v_cls_2788_; lean_object* v___x_2789_; uint8_t v___x_2790_; 
v_inheritedTraceOptions_2787_ = lean_ctor_get(v_toCold_2784_, 11);
v_cls_2788_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2789_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3);
v___x_2790_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2787_, v_options_2785_, v___x_2789_);
if (v___x_2790_ == 0)
{
v___y_2760_ = v_a_2747_;
v___y_2761_ = v_a_2748_;
v___y_2762_ = v_a_2749_;
v___y_2763_ = v_a_2750_;
v___y_2764_ = v_a_2751_;
v___y_2765_ = v_a_2752_;
v___y_2766_ = v_a_2753_;
v___y_2767_ = v_a_2754_;
v___y_2768_ = v_a_2755_;
v___y_2769_ = v_a_2756_;
v___y_2770_ = v_a_2757_;
goto v___jp_2759_;
}
else
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v___x_2791_, 1);
v___x_2793_ = l_Lean_MessageData_ofExpr(v_a_2792_);
v___x_2794_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_2788_, v___x_2793_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_dec_ref_known(v___x_2794_, 1);
v___y_2760_ = v_a_2747_;
v___y_2761_ = v_a_2748_;
v___y_2762_ = v_a_2749_;
v___y_2763_ = v_a_2750_;
v___y_2764_ = v_a_2751_;
v___y_2765_ = v_a_2752_;
v___y_2766_ = v_a_2753_;
v___y_2767_ = v_a_2754_;
v___y_2768_ = v_a_2755_;
v___y_2769_ = v_a_2756_;
v___y_2770_ = v_a_2757_;
goto v___jp_2759_;
}
else
{
return v___x_2794_;
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
v_a_2795_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2791_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2791_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
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
v___jp_2759_:
{
lean_object* v___x_2771_; 
v___x_2771_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2746_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___f_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
lean_inc(v___y_2760_);
v___f_2773_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2773_, 0, v___y_2760_);
lean_closure_set(v___f_2773_, 1, v_a_2772_);
v___x_2774_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2775_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2774_, v___f_2773_, v___y_2761_);
return v___x_2775_;
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
v_a_2776_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2771_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2771_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object* v_c_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_);
lean_dec(v_a_2814_);
lean_dec_ref(v_a_2813_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
lean_dec(v_a_2810_);
lean_dec_ref(v_a_2809_);
lean_dec(v_a_2808_);
lean_dec_ref(v_a_2807_);
lean_dec(v_a_2806_);
lean_dec(v_a_2805_);
lean_dec(v_a_2804_);
lean_dec_ref(v_c_2803_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object* v_c_u2082_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v_p_2830_; lean_object* v_toCold_2831_; lean_object* v_currRecDepth_2832_; lean_object* v_ref_2833_; uint16_t v_optionFlags_2834_; uint8_t v_suppressElabErrors_2835_; uint8_t v_isRecordingDeps_2836_; lean_object* v_maxRecDepth_2888_; lean_object* v___x_2889_; uint8_t v___x_2890_; 
v_p_2830_ = lean_ctor_get(v_c_u2082_2817_, 0);
v_toCold_2831_ = lean_ctor_get(v_a_2827_, 0);
lean_inc_ref(v_toCold_2831_);
v_currRecDepth_2832_ = lean_ctor_get(v_a_2827_, 1);
lean_inc(v_currRecDepth_2832_);
v_ref_2833_ = lean_ctor_get(v_a_2827_, 2);
lean_inc(v_ref_2833_);
v_optionFlags_2834_ = lean_ctor_get_uint16(v_a_2827_, sizeof(void*)*3);
v_suppressElabErrors_2835_ = lean_ctor_get_uint8(v_a_2827_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2836_ = lean_ctor_get_uint8(v_a_2827_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_2827_);
v_maxRecDepth_2888_ = lean_ctor_get(v_toCold_2831_, 3);
v___x_2889_ = lean_unsigned_to_nat(0u);
v___x_2890_ = lean_nat_dec_eq(v_maxRecDepth_2888_, v___x_2889_);
if (v___x_2890_ == 0)
{
uint8_t v___x_2891_; 
v___x_2891_ = lean_nat_dec_eq(v_currRecDepth_2832_, v_maxRecDepth_2888_);
if (v___x_2891_ == 0)
{
goto v___jp_2837_;
}
else
{
lean_object* v___x_2892_; 
lean_dec(v_currRecDepth_2832_);
lean_dec_ref(v_toCold_2831_);
lean_dec_ref(v_c_u2082_2817_);
v___x_2892_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_2833_);
return v___x_2892_;
}
}
else
{
goto v___jp_2837_;
}
v___jp_2837_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2838_ = lean_unsigned_to_nat(1u);
v___x_2839_ = lean_nat_add(v_currRecDepth_2832_, v___x_2838_);
lean_dec(v_currRecDepth_2832_);
v___x_2840_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2840_, 0, v_toCold_2831_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
lean_ctor_set(v___x_2840_, 2, v_ref_2833_);
lean_ctor_set_uint16(v___x_2840_, sizeof(void*)*3, v_optionFlags_2834_);
lean_ctor_set_uint8(v___x_2840_, sizeof(void*)*3 + 2, v_suppressElabErrors_2835_);
lean_ctor_set_uint8(v___x_2840_, sizeof(void*)*3 + 3, v_isRecordingDeps_2836_);
v___x_2841_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2830_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v___x_2840_, v_a_2828_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2879_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2844_ = v___x_2841_;
v_isShared_2845_ = v_isSharedCheck_2879_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2841_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2879_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
if (lean_obj_tag(v_a_2842_) == 1)
{
lean_object* v_val_2846_; lean_object* v_snd_2847_; lean_object* v_snd_2848_; lean_object* v_fst_2849_; lean_object* v_fst_2850_; lean_object* v_p_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_del_object(v___x_2844_);
v_val_2846_ = lean_ctor_get(v_a_2842_, 0);
lean_inc(v_val_2846_);
lean_dec_ref_known(v_a_2842_, 1);
v_snd_2847_ = lean_ctor_get(v_val_2846_, 1);
lean_inc(v_snd_2847_);
v_snd_2848_ = lean_ctor_get(v_snd_2847_, 1);
lean_inc(v_snd_2848_);
v_fst_2849_ = lean_ctor_get(v_val_2846_, 0);
lean_inc(v_fst_2849_);
lean_dec(v_val_2846_);
v_fst_2850_ = lean_ctor_get(v_snd_2847_, 0);
lean_inc(v_fst_2850_);
lean_dec(v_snd_2847_);
v_p_2851_ = lean_ctor_get(v_snd_2848_, 0);
v___x_2852_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2851_, v_fst_2850_);
lean_inc_ref(v_c_u2082_2817_);
v___x_2853_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v___x_2852_, v_fst_2850_, v_snd_2848_, v_fst_2849_, v_c_u2082_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v___x_2840_, v_a_2828_);
lean_dec(v_fst_2850_);
lean_dec(v___x_2852_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2854_);
lean_dec_ref_known(v___x_2853_, 1);
if (lean_obj_tag(v_a_2854_) == 1)
{
lean_object* v_val_2855_; 
lean_dec_ref(v_c_u2082_2817_);
v_val_2855_ = lean_ctor_get(v_a_2854_, 0);
lean_inc(v_val_2855_);
lean_dec_ref_known(v_a_2854_, 1);
v_c_u2082_2817_ = v_val_2855_;
v_a_2827_ = v___x_2840_;
goto _start;
}
else
{
lean_object* v___x_2857_; 
lean_dec(v_a_2854_);
v___x_2857_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_u2082_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v___x_2840_, v_a_2828_);
lean_dec_ref_known(v___x_2840_, 3);
lean_dec_ref(v_c_u2082_2817_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2865_; 
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2865_ == 0)
{
lean_object* v_unused_2866_; 
v_unused_2866_ = lean_ctor_get(v___x_2857_, 0);
lean_dec(v_unused_2866_);
v___x_2859_ = v___x_2857_;
v_isShared_2860_ = v_isSharedCheck_2865_;
goto v_resetjp_2858_;
}
else
{
lean_dec(v___x_2857_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2865_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2861_; lean_object* v___x_2863_; 
v___x_2861_ = lean_box(0);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v___x_2861_);
v___x_2863_ = v___x_2859_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2861_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
v_a_2867_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2857_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2857_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2840_, 3);
lean_dec_ref(v_c_u2082_2817_);
return v___x_2853_;
}
}
else
{
lean_object* v___x_2875_; lean_object* v___x_2877_; 
lean_dec(v_a_2842_);
lean_dec_ref_known(v___x_2840_, 3);
v___x_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2875_, 0, v_c_u2082_2817_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v___x_2875_);
v___x_2877_ = v___x_2844_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec_ref_known(v___x_2840_, 3);
lean_dec_ref(v_c_u2082_2817_);
v_a_2880_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2841_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2841_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object* v_c_u2082_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_u2082_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
lean_dec(v_a_2904_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
lean_dec(v_a_2896_);
lean_dec(v_a_2895_);
lean_dec(v_a_2894_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object* v_val_2907_, lean_object* v_x_2908_, size_t v_x_2909_, size_t v_x_2910_){
_start:
{
if (lean_obj_tag(v_x_2908_) == 0)
{
lean_object* v_cs_2911_; size_t v_j_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; uint8_t v___x_2915_; 
v_cs_2911_ = lean_ctor_get(v_x_2908_, 0);
v_j_2912_ = lean_usize_shift_right(v_x_2909_, v_x_2910_);
v___x_2913_ = lean_usize_to_nat(v_j_2912_);
v___x_2914_ = lean_array_get_size(v_cs_2911_);
v___x_2915_ = lean_nat_dec_lt(v___x_2913_, v___x_2914_);
if (v___x_2915_ == 0)
{
lean_dec(v___x_2913_);
lean_dec_ref(v_val_2907_);
return v_x_2908_;
}
else
{
lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2933_; 
lean_inc_ref(v_cs_2911_);
v_isSharedCheck_2933_ = !lean_is_exclusive(v_x_2908_);
if (v_isSharedCheck_2933_ == 0)
{
lean_object* v_unused_2934_; 
v_unused_2934_ = lean_ctor_get(v_x_2908_, 0);
lean_dec(v_unused_2934_);
v___x_2917_ = v_x_2908_;
v_isShared_2918_ = v_isSharedCheck_2933_;
goto v_resetjp_2916_;
}
else
{
lean_dec(v_x_2908_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2933_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
size_t v___x_2919_; size_t v___x_2920_; size_t v___x_2921_; size_t v_i_2922_; size_t v___x_2923_; size_t v_shift_2924_; lean_object* v_v_2925_; lean_object* v___x_2926_; lean_object* v_xs_x27_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2931_; 
v___x_2919_ = ((size_t)1ULL);
v___x_2920_ = lean_usize_shift_left(v___x_2919_, v_x_2910_);
v___x_2921_ = lean_usize_sub(v___x_2920_, v___x_2919_);
v_i_2922_ = lean_usize_land(v_x_2909_, v___x_2921_);
v___x_2923_ = ((size_t)5ULL);
v_shift_2924_ = lean_usize_sub(v_x_2910_, v___x_2923_);
v_v_2925_ = lean_array_fget(v_cs_2911_, v___x_2913_);
v___x_2926_ = lean_box(0);
v_xs_x27_2927_ = lean_array_fset(v_cs_2911_, v___x_2913_, v___x_2926_);
v___x_2928_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2907_, v_v_2925_, v_i_2922_, v_shift_2924_);
v___x_2929_ = lean_array_fset(v_xs_x27_2927_, v___x_2913_, v___x_2928_);
lean_dec(v___x_2913_);
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 0, v___x_2929_);
v___x_2931_ = v___x_2917_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2929_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
else
{
lean_object* v_vs_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; 
v_vs_2935_ = lean_ctor_get(v_x_2908_, 0);
v___x_2936_ = lean_usize_to_nat(v_x_2909_);
v___x_2937_ = lean_array_get_size(v_vs_2935_);
v___x_2938_ = lean_nat_dec_lt(v___x_2936_, v___x_2937_);
if (v___x_2938_ == 0)
{
lean_dec(v___x_2936_);
lean_dec_ref(v_val_2907_);
return v_x_2908_;
}
else
{
lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2950_; 
lean_inc_ref(v_vs_2935_);
v_isSharedCheck_2950_ = !lean_is_exclusive(v_x_2908_);
if (v_isSharedCheck_2950_ == 0)
{
lean_object* v_unused_2951_; 
v_unused_2951_ = lean_ctor_get(v_x_2908_, 0);
lean_dec(v_unused_2951_);
v___x_2940_ = v_x_2908_;
v_isShared_2941_ = v_isSharedCheck_2950_;
goto v_resetjp_2939_;
}
else
{
lean_dec(v_x_2908_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2950_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v_v_2942_; lean_object* v___x_2943_; lean_object* v_xs_x27_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2948_; 
v_v_2942_ = lean_array_fget(v_vs_2935_, v___x_2936_);
v___x_2943_ = lean_box(0);
v_xs_x27_2944_ = lean_array_fset(v_vs_2935_, v___x_2936_, v___x_2943_);
v___x_2945_ = l_Lean_PersistentArray_push___redArg(v_v_2942_, v_val_2907_);
v___x_2946_ = lean_array_fset(v_xs_x27_2944_, v___x_2936_, v___x_2945_);
lean_dec(v___x_2936_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 0, v___x_2946_);
v___x_2948_ = v___x_2940_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2946_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_val_2952_, lean_object* v_x_2953_, lean_object* v_x_2954_, lean_object* v_x_2955_){
_start:
{
size_t v_x_41338__boxed_2956_; size_t v_x_41339__boxed_2957_; lean_object* v_res_2958_; 
v_x_41338__boxed_2956_ = lean_unbox_usize(v_x_2954_);
lean_dec(v_x_2954_);
v_x_41339__boxed_2957_ = lean_unbox_usize(v_x_2955_);
lean_dec(v_x_2955_);
v_res_2958_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2952_, v_x_2953_, v_x_41338__boxed_2956_, v_x_41339__boxed_2957_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object* v_val_2959_, lean_object* v_t_2960_, lean_object* v_i_2961_){
_start:
{
lean_object* v_root_2962_; lean_object* v_tail_2963_; lean_object* v_size_2964_; size_t v_shift_2965_; lean_object* v_tailOff_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2990_; 
v_root_2962_ = lean_ctor_get(v_t_2960_, 0);
v_tail_2963_ = lean_ctor_get(v_t_2960_, 1);
v_size_2964_ = lean_ctor_get(v_t_2960_, 2);
v_shift_2965_ = lean_ctor_get_usize(v_t_2960_, 4);
v_tailOff_2966_ = lean_ctor_get(v_t_2960_, 3);
v_isSharedCheck_2990_ = !lean_is_exclusive(v_t_2960_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2968_ = v_t_2960_;
v_isShared_2969_ = v_isSharedCheck_2990_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_tailOff_2966_);
lean_inc(v_size_2964_);
lean_inc(v_tail_2963_);
lean_inc(v_root_2962_);
lean_dec(v_t_2960_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2990_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
uint8_t v___x_2970_; 
v___x_2970_ = lean_nat_dec_le(v_tailOff_2966_, v_i_2961_);
if (v___x_2970_ == 0)
{
size_t v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2974_; 
v___x_2971_ = lean_usize_of_nat(v_i_2961_);
v___x_2972_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2959_, v_root_2962_, v___x_2971_, v_shift_2965_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 0, v___x_2972_);
v___x_2974_ = v___x_2968_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2972_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v_tail_2963_);
lean_ctor_set(v_reuseFailAlloc_2975_, 2, v_size_2964_);
lean_ctor_set(v_reuseFailAlloc_2975_, 3, v_tailOff_2966_);
lean_ctor_set_usize(v_reuseFailAlloc_2975_, 4, v_shift_2965_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
else
{
lean_object* v___x_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v___x_2976_ = lean_nat_sub(v_i_2961_, v_tailOff_2966_);
v___x_2977_ = lean_array_get_size(v_tail_2963_);
v___x_2978_ = lean_nat_dec_lt(v___x_2976_, v___x_2977_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2980_; 
lean_dec(v___x_2976_);
lean_dec_ref(v_val_2959_);
if (v_isShared_2969_ == 0)
{
v___x_2980_ = v___x_2968_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_root_2962_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v_tail_2963_);
lean_ctor_set(v_reuseFailAlloc_2981_, 2, v_size_2964_);
lean_ctor_set(v_reuseFailAlloc_2981_, 3, v_tailOff_2966_);
lean_ctor_set_usize(v_reuseFailAlloc_2981_, 4, v_shift_2965_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
else
{
lean_object* v_v_2982_; lean_object* v___x_2983_; lean_object* v_xs_x27_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2988_; 
v_v_2982_ = lean_array_fget(v_tail_2963_, v___x_2976_);
v___x_2983_ = lean_box(0);
v_xs_x27_2984_ = lean_array_fset(v_tail_2963_, v___x_2976_, v___x_2983_);
v___x_2985_ = l_Lean_PersistentArray_push___redArg(v_v_2982_, v_val_2959_);
v___x_2986_ = lean_array_fset(v_xs_x27_2984_, v___x_2976_, v___x_2985_);
lean_dec(v___x_2976_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 1, v___x_2986_);
v___x_2988_ = v___x_2968_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_root_2962_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v___x_2986_);
lean_ctor_set(v_reuseFailAlloc_2989_, 2, v_size_2964_);
lean_ctor_set(v_reuseFailAlloc_2989_, 3, v_tailOff_2966_);
lean_ctor_set_usize(v_reuseFailAlloc_2989_, 4, v_shift_2965_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object* v_val_2991_, lean_object* v_t_2992_, lean_object* v_i_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_2991_, v_t_2992_, v_i_2993_);
lean_dec(v_i_2993_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(lean_object* v___y_2995_, lean_object* v_val_2996_, lean_object* v_v_2997_, lean_object* v_s_2998_){
_start:
{
lean_object* v_structs_2999_; lean_object* v_typeIdOf_3000_; lean_object* v_exprToStructId_3001_; lean_object* v_exprToStructIdEntries_3002_; lean_object* v_forbiddenNatModules_3003_; lean_object* v_natStructs_3004_; lean_object* v_natTypeIdOf_3005_; lean_object* v_exprToNatStructId_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v_structs_2999_ = lean_ctor_get(v_s_2998_, 0);
v_typeIdOf_3000_ = lean_ctor_get(v_s_2998_, 1);
v_exprToStructId_3001_ = lean_ctor_get(v_s_2998_, 2);
v_exprToStructIdEntries_3002_ = lean_ctor_get(v_s_2998_, 3);
v_forbiddenNatModules_3003_ = lean_ctor_get(v_s_2998_, 4);
v_natStructs_3004_ = lean_ctor_get(v_s_2998_, 5);
v_natTypeIdOf_3005_ = lean_ctor_get(v_s_2998_, 6);
v_exprToNatStructId_3006_ = lean_ctor_get(v_s_2998_, 7);
v___x_3007_ = lean_array_get_size(v_structs_2999_);
v___x_3008_ = lean_nat_dec_lt(v___y_2995_, v___x_3007_);
if (v___x_3008_ == 0)
{
lean_dec_ref(v_val_2996_);
return v_s_2998_;
}
else
{
lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3070_; 
lean_inc_ref(v_exprToNatStructId_3006_);
lean_inc_ref(v_natTypeIdOf_3005_);
lean_inc_ref(v_natStructs_3004_);
lean_inc_ref(v_forbiddenNatModules_3003_);
lean_inc_ref(v_exprToStructIdEntries_3002_);
lean_inc_ref(v_exprToStructId_3001_);
lean_inc_ref(v_typeIdOf_3000_);
lean_inc_ref(v_structs_2999_);
v_isSharedCheck_3070_ = !lean_is_exclusive(v_s_2998_);
if (v_isSharedCheck_3070_ == 0)
{
lean_object* v_unused_3071_; lean_object* v_unused_3072_; lean_object* v_unused_3073_; lean_object* v_unused_3074_; lean_object* v_unused_3075_; lean_object* v_unused_3076_; lean_object* v_unused_3077_; lean_object* v_unused_3078_; 
v_unused_3071_ = lean_ctor_get(v_s_2998_, 7);
lean_dec(v_unused_3071_);
v_unused_3072_ = lean_ctor_get(v_s_2998_, 6);
lean_dec(v_unused_3072_);
v_unused_3073_ = lean_ctor_get(v_s_2998_, 5);
lean_dec(v_unused_3073_);
v_unused_3074_ = lean_ctor_get(v_s_2998_, 4);
lean_dec(v_unused_3074_);
v_unused_3075_ = lean_ctor_get(v_s_2998_, 3);
lean_dec(v_unused_3075_);
v_unused_3076_ = lean_ctor_get(v_s_2998_, 2);
lean_dec(v_unused_3076_);
v_unused_3077_ = lean_ctor_get(v_s_2998_, 1);
lean_dec(v_unused_3077_);
v_unused_3078_ = lean_ctor_get(v_s_2998_, 0);
lean_dec(v_unused_3078_);
v___x_3010_ = v_s_2998_;
v_isShared_3011_ = v_isSharedCheck_3070_;
goto v_resetjp_3009_;
}
else
{
lean_dec(v_s_2998_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3070_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v_v_3012_; lean_object* v_id_3013_; lean_object* v_ringId_x3f_3014_; lean_object* v_type_3015_; lean_object* v_u_3016_; lean_object* v_intModuleInst_3017_; lean_object* v_leInst_x3f_3018_; lean_object* v_ltInst_x3f_3019_; lean_object* v_lawfulOrderLTInst_x3f_3020_; lean_object* v_isPreorderInst_x3f_3021_; lean_object* v_orderedAddInst_x3f_3022_; lean_object* v_isLinearInst_x3f_3023_; lean_object* v_noNatDivInst_x3f_3024_; lean_object* v_ringInst_x3f_3025_; lean_object* v_commRingInst_x3f_3026_; lean_object* v_orderedRingInst_x3f_3027_; lean_object* v_fieldInst_x3f_3028_; lean_object* v_charInst_x3f_3029_; lean_object* v_zero_3030_; lean_object* v_ofNatZero_3031_; lean_object* v_one_x3f_3032_; lean_object* v_leFn_x3f_3033_; lean_object* v_ltFn_x3f_3034_; lean_object* v_addFn_3035_; lean_object* v_zsmulFn_3036_; lean_object* v_nsmulFn_3037_; lean_object* v_zsmulFn_x3f_3038_; lean_object* v_nsmulFn_x3f_3039_; lean_object* v_homomulFn_x3f_3040_; lean_object* v_subFn_3041_; lean_object* v_negFn_3042_; lean_object* v_vars_3043_; lean_object* v_varMap_3044_; lean_object* v_lowers_3045_; lean_object* v_uppers_3046_; lean_object* v_diseqs_3047_; lean_object* v_assignment_3048_; uint8_t v_caseSplits_3049_; lean_object* v_conflict_x3f_3050_; lean_object* v_diseqSplits_3051_; lean_object* v_elimEqs_3052_; lean_object* v_elimStack_3053_; lean_object* v_occurs_3054_; lean_object* v_ignored_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3069_; 
v_v_3012_ = lean_array_fget(v_structs_2999_, v___y_2995_);
v_id_3013_ = lean_ctor_get(v_v_3012_, 0);
v_ringId_x3f_3014_ = lean_ctor_get(v_v_3012_, 1);
v_type_3015_ = lean_ctor_get(v_v_3012_, 2);
v_u_3016_ = lean_ctor_get(v_v_3012_, 3);
v_intModuleInst_3017_ = lean_ctor_get(v_v_3012_, 4);
v_leInst_x3f_3018_ = lean_ctor_get(v_v_3012_, 5);
v_ltInst_x3f_3019_ = lean_ctor_get(v_v_3012_, 6);
v_lawfulOrderLTInst_x3f_3020_ = lean_ctor_get(v_v_3012_, 7);
v_isPreorderInst_x3f_3021_ = lean_ctor_get(v_v_3012_, 8);
v_orderedAddInst_x3f_3022_ = lean_ctor_get(v_v_3012_, 9);
v_isLinearInst_x3f_3023_ = lean_ctor_get(v_v_3012_, 10);
v_noNatDivInst_x3f_3024_ = lean_ctor_get(v_v_3012_, 11);
v_ringInst_x3f_3025_ = lean_ctor_get(v_v_3012_, 12);
v_commRingInst_x3f_3026_ = lean_ctor_get(v_v_3012_, 13);
v_orderedRingInst_x3f_3027_ = lean_ctor_get(v_v_3012_, 14);
v_fieldInst_x3f_3028_ = lean_ctor_get(v_v_3012_, 15);
v_charInst_x3f_3029_ = lean_ctor_get(v_v_3012_, 16);
v_zero_3030_ = lean_ctor_get(v_v_3012_, 17);
v_ofNatZero_3031_ = lean_ctor_get(v_v_3012_, 18);
v_one_x3f_3032_ = lean_ctor_get(v_v_3012_, 19);
v_leFn_x3f_3033_ = lean_ctor_get(v_v_3012_, 20);
v_ltFn_x3f_3034_ = lean_ctor_get(v_v_3012_, 21);
v_addFn_3035_ = lean_ctor_get(v_v_3012_, 22);
v_zsmulFn_3036_ = lean_ctor_get(v_v_3012_, 23);
v_nsmulFn_3037_ = lean_ctor_get(v_v_3012_, 24);
v_zsmulFn_x3f_3038_ = lean_ctor_get(v_v_3012_, 25);
v_nsmulFn_x3f_3039_ = lean_ctor_get(v_v_3012_, 26);
v_homomulFn_x3f_3040_ = lean_ctor_get(v_v_3012_, 27);
v_subFn_3041_ = lean_ctor_get(v_v_3012_, 28);
v_negFn_3042_ = lean_ctor_get(v_v_3012_, 29);
v_vars_3043_ = lean_ctor_get(v_v_3012_, 30);
v_varMap_3044_ = lean_ctor_get(v_v_3012_, 31);
v_lowers_3045_ = lean_ctor_get(v_v_3012_, 32);
v_uppers_3046_ = lean_ctor_get(v_v_3012_, 33);
v_diseqs_3047_ = lean_ctor_get(v_v_3012_, 34);
v_assignment_3048_ = lean_ctor_get(v_v_3012_, 35);
v_caseSplits_3049_ = lean_ctor_get_uint8(v_v_3012_, sizeof(void*)*42);
v_conflict_x3f_3050_ = lean_ctor_get(v_v_3012_, 36);
v_diseqSplits_3051_ = lean_ctor_get(v_v_3012_, 37);
v_elimEqs_3052_ = lean_ctor_get(v_v_3012_, 38);
v_elimStack_3053_ = lean_ctor_get(v_v_3012_, 39);
v_occurs_3054_ = lean_ctor_get(v_v_3012_, 40);
v_ignored_3055_ = lean_ctor_get(v_v_3012_, 41);
v_isSharedCheck_3069_ = !lean_is_exclusive(v_v_3012_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3057_ = v_v_3012_;
v_isShared_3058_ = v_isSharedCheck_3069_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_ignored_3055_);
lean_inc(v_occurs_3054_);
lean_inc(v_elimStack_3053_);
lean_inc(v_elimEqs_3052_);
lean_inc(v_diseqSplits_3051_);
lean_inc(v_conflict_x3f_3050_);
lean_inc(v_assignment_3048_);
lean_inc(v_diseqs_3047_);
lean_inc(v_uppers_3046_);
lean_inc(v_lowers_3045_);
lean_inc(v_varMap_3044_);
lean_inc(v_vars_3043_);
lean_inc(v_negFn_3042_);
lean_inc(v_subFn_3041_);
lean_inc(v_homomulFn_x3f_3040_);
lean_inc(v_nsmulFn_x3f_3039_);
lean_inc(v_zsmulFn_x3f_3038_);
lean_inc(v_nsmulFn_3037_);
lean_inc(v_zsmulFn_3036_);
lean_inc(v_addFn_3035_);
lean_inc(v_ltFn_x3f_3034_);
lean_inc(v_leFn_x3f_3033_);
lean_inc(v_one_x3f_3032_);
lean_inc(v_ofNatZero_3031_);
lean_inc(v_zero_3030_);
lean_inc(v_charInst_x3f_3029_);
lean_inc(v_fieldInst_x3f_3028_);
lean_inc(v_orderedRingInst_x3f_3027_);
lean_inc(v_commRingInst_x3f_3026_);
lean_inc(v_ringInst_x3f_3025_);
lean_inc(v_noNatDivInst_x3f_3024_);
lean_inc(v_isLinearInst_x3f_3023_);
lean_inc(v_orderedAddInst_x3f_3022_);
lean_inc(v_isPreorderInst_x3f_3021_);
lean_inc(v_lawfulOrderLTInst_x3f_3020_);
lean_inc(v_ltInst_x3f_3019_);
lean_inc(v_leInst_x3f_3018_);
lean_inc(v_intModuleInst_3017_);
lean_inc(v_u_3016_);
lean_inc(v_type_3015_);
lean_inc(v_ringId_x3f_3014_);
lean_inc(v_id_3013_);
lean_dec(v_v_3012_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3069_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3059_; lean_object* v_xs_x27_3060_; lean_object* v___x_3061_; lean_object* v___x_3063_; 
v___x_3059_ = lean_box(0);
v_xs_x27_3060_ = lean_array_fset(v_structs_2999_, v___y_2995_, v___x_3059_);
v___x_3061_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_2996_, v_diseqs_3047_, v_v_2997_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 34, v___x_3061_);
v___x_3063_ = v___x_3057_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_id_3013_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v_ringId_x3f_3014_);
lean_ctor_set(v_reuseFailAlloc_3068_, 2, v_type_3015_);
lean_ctor_set(v_reuseFailAlloc_3068_, 3, v_u_3016_);
lean_ctor_set(v_reuseFailAlloc_3068_, 4, v_intModuleInst_3017_);
lean_ctor_set(v_reuseFailAlloc_3068_, 5, v_leInst_x3f_3018_);
lean_ctor_set(v_reuseFailAlloc_3068_, 6, v_ltInst_x3f_3019_);
lean_ctor_set(v_reuseFailAlloc_3068_, 7, v_lawfulOrderLTInst_x3f_3020_);
lean_ctor_set(v_reuseFailAlloc_3068_, 8, v_isPreorderInst_x3f_3021_);
lean_ctor_set(v_reuseFailAlloc_3068_, 9, v_orderedAddInst_x3f_3022_);
lean_ctor_set(v_reuseFailAlloc_3068_, 10, v_isLinearInst_x3f_3023_);
lean_ctor_set(v_reuseFailAlloc_3068_, 11, v_noNatDivInst_x3f_3024_);
lean_ctor_set(v_reuseFailAlloc_3068_, 12, v_ringInst_x3f_3025_);
lean_ctor_set(v_reuseFailAlloc_3068_, 13, v_commRingInst_x3f_3026_);
lean_ctor_set(v_reuseFailAlloc_3068_, 14, v_orderedRingInst_x3f_3027_);
lean_ctor_set(v_reuseFailAlloc_3068_, 15, v_fieldInst_x3f_3028_);
lean_ctor_set(v_reuseFailAlloc_3068_, 16, v_charInst_x3f_3029_);
lean_ctor_set(v_reuseFailAlloc_3068_, 17, v_zero_3030_);
lean_ctor_set(v_reuseFailAlloc_3068_, 18, v_ofNatZero_3031_);
lean_ctor_set(v_reuseFailAlloc_3068_, 19, v_one_x3f_3032_);
lean_ctor_set(v_reuseFailAlloc_3068_, 20, v_leFn_x3f_3033_);
lean_ctor_set(v_reuseFailAlloc_3068_, 21, v_ltFn_x3f_3034_);
lean_ctor_set(v_reuseFailAlloc_3068_, 22, v_addFn_3035_);
lean_ctor_set(v_reuseFailAlloc_3068_, 23, v_zsmulFn_3036_);
lean_ctor_set(v_reuseFailAlloc_3068_, 24, v_nsmulFn_3037_);
lean_ctor_set(v_reuseFailAlloc_3068_, 25, v_zsmulFn_x3f_3038_);
lean_ctor_set(v_reuseFailAlloc_3068_, 26, v_nsmulFn_x3f_3039_);
lean_ctor_set(v_reuseFailAlloc_3068_, 27, v_homomulFn_x3f_3040_);
lean_ctor_set(v_reuseFailAlloc_3068_, 28, v_subFn_3041_);
lean_ctor_set(v_reuseFailAlloc_3068_, 29, v_negFn_3042_);
lean_ctor_set(v_reuseFailAlloc_3068_, 30, v_vars_3043_);
lean_ctor_set(v_reuseFailAlloc_3068_, 31, v_varMap_3044_);
lean_ctor_set(v_reuseFailAlloc_3068_, 32, v_lowers_3045_);
lean_ctor_set(v_reuseFailAlloc_3068_, 33, v_uppers_3046_);
lean_ctor_set(v_reuseFailAlloc_3068_, 34, v___x_3061_);
lean_ctor_set(v_reuseFailAlloc_3068_, 35, v_assignment_3048_);
lean_ctor_set(v_reuseFailAlloc_3068_, 36, v_conflict_x3f_3050_);
lean_ctor_set(v_reuseFailAlloc_3068_, 37, v_diseqSplits_3051_);
lean_ctor_set(v_reuseFailAlloc_3068_, 38, v_elimEqs_3052_);
lean_ctor_set(v_reuseFailAlloc_3068_, 39, v_elimStack_3053_);
lean_ctor_set(v_reuseFailAlloc_3068_, 40, v_occurs_3054_);
lean_ctor_set(v_reuseFailAlloc_3068_, 41, v_ignored_3055_);
lean_ctor_set_uint8(v_reuseFailAlloc_3068_, sizeof(void*)*42, v_caseSplits_3049_);
v___x_3063_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
lean_object* v___x_3064_; lean_object* v___x_3066_; 
v___x_3064_ = lean_array_fset(v_xs_x27_3060_, v___y_2995_, v___x_3063_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 0, v___x_3064_);
v___x_3066_ = v___x_3010_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3064_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v_typeIdOf_3000_);
lean_ctor_set(v_reuseFailAlloc_3067_, 2, v_exprToStructId_3001_);
lean_ctor_set(v_reuseFailAlloc_3067_, 3, v_exprToStructIdEntries_3002_);
lean_ctor_set(v_reuseFailAlloc_3067_, 4, v_forbiddenNatModules_3003_);
lean_ctor_set(v_reuseFailAlloc_3067_, 5, v_natStructs_3004_);
lean_ctor_set(v_reuseFailAlloc_3067_, 6, v_natTypeIdOf_3005_);
lean_ctor_set(v_reuseFailAlloc_3067_, 7, v_exprToNatStructId_3006_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed(lean_object* v___y_3079_, lean_object* v_val_3080_, lean_object* v_v_3081_, lean_object* v_s_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(v___y_3079_, v_val_3080_, v_v_3081_, v_s_3082_);
lean_dec(v_v_3081_);
lean_dec(v___y_3079_);
return v_res_3083_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2(void){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3089_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3090_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3091_ = l_Lean_Name_append(v___x_3090_, v___x_3089_);
return v___x_3091_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3098_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3099_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3100_ = l_Lean_Name_append(v___x_3099_, v___x_3098_);
return v___x_3100_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7(void){
_start:
{
lean_object* v_cls_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v_cls_3105_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3107_ = l_Lean_Name_append(v___x_3106_, v_cls_3105_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object* v_c_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_){
_start:
{
lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v_toCold_3179_; lean_object* v_options_3180_; lean_object* v_inheritedTraceOptions_3181_; uint8_t v_hasTrace_3182_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; 
v_toCold_3179_ = lean_ctor_get(v_a_3118_, 0);
v_options_3180_ = lean_ctor_get(v_toCold_3179_, 2);
v_inheritedTraceOptions_3181_ = lean_ctor_get(v_toCold_3179_, 11);
v_hasTrace_3182_ = lean_ctor_get_uint8(v_options_3180_, sizeof(void*)*1);
if (v_hasTrace_3182_ == 0)
{
v___y_3184_ = v_a_3109_;
v___y_3185_ = v_a_3110_;
v___y_3186_ = v_a_3111_;
v___y_3187_ = v_a_3112_;
v___y_3188_ = v_a_3113_;
v___y_3189_ = v_a_3114_;
v___y_3190_ = v_a_3115_;
v___y_3191_ = v_a_3116_;
v___y_3192_ = v_a_3117_;
v___y_3193_ = v_a_3118_;
v___y_3194_ = v_a_3119_;
goto v___jp_3183_;
}
else
{
lean_object* v_cls_3255_; lean_object* v___x_3256_; uint8_t v___x_3257_; 
v_cls_3255_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3256_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_3257_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3181_, v_options_3180_, v___x_3256_);
if (v___x_3257_ == 0)
{
v___y_3184_ = v_a_3109_;
v___y_3185_ = v_a_3110_;
v___y_3186_ = v_a_3111_;
v___y_3187_ = v_a_3112_;
v___y_3188_ = v_a_3113_;
v___y_3189_ = v_a_3114_;
v___y_3190_ = v_a_3115_;
v___y_3191_ = v_a_3116_;
v___y_3192_ = v_a_3117_;
v___y_3193_ = v_a_3118_;
v___y_3194_ = v_a_3119_;
goto v___jp_3183_;
}
else
{
lean_object* v___x_3258_; 
v___x_3258_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_a_3259_);
lean_dec_ref_known(v___x_3258_, 1);
v___x_3260_ = l_Lean_MessageData_ofExpr(v_a_3259_);
v___x_3261_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_3255_, v___x_3260_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_dec_ref_known(v___x_3261_, 1);
v___y_3184_ = v_a_3109_;
v___y_3185_ = v_a_3110_;
v___y_3186_ = v_a_3111_;
v___y_3187_ = v_a_3112_;
v___y_3188_ = v_a_3113_;
v___y_3189_ = v_a_3114_;
v___y_3190_ = v_a_3115_;
v___y_3191_ = v_a_3116_;
v___y_3192_ = v_a_3117_;
v___y_3193_ = v_a_3118_;
v___y_3194_ = v_a_3119_;
goto v___jp_3183_;
}
else
{
lean_dec_ref(v_c_3108_);
return v___x_3261_;
}
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_dec_ref(v_c_3108_);
v_a_3262_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3258_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3258_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
}
v___jp_3121_:
{
lean_object* v___f_3138_; lean_object* v___x_3139_; 
lean_inc(v___y_3127_);
v___f_3138_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3138_, 0, v___y_3127_);
lean_closure_set(v___f_3138_, 1, v___y_3123_);
lean_closure_set(v___f_3138_, 2, v___y_3122_);
v___x_3139_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_3124_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
lean_dec_ref_known(v___x_3139_, 1);
v___x_3140_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3141_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3140_, v___f_3138_, v___y_3128_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v___x_3142_; 
lean_dec_ref_known(v___x_3141_, 1);
v___x_3142_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3155_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3145_ = v___x_3142_;
v_isShared_3146_ = v_isSharedCheck_3155_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3142_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3155_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
uint8_t v___x_3147_; uint8_t v___x_3148_; uint8_t v___x_3149_; 
v___x_3147_ = 0;
v___x_3148_ = lean_unbox(v_a_3143_);
lean_dec(v_a_3143_);
v___x_3149_ = l_Lean_instBEqLBool_beq(v___x_3148_, v___x_3147_);
if (v___x_3149_ == 0)
{
lean_object* v___x_3150_; lean_object* v___x_3152_; 
lean_dec(v___y_3125_);
v___x_3150_ = lean_box(0);
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 0, v___x_3150_);
v___x_3152_ = v___x_3145_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3150_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
else
{
lean_object* v___x_3154_; 
lean_del_object(v___x_3145_);
v___x_3154_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_3125_, v___y_3127_, v___y_3128_);
return v___x_3154_;
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec(v___y_3125_);
v_a_3156_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3142_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3142_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
return v___x_3141_;
}
}
else
{
lean_dec_ref(v___f_3138_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
return v___x_3139_;
}
}
v___jp_3164_:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3177_, 0, v___y_3165_);
v___x_3178_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(v___x_3177_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
return v___x_3178_;
}
v___jp_3183_:
{
lean_object* v___x_3195_; 
lean_inc_ref(v___y_3193_);
v___x_3195_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_3108_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3246_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3198_ = v___x_3195_;
v_isShared_3199_ = v_isSharedCheck_3246_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3195_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3246_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
if (lean_obj_tag(v_a_3196_) == 1)
{
lean_object* v_val_3200_; lean_object* v_p_3201_; 
lean_del_object(v___x_3198_);
v_val_3200_ = lean_ctor_get(v_a_3196_, 0);
lean_inc(v_val_3200_);
lean_dec_ref_known(v_a_3196_, 1);
v_p_3201_ = lean_ctor_get(v_val_3200_, 0);
if (lean_obj_tag(v_p_3201_) == 0)
{
lean_object* v_toCold_3202_; lean_object* v_options_3203_; uint8_t v_hasTrace_3204_; 
v_toCold_3202_ = lean_ctor_get(v___y_3193_, 0);
v_options_3203_ = lean_ctor_get(v_toCold_3202_, 2);
v_hasTrace_3204_ = lean_ctor_get_uint8(v_options_3203_, sizeof(void*)*1);
if (v_hasTrace_3204_ == 0)
{
v___y_3165_ = v_val_3200_;
v___y_3166_ = v___y_3184_;
v___y_3167_ = v___y_3185_;
v___y_3168_ = v___y_3186_;
v___y_3169_ = v___y_3187_;
v___y_3170_ = v___y_3188_;
v___y_3171_ = v___y_3189_;
v___y_3172_ = v___y_3190_;
v___y_3173_ = v___y_3191_;
v___y_3174_ = v___y_3192_;
v___y_3175_ = v___y_3193_;
v___y_3176_ = v___y_3194_;
goto v___jp_3164_;
}
else
{
lean_object* v_inheritedTraceOptions_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; uint8_t v___x_3208_; 
v_inheritedTraceOptions_3205_ = lean_ctor_get(v_toCold_3202_, 11);
v___x_3206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3207_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2);
v___x_3208_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3205_, v_options_3203_, v___x_3207_);
if (v___x_3208_ == 0)
{
v___y_3165_ = v_val_3200_;
v___y_3166_ = v___y_3184_;
v___y_3167_ = v___y_3185_;
v___y_3168_ = v___y_3186_;
v___y_3169_ = v___y_3187_;
v___y_3170_ = v___y_3188_;
v___y_3171_ = v___y_3189_;
v___y_3172_ = v___y_3190_;
v___y_3173_ = v___y_3191_;
v___y_3174_ = v___y_3192_;
v___y_3175_ = v___y_3193_;
v___y_3176_ = v___y_3194_;
goto v___jp_3164_;
}
else
{
lean_object* v___x_3209_; 
v___x_3209_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3200_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref_known(v___x_3209_, 1);
v___x_3211_ = l_Lean_MessageData_ofExpr(v_a_3210_);
v___x_3212_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3206_, v___x_3211_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_dec_ref_known(v___x_3212_, 1);
v___y_3165_ = v_val_3200_;
v___y_3166_ = v___y_3184_;
v___y_3167_ = v___y_3185_;
v___y_3168_ = v___y_3186_;
v___y_3169_ = v___y_3187_;
v___y_3170_ = v___y_3188_;
v___y_3171_ = v___y_3189_;
v___y_3172_ = v___y_3190_;
v___y_3173_ = v___y_3191_;
v___y_3174_ = v___y_3192_;
v___y_3175_ = v___y_3193_;
v___y_3176_ = v___y_3194_;
goto v___jp_3164_;
}
else
{
lean_dec(v_val_3200_);
return v___x_3212_;
}
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec(v_val_3200_);
v_a_3213_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3209_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3209_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3221_; lean_object* v_options_3222_; uint8_t v_hasTrace_3223_; 
lean_inc_ref(v_p_3201_);
v_toCold_3221_ = lean_ctor_get(v___y_3193_, 0);
v_options_3222_ = lean_ctor_get(v_toCold_3221_, 2);
v_hasTrace_3223_ = lean_ctor_get_uint8(v_options_3222_, sizeof(void*)*1);
if (v_hasTrace_3223_ == 0)
{
lean_object* v_v_3224_; 
v_v_3224_ = lean_ctor_get(v_p_3201_, 1);
lean_inc_n(v_v_3224_, 2);
lean_inc(v_val_3200_);
v___y_3122_ = v_v_3224_;
v___y_3123_ = v_val_3200_;
v___y_3124_ = v_p_3201_;
v___y_3125_ = v_v_3224_;
v___y_3126_ = v_val_3200_;
v___y_3127_ = v___y_3184_;
v___y_3128_ = v___y_3185_;
v___y_3129_ = v___y_3186_;
v___y_3130_ = v___y_3187_;
v___y_3131_ = v___y_3188_;
v___y_3132_ = v___y_3189_;
v___y_3133_ = v___y_3190_;
v___y_3134_ = v___y_3191_;
v___y_3135_ = v___y_3192_;
v___y_3136_ = v___y_3193_;
v___y_3137_ = v___y_3194_;
goto v___jp_3121_;
}
else
{
lean_object* v_v_3225_; lean_object* v_inheritedTraceOptions_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; uint8_t v___x_3229_; 
v_v_3225_ = lean_ctor_get(v_p_3201_, 1);
lean_inc(v_v_3225_);
v_inheritedTraceOptions_3226_ = lean_ctor_get(v_toCold_3221_, 11);
v___x_3227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3228_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_3229_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3226_, v_options_3222_, v___x_3228_);
if (v___x_3229_ == 0)
{
lean_inc(v_val_3200_);
lean_inc(v_v_3225_);
v___y_3122_ = v_v_3225_;
v___y_3123_ = v_val_3200_;
v___y_3124_ = v_p_3201_;
v___y_3125_ = v_v_3225_;
v___y_3126_ = v_val_3200_;
v___y_3127_ = v___y_3184_;
v___y_3128_ = v___y_3185_;
v___y_3129_ = v___y_3186_;
v___y_3130_ = v___y_3187_;
v___y_3131_ = v___y_3188_;
v___y_3132_ = v___y_3189_;
v___y_3133_ = v___y_3190_;
v___y_3134_ = v___y_3191_;
v___y_3135_ = v___y_3192_;
v___y_3136_ = v___y_3193_;
v___y_3137_ = v___y_3194_;
goto v___jp_3121_;
}
else
{
lean_object* v___x_3230_; 
v___x_3230_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3200_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3230_, 1);
v___x_3232_ = l_Lean_MessageData_ofExpr(v_a_3231_);
v___x_3233_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3227_, v___x_3232_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_dec_ref_known(v___x_3233_, 1);
lean_inc(v_val_3200_);
lean_inc(v_v_3225_);
v___y_3122_ = v_v_3225_;
v___y_3123_ = v_val_3200_;
v___y_3124_ = v_p_3201_;
v___y_3125_ = v_v_3225_;
v___y_3126_ = v_val_3200_;
v___y_3127_ = v___y_3184_;
v___y_3128_ = v___y_3185_;
v___y_3129_ = v___y_3186_;
v___y_3130_ = v___y_3187_;
v___y_3131_ = v___y_3188_;
v___y_3132_ = v___y_3189_;
v___y_3133_ = v___y_3190_;
v___y_3134_ = v___y_3191_;
v___y_3135_ = v___y_3192_;
v___y_3136_ = v___y_3193_;
v___y_3137_ = v___y_3194_;
goto v___jp_3121_;
}
else
{
lean_dec(v_v_3225_);
lean_dec_ref_known(v_p_3201_, 3);
lean_dec(v_val_3200_);
return v___x_3233_;
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec(v_v_3225_);
lean_dec_ref_known(v_p_3201_, 3);
lean_dec(v_val_3200_);
v_a_3234_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3230_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3230_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3242_; lean_object* v___x_3244_; 
lean_dec(v_a_3196_);
v___x_3242_ = lean_box(0);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 0, v___x_3242_);
v___x_3244_ = v___x_3198_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
v_a_3247_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3249_ = v___x_3195_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3195_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3247_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___boxed(lean_object* v_c_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_c_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_);
lean_dec(v_a_3281_);
lean_dec_ref(v_a_3280_);
lean_dec(v_a_3279_);
lean_dec_ref(v_a_3278_);
lean_dec(v_a_3277_);
lean_dec_ref(v_a_3276_);
lean_dec(v_a_3275_);
lean_dec_ref(v_a_3274_);
lean_dec(v_a_3273_);
lean_dec(v_a_3272_);
lean_dec(v_a_3271_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_3284_, lean_object* v_as_3285_, size_t v_sz_3286_, size_t v_i_3287_, lean_object* v_b_3288_){
_start:
{
uint8_t v___x_3289_; 
v___x_3289_ = lean_usize_dec_lt(v_i_3287_, v_sz_3286_);
if (v___x_3289_ == 0)
{
return v_b_3288_;
}
else
{
lean_object* v_snd_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3331_; 
v_snd_3290_ = lean_ctor_get(v_b_3288_, 1);
v_isSharedCheck_3331_ = !lean_is_exclusive(v_b_3288_);
if (v_isSharedCheck_3331_ == 0)
{
lean_object* v_unused_3332_; 
v_unused_3332_ = lean_ctor_get(v_b_3288_, 0);
lean_dec(v_unused_3332_);
v___x_3292_ = v_b_3288_;
v_isShared_3293_ = v_isSharedCheck_3331_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_snd_3290_);
lean_dec(v_b_3288_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3331_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v_fst_3294_; lean_object* v_snd_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3330_; 
v_fst_3294_ = lean_ctor_get(v_snd_3290_, 0);
v_snd_3295_ = lean_ctor_get(v_snd_3290_, 1);
v_isSharedCheck_3330_ = !lean_is_exclusive(v_snd_3290_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3297_ = v_snd_3290_;
v_isShared_3298_ = v_isSharedCheck_3330_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_snd_3295_);
lean_inc(v_fst_3294_);
lean_dec(v_snd_3290_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3330_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v_a_3299_; lean_object* v_p_3300_; lean_object* v___x_3301_; lean_object* v_a_3303_; lean_object* v_b_3310_; lean_object* v___x_3311_; uint8_t v___x_3312_; 
v_a_3299_ = lean_array_uget(v_as_3285_, v_i_3287_);
v_p_3300_ = lean_ctor_get(v_a_3299_, 0);
v___x_3301_ = lean_box(0);
v_b_3310_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3300_, v_x_3284_);
v___x_3311_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3312_ = lean_int_dec_eq(v_b_3310_, v___x_3311_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3314_; 
lean_inc(v_a_3299_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 1, v_a_3299_);
lean_ctor_set(v___x_3292_, 0, v_b_3310_);
v___x_3314_ = v___x_3292_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_b_3310_);
lean_ctor_set(v_reuseFailAlloc_3325_, 1, v_a_3299_);
v___x_3314_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3322_; 
v_isSharedCheck_3322_ = !lean_is_exclusive(v_a_3299_);
if (v_isSharedCheck_3322_ == 0)
{
lean_object* v_unused_3323_; lean_object* v_unused_3324_; 
v_unused_3323_ = lean_ctor_get(v_a_3299_, 1);
lean_dec(v_unused_3323_);
v_unused_3324_ = lean_ctor_get(v_a_3299_, 0);
lean_dec(v_unused_3324_);
v___x_3316_ = v_a_3299_;
v_isShared_3317_ = v_isSharedCheck_3322_;
goto v_resetjp_3315_;
}
else
{
lean_dec(v_a_3299_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3322_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v_todo_3318_; lean_object* v___x_3320_; 
v_todo_3318_ = lean_array_push(v_snd_3295_, v___x_3314_);
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 1, v_todo_3318_);
lean_ctor_set(v___x_3316_, 0, v_fst_3294_);
v___x_3320_ = v___x_3316_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_fst_3294_);
lean_ctor_set(v_reuseFailAlloc_3321_, 1, v_todo_3318_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
v_a_3303_ = v___x_3320_;
goto v___jp_3302_;
}
}
}
}
else
{
lean_object* v_cs_x27_3326_; lean_object* v___x_3328_; 
lean_dec(v_b_3310_);
v_cs_x27_3326_ = l_Lean_PersistentArray_push___redArg(v_fst_3294_, v_a_3299_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 1, v_snd_3295_);
lean_ctor_set(v___x_3292_, 0, v_cs_x27_3326_);
v___x_3328_ = v___x_3292_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_cs_x27_3326_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v_snd_3295_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
v_a_3303_ = v___x_3328_;
goto v___jp_3302_;
}
}
v___jp_3302_:
{
lean_object* v___x_3305_; 
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 1, v_a_3303_);
lean_ctor_set(v___x_3297_, 0, v___x_3301_);
v___x_3305_ = v___x_3297_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3301_);
lean_ctor_set(v_reuseFailAlloc_3309_, 1, v_a_3303_);
v___x_3305_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
size_t v___x_3306_; size_t v___x_3307_; 
v___x_3306_ = ((size_t)1ULL);
v___x_3307_ = lean_usize_add(v_i_3287_, v___x_3306_);
v_i_3287_ = v___x_3307_;
v_b_3288_ = v___x_3305_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_3333_, lean_object* v_as_3334_, lean_object* v_sz_3335_, lean_object* v_i_3336_, lean_object* v_b_3337_){
_start:
{
size_t v_sz_boxed_3338_; size_t v_i_boxed_3339_; lean_object* v_res_3340_; 
v_sz_boxed_3338_ = lean_unbox_usize(v_sz_3335_);
lean_dec(v_sz_3335_);
v_i_boxed_3339_ = lean_unbox_usize(v_i_3336_);
lean_dec(v_i_3336_);
v_res_3340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3333_, v_as_3334_, v_sz_boxed_3338_, v_i_boxed_3339_, v_b_3337_);
lean_dec_ref(v_as_3334_);
lean_dec(v_x_3333_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(lean_object* v_x_3341_, lean_object* v_as_3342_, size_t v_sz_3343_, size_t v_i_3344_, lean_object* v_b_3345_){
_start:
{
uint8_t v___x_3346_; 
v___x_3346_ = lean_usize_dec_lt(v_i_3344_, v_sz_3343_);
if (v___x_3346_ == 0)
{
return v_b_3345_;
}
else
{
lean_object* v_snd_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3388_; 
v_snd_3347_ = lean_ctor_get(v_b_3345_, 1);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_b_3345_);
if (v_isSharedCheck_3388_ == 0)
{
lean_object* v_unused_3389_; 
v_unused_3389_ = lean_ctor_get(v_b_3345_, 0);
lean_dec(v_unused_3389_);
v___x_3349_ = v_b_3345_;
v_isShared_3350_ = v_isSharedCheck_3388_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_snd_3347_);
lean_dec(v_b_3345_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3388_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v_fst_3351_; lean_object* v_snd_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3387_; 
v_fst_3351_ = lean_ctor_get(v_snd_3347_, 0);
v_snd_3352_ = lean_ctor_get(v_snd_3347_, 1);
v_isSharedCheck_3387_ = !lean_is_exclusive(v_snd_3347_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3354_ = v_snd_3347_;
v_isShared_3355_ = v_isSharedCheck_3387_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_snd_3352_);
lean_inc(v_fst_3351_);
lean_dec(v_snd_3347_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3387_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v_a_3356_; lean_object* v_p_3357_; lean_object* v___x_3358_; lean_object* v_a_3360_; lean_object* v_b_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
v_a_3356_ = lean_array_uget(v_as_3342_, v_i_3344_);
v_p_3357_ = lean_ctor_get(v_a_3356_, 0);
v___x_3358_ = lean_box(0);
v_b_3367_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3357_, v_x_3341_);
v___x_3368_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3369_ = lean_int_dec_eq(v_b_3367_, v___x_3368_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3371_; 
lean_inc(v_a_3356_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 1, v_a_3356_);
lean_ctor_set(v___x_3349_, 0, v_b_3367_);
v___x_3371_ = v___x_3349_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_b_3367_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_a_3356_);
v___x_3371_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3379_; 
v_isSharedCheck_3379_ = !lean_is_exclusive(v_a_3356_);
if (v_isSharedCheck_3379_ == 0)
{
lean_object* v_unused_3380_; lean_object* v_unused_3381_; 
v_unused_3380_ = lean_ctor_get(v_a_3356_, 1);
lean_dec(v_unused_3380_);
v_unused_3381_ = lean_ctor_get(v_a_3356_, 0);
lean_dec(v_unused_3381_);
v___x_3373_ = v_a_3356_;
v_isShared_3374_ = v_isSharedCheck_3379_;
goto v_resetjp_3372_;
}
else
{
lean_dec(v_a_3356_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3379_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v_todo_3375_; lean_object* v___x_3377_; 
v_todo_3375_ = lean_array_push(v_snd_3352_, v___x_3371_);
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 1, v_todo_3375_);
lean_ctor_set(v___x_3373_, 0, v_fst_3351_);
v___x_3377_ = v___x_3373_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_fst_3351_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v_todo_3375_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
v_a_3360_ = v___x_3377_;
goto v___jp_3359_;
}
}
}
}
else
{
lean_object* v_cs_x27_3383_; lean_object* v___x_3385_; 
lean_dec(v_b_3367_);
v_cs_x27_3383_ = l_Lean_PersistentArray_push___redArg(v_fst_3351_, v_a_3356_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 1, v_snd_3352_);
lean_ctor_set(v___x_3349_, 0, v_cs_x27_3383_);
v___x_3385_ = v___x_3349_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_cs_x27_3383_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v_snd_3352_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
v_a_3360_ = v___x_3385_;
goto v___jp_3359_;
}
}
v___jp_3359_:
{
lean_object* v___x_3362_; 
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 1, v_a_3360_);
lean_ctor_set(v___x_3354_, 0, v___x_3358_);
v___x_3362_ = v___x_3354_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3358_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v_a_3360_);
v___x_3362_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
size_t v___x_3363_; size_t v___x_3364_; lean_object* v___x_3365_; 
v___x_3363_ = ((size_t)1ULL);
v___x_3364_ = lean_usize_add(v_i_3344_, v___x_3363_);
v___x_3365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3341_, v_as_3342_, v_sz_3343_, v___x_3364_, v___x_3362_);
return v___x_3365_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_3390_, lean_object* v_as_3391_, lean_object* v_sz_3392_, lean_object* v_i_3393_, lean_object* v_b_3394_){
_start:
{
size_t v_sz_boxed_3395_; size_t v_i_boxed_3396_; lean_object* v_res_3397_; 
v_sz_boxed_3395_ = lean_unbox_usize(v_sz_3392_);
lean_dec(v_sz_3392_);
v_i_boxed_3396_ = lean_unbox_usize(v_i_3393_);
lean_dec(v_i_3393_);
v_res_3397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3390_, v_as_3391_, v_sz_boxed_3395_, v_i_boxed_3396_, v_b_3394_);
lean_dec_ref(v_as_3391_);
lean_dec(v_x_3390_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_3398_, lean_object* v_as_3399_, size_t v_sz_3400_, size_t v_i_3401_, lean_object* v_b_3402_){
_start:
{
uint8_t v___x_3403_; 
v___x_3403_ = lean_usize_dec_lt(v_i_3401_, v_sz_3400_);
if (v___x_3403_ == 0)
{
return v_b_3402_;
}
else
{
lean_object* v_snd_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3445_; 
v_snd_3404_ = lean_ctor_get(v_b_3402_, 1);
v_isSharedCheck_3445_ = !lean_is_exclusive(v_b_3402_);
if (v_isSharedCheck_3445_ == 0)
{
lean_object* v_unused_3446_; 
v_unused_3446_ = lean_ctor_get(v_b_3402_, 0);
lean_dec(v_unused_3446_);
v___x_3406_ = v_b_3402_;
v_isShared_3407_ = v_isSharedCheck_3445_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_snd_3404_);
lean_dec(v_b_3402_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3445_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v_fst_3408_; lean_object* v_snd_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3444_; 
v_fst_3408_ = lean_ctor_get(v_snd_3404_, 0);
v_snd_3409_ = lean_ctor_get(v_snd_3404_, 1);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_snd_3404_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3411_ = v_snd_3404_;
v_isShared_3412_ = v_isSharedCheck_3444_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_snd_3409_);
lean_inc(v_fst_3408_);
lean_dec(v_snd_3404_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3444_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v_a_3413_; lean_object* v_p_3414_; lean_object* v___x_3415_; lean_object* v_a_3417_; lean_object* v_b_3424_; lean_object* v___x_3425_; uint8_t v___x_3426_; 
v_a_3413_ = lean_array_uget(v_as_3399_, v_i_3401_);
v_p_3414_ = lean_ctor_get(v_a_3413_, 0);
v___x_3415_ = lean_box(0);
v_b_3424_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3414_, v_x_3398_);
v___x_3425_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3426_ = lean_int_dec_eq(v_b_3424_, v___x_3425_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3428_; 
lean_inc(v_a_3413_);
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 1, v_a_3413_);
lean_ctor_set(v___x_3406_, 0, v_b_3424_);
v___x_3428_ = v___x_3406_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_b_3424_);
lean_ctor_set(v_reuseFailAlloc_3439_, 1, v_a_3413_);
v___x_3428_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3436_; 
v_isSharedCheck_3436_ = !lean_is_exclusive(v_a_3413_);
if (v_isSharedCheck_3436_ == 0)
{
lean_object* v_unused_3437_; lean_object* v_unused_3438_; 
v_unused_3437_ = lean_ctor_get(v_a_3413_, 1);
lean_dec(v_unused_3437_);
v_unused_3438_ = lean_ctor_get(v_a_3413_, 0);
lean_dec(v_unused_3438_);
v___x_3430_ = v_a_3413_;
v_isShared_3431_ = v_isSharedCheck_3436_;
goto v_resetjp_3429_;
}
else
{
lean_dec(v_a_3413_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3436_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v_todo_3432_; lean_object* v___x_3434_; 
v_todo_3432_ = lean_array_push(v_snd_3409_, v___x_3428_);
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 1, v_todo_3432_);
lean_ctor_set(v___x_3430_, 0, v_fst_3408_);
v___x_3434_ = v___x_3430_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_fst_3408_);
lean_ctor_set(v_reuseFailAlloc_3435_, 1, v_todo_3432_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
v_a_3417_ = v___x_3434_;
goto v___jp_3416_;
}
}
}
}
else
{
lean_object* v_cs_x27_3440_; lean_object* v___x_3442_; 
lean_dec(v_b_3424_);
v_cs_x27_3440_ = l_Lean_PersistentArray_push___redArg(v_fst_3408_, v_a_3413_);
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 1, v_snd_3409_);
lean_ctor_set(v___x_3406_, 0, v_cs_x27_3440_);
v___x_3442_ = v___x_3406_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_cs_x27_3440_);
lean_ctor_set(v_reuseFailAlloc_3443_, 1, v_snd_3409_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
v_a_3417_ = v___x_3442_;
goto v___jp_3416_;
}
}
v___jp_3416_:
{
lean_object* v___x_3419_; 
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 1, v_a_3417_);
lean_ctor_set(v___x_3411_, 0, v___x_3415_);
v___x_3419_ = v___x_3411_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v_a_3417_);
v___x_3419_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
size_t v___x_3420_; size_t v___x_3421_; 
v___x_3420_ = ((size_t)1ULL);
v___x_3421_ = lean_usize_add(v_i_3401_, v___x_3420_);
v_i_3401_ = v___x_3421_;
v_b_3402_ = v___x_3419_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3447_, lean_object* v_as_3448_, lean_object* v_sz_3449_, lean_object* v_i_3450_, lean_object* v_b_3451_){
_start:
{
size_t v_sz_boxed_3452_; size_t v_i_boxed_3453_; lean_object* v_res_3454_; 
v_sz_boxed_3452_ = lean_unbox_usize(v_sz_3449_);
lean_dec(v_sz_3449_);
v_i_boxed_3453_ = lean_unbox_usize(v_i_3450_);
lean_dec(v_i_3450_);
v_res_3454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3447_, v_as_3448_, v_sz_boxed_3452_, v_i_boxed_3453_, v_b_3451_);
lean_dec_ref(v_as_3448_);
lean_dec(v_x_3447_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_3455_, lean_object* v_as_3456_, size_t v_sz_3457_, size_t v_i_3458_, lean_object* v_b_3459_){
_start:
{
uint8_t v___x_3460_; 
v___x_3460_ = lean_usize_dec_lt(v_i_3458_, v_sz_3457_);
if (v___x_3460_ == 0)
{
return v_b_3459_;
}
else
{
lean_object* v_snd_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3502_; 
v_snd_3461_ = lean_ctor_get(v_b_3459_, 1);
v_isSharedCheck_3502_ = !lean_is_exclusive(v_b_3459_);
if (v_isSharedCheck_3502_ == 0)
{
lean_object* v_unused_3503_; 
v_unused_3503_ = lean_ctor_get(v_b_3459_, 0);
lean_dec(v_unused_3503_);
v___x_3463_ = v_b_3459_;
v_isShared_3464_ = v_isSharedCheck_3502_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_snd_3461_);
lean_dec(v_b_3459_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3502_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v_fst_3465_; lean_object* v_snd_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3501_; 
v_fst_3465_ = lean_ctor_get(v_snd_3461_, 0);
v_snd_3466_ = lean_ctor_get(v_snd_3461_, 1);
v_isSharedCheck_3501_ = !lean_is_exclusive(v_snd_3461_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3468_ = v_snd_3461_;
v_isShared_3469_ = v_isSharedCheck_3501_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_snd_3466_);
lean_inc(v_fst_3465_);
lean_dec(v_snd_3461_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3501_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v_a_3470_; lean_object* v_p_3471_; lean_object* v___x_3472_; lean_object* v_a_3474_; lean_object* v_b_3481_; lean_object* v___x_3482_; uint8_t v___x_3483_; 
v_a_3470_ = lean_array_uget(v_as_3456_, v_i_3458_);
v_p_3471_ = lean_ctor_get(v_a_3470_, 0);
v___x_3472_ = lean_box(0);
v_b_3481_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3471_, v_x_3455_);
v___x_3482_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3483_ = lean_int_dec_eq(v_b_3481_, v___x_3482_);
if (v___x_3483_ == 0)
{
lean_object* v___x_3485_; 
lean_inc(v_a_3470_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 1, v_a_3470_);
lean_ctor_set(v___x_3463_, 0, v_b_3481_);
v___x_3485_ = v___x_3463_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_b_3481_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v_a_3470_);
v___x_3485_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3493_; 
v_isSharedCheck_3493_ = !lean_is_exclusive(v_a_3470_);
if (v_isSharedCheck_3493_ == 0)
{
lean_object* v_unused_3494_; lean_object* v_unused_3495_; 
v_unused_3494_ = lean_ctor_get(v_a_3470_, 1);
lean_dec(v_unused_3494_);
v_unused_3495_ = lean_ctor_get(v_a_3470_, 0);
lean_dec(v_unused_3495_);
v___x_3487_ = v_a_3470_;
v_isShared_3488_ = v_isSharedCheck_3493_;
goto v_resetjp_3486_;
}
else
{
lean_dec(v_a_3470_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3493_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v_todo_3489_; lean_object* v___x_3491_; 
v_todo_3489_ = lean_array_push(v_snd_3466_, v___x_3485_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 1, v_todo_3489_);
lean_ctor_set(v___x_3487_, 0, v_fst_3465_);
v___x_3491_ = v___x_3487_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_fst_3465_);
lean_ctor_set(v_reuseFailAlloc_3492_, 1, v_todo_3489_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
v_a_3474_ = v___x_3491_;
goto v___jp_3473_;
}
}
}
}
else
{
lean_object* v_cs_x27_3497_; lean_object* v___x_3499_; 
lean_dec(v_b_3481_);
v_cs_x27_3497_ = l_Lean_PersistentArray_push___redArg(v_fst_3465_, v_a_3470_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 1, v_snd_3466_);
lean_ctor_set(v___x_3463_, 0, v_cs_x27_3497_);
v___x_3499_ = v___x_3463_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_cs_x27_3497_);
lean_ctor_set(v_reuseFailAlloc_3500_, 1, v_snd_3466_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
v_a_3474_ = v___x_3499_;
goto v___jp_3473_;
}
}
v___jp_3473_:
{
lean_object* v___x_3476_; 
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 1, v_a_3474_);
lean_ctor_set(v___x_3468_, 0, v___x_3472_);
v___x_3476_ = v___x_3468_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3472_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v_a_3474_);
v___x_3476_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
size_t v___x_3477_; size_t v___x_3478_; lean_object* v___x_3479_; 
v___x_3477_ = ((size_t)1ULL);
v___x_3478_ = lean_usize_add(v_i_3458_, v___x_3477_);
v___x_3479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3455_, v_as_3456_, v_sz_3457_, v___x_3478_, v___x_3476_);
return v___x_3479_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_3504_, lean_object* v_as_3505_, lean_object* v_sz_3506_, lean_object* v_i_3507_, lean_object* v_b_3508_){
_start:
{
size_t v_sz_boxed_3509_; size_t v_i_boxed_3510_; lean_object* v_res_3511_; 
v_sz_boxed_3509_ = lean_unbox_usize(v_sz_3506_);
lean_dec(v_sz_3506_);
v_i_boxed_3510_ = lean_unbox_usize(v_i_3507_);
lean_dec(v_i_3507_);
v_res_3511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3504_, v_as_3505_, v_sz_boxed_3509_, v_i_boxed_3510_, v_b_3508_);
lean_dec_ref(v_as_3505_);
lean_dec(v_x_3504_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(lean_object* v_init_3512_, lean_object* v_x_3513_, lean_object* v_n_3514_, lean_object* v_b_3515_){
_start:
{
if (lean_obj_tag(v_n_3514_) == 0)
{
lean_object* v_cs_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; size_t v_sz_3519_; size_t v___x_3520_; lean_object* v___x_3521_; lean_object* v_fst_3522_; 
v_cs_3516_ = lean_ctor_get(v_n_3514_, 0);
v___x_3517_ = lean_box(0);
v___x_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
lean_ctor_set(v___x_3518_, 1, v_b_3515_);
v_sz_3519_ = lean_array_size(v_cs_3516_);
v___x_3520_ = ((size_t)0ULL);
v___x_3521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3512_, v_x_3513_, v_cs_3516_, v_sz_3519_, v___x_3520_, v___x_3518_);
v_fst_3522_ = lean_ctor_get(v___x_3521_, 0);
if (lean_obj_tag(v_fst_3522_) == 0)
{
lean_object* v_snd_3523_; lean_object* v___x_3524_; 
v_snd_3523_ = lean_ctor_get(v___x_3521_, 1);
lean_inc(v_snd_3523_);
lean_dec_ref(v___x_3521_);
v___x_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3524_, 0, v_snd_3523_);
return v___x_3524_;
}
else
{
lean_object* v_val_3525_; 
lean_inc_ref(v_fst_3522_);
lean_dec_ref(v___x_3521_);
v_val_3525_ = lean_ctor_get(v_fst_3522_, 0);
lean_inc(v_val_3525_);
lean_dec_ref_known(v_fst_3522_, 1);
return v_val_3525_;
}
}
else
{
lean_object* v_vs_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; size_t v_sz_3529_; size_t v___x_3530_; lean_object* v___x_3531_; lean_object* v_fst_3532_; 
v_vs_3526_ = lean_ctor_get(v_n_3514_, 0);
v___x_3527_ = lean_box(0);
v___x_3528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3527_);
lean_ctor_set(v___x_3528_, 1, v_b_3515_);
v_sz_3529_ = lean_array_size(v_vs_3526_);
v___x_3530_ = ((size_t)0ULL);
v___x_3531_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3513_, v_vs_3526_, v_sz_3529_, v___x_3530_, v___x_3528_);
v_fst_3532_ = lean_ctor_get(v___x_3531_, 0);
if (lean_obj_tag(v_fst_3532_) == 0)
{
lean_object* v_snd_3533_; lean_object* v___x_3534_; 
v_snd_3533_ = lean_ctor_get(v___x_3531_, 1);
lean_inc(v_snd_3533_);
lean_dec_ref(v___x_3531_);
v___x_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3534_, 0, v_snd_3533_);
return v___x_3534_;
}
else
{
lean_object* v_val_3535_; 
lean_inc_ref(v_fst_3532_);
lean_dec_ref(v___x_3531_);
v_val_3535_ = lean_ctor_get(v_fst_3532_, 0);
lean_inc(v_val_3535_);
lean_dec_ref_known(v_fst_3532_, 1);
return v_val_3535_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3536_, lean_object* v_x_3537_, lean_object* v_as_3538_, size_t v_sz_3539_, size_t v_i_3540_, lean_object* v_b_3541_){
_start:
{
uint8_t v___x_3542_; 
v___x_3542_ = lean_usize_dec_lt(v_i_3540_, v_sz_3539_);
if (v___x_3542_ == 0)
{
return v_b_3541_;
}
else
{
lean_object* v_snd_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3561_; 
v_snd_3543_ = lean_ctor_get(v_b_3541_, 1);
v_isSharedCheck_3561_ = !lean_is_exclusive(v_b_3541_);
if (v_isSharedCheck_3561_ == 0)
{
lean_object* v_unused_3562_; 
v_unused_3562_ = lean_ctor_get(v_b_3541_, 0);
lean_dec(v_unused_3562_);
v___x_3545_ = v_b_3541_;
v_isShared_3546_ = v_isSharedCheck_3561_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_snd_3543_);
lean_dec(v_b_3541_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3561_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v_a_3547_; lean_object* v___x_3548_; 
v_a_3547_ = lean_array_uget_borrowed(v_as_3538_, v_i_3540_);
lean_inc(v_snd_3543_);
v___x_3548_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3536_, v_x_3537_, v_a_3547_, v_snd_3543_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v___x_3549_; lean_object* v___x_3551_; 
v___x_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 0, v___x_3549_);
v___x_3551_ = v___x_3545_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_snd_3543_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3554_; lean_object* v___x_3556_; 
lean_dec(v_snd_3543_);
v_a_3553_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_a_3553_);
lean_dec_ref_known(v___x_3548_, 1);
v___x_3554_ = lean_box(0);
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 1, v_a_3553_);
lean_ctor_set(v___x_3545_, 0, v___x_3554_);
v___x_3556_ = v___x_3545_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3554_);
lean_ctor_set(v_reuseFailAlloc_3560_, 1, v_a_3553_);
v___x_3556_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
size_t v___x_3557_; size_t v___x_3558_; 
v___x_3557_ = ((size_t)1ULL);
v___x_3558_ = lean_usize_add(v_i_3540_, v___x_3557_);
v_i_3540_ = v___x_3558_;
v_b_3541_ = v___x_3556_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3563_, lean_object* v_x_3564_, lean_object* v_as_3565_, lean_object* v_sz_3566_, lean_object* v_i_3567_, lean_object* v_b_3568_){
_start:
{
size_t v_sz_boxed_3569_; size_t v_i_boxed_3570_; lean_object* v_res_3571_; 
v_sz_boxed_3569_ = lean_unbox_usize(v_sz_3566_);
lean_dec(v_sz_3566_);
v_i_boxed_3570_ = lean_unbox_usize(v_i_3567_);
lean_dec(v_i_3567_);
v_res_3571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3563_, v_x_3564_, v_as_3565_, v_sz_boxed_3569_, v_i_boxed_3570_, v_b_3568_);
lean_dec_ref(v_as_3565_);
lean_dec(v_x_3564_);
lean_dec_ref(v_init_3563_);
return v_res_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3572_, lean_object* v_x_3573_, lean_object* v_n_3574_, lean_object* v_b_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3572_, v_x_3573_, v_n_3574_, v_b_3575_);
lean_dec_ref(v_n_3574_);
lean_dec(v_x_3573_);
lean_dec_ref(v_init_3572_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object* v_x_3577_, lean_object* v_t_3578_, lean_object* v_init_3579_){
_start:
{
lean_object* v_root_3580_; lean_object* v_tail_3581_; lean_object* v___x_3582_; 
v_root_3580_ = lean_ctor_get(v_t_3578_, 0);
v_tail_3581_ = lean_ctor_get(v_t_3578_, 1);
lean_inc_ref(v_init_3579_);
v___x_3582_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3579_, v_x_3577_, v_root_3580_, v_init_3579_);
lean_dec_ref(v_init_3579_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v_a_3583_; 
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___x_3582_, 1);
return v_a_3583_;
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; size_t v_sz_3587_; size_t v___x_3588_; lean_object* v___x_3589_; lean_object* v_fst_3590_; 
v_a_3584_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_a_3584_);
lean_dec_ref_known(v___x_3582_, 1);
v___x_3585_ = lean_box(0);
v___x_3586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3585_);
lean_ctor_set(v___x_3586_, 1, v_a_3584_);
v_sz_3587_ = lean_array_size(v_tail_3581_);
v___x_3588_ = ((size_t)0ULL);
v___x_3589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3577_, v_tail_3581_, v_sz_3587_, v___x_3588_, v___x_3586_);
v_fst_3590_ = lean_ctor_get(v___x_3589_, 0);
if (lean_obj_tag(v_fst_3590_) == 0)
{
lean_object* v_snd_3591_; 
v_snd_3591_ = lean_ctor_get(v___x_3589_, 1);
lean_inc(v_snd_3591_);
lean_dec_ref(v___x_3589_);
return v_snd_3591_;
}
else
{
lean_object* v_val_3592_; 
lean_inc_ref(v_fst_3590_);
lean_dec_ref(v___x_3589_);
v_val_3592_ = lean_ctor_get(v_fst_3590_, 0);
lean_inc(v_val_3592_);
lean_dec_ref_known(v_fst_3590_, 1);
return v_val_3592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object* v_x_3593_, lean_object* v_t_3594_, lean_object* v_init_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3593_, v_t_3594_, v_init_3595_);
lean_dec_ref(v_t_3594_);
lean_dec(v_x_3593_);
return v_res_3596_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3597_ = lean_unsigned_to_nat(32u);
v___x_3598_ = lean_mk_empty_array_with_capacity(v___x_3597_);
v___x_3599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3598_);
return v___x_3599_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1(void){
_start:
{
size_t v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v_cs_x27_3605_; 
v___x_3600_ = ((size_t)5ULL);
v___x_3601_ = lean_unsigned_to_nat(0u);
v___x_3602_ = lean_unsigned_to_nat(32u);
v___x_3603_ = lean_mk_empty_array_with_capacity(v___x_3602_);
v___x_3604_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0);
v_cs_x27_3605_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_3605_, 0, v___x_3604_);
lean_ctor_set(v_cs_x27_3605_, 1, v___x_3603_);
lean_ctor_set(v_cs_x27_3605_, 2, v___x_3601_);
lean_ctor_set(v_cs_x27_3605_, 3, v___x_3601_);
lean_ctor_set_usize(v_cs_x27_3605_, 4, v___x_3600_);
return v_cs_x27_3605_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_3608_; lean_object* v_cs_x27_3609_; lean_object* v___x_3610_; 
v_todo_3608_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2));
v_cs_x27_3609_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1);
v___x_3610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3610_, 0, v_cs_x27_3609_);
lean_ctor_set(v___x_3610_, 1, v_todo_3608_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object* v_x_3611_, lean_object* v_cs_3612_){
_start:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v_fst_3615_; lean_object* v_snd_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
v___x_3613_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3);
v___x_3614_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3611_, v_cs_3612_, v___x_3613_);
v_fst_3615_ = lean_ctor_get(v___x_3614_, 0);
v_snd_3616_ = lean_ctor_get(v___x_3614_, 1);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3614_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_snd_3616_);
lean_inc(v_fst_3615_);
lean_dec(v___x_3614_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_fst_3615_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v_snd_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object* v_x_3624_, lean_object* v_cs_3625_){
_start:
{
lean_object* v_res_3626_; 
v_res_3626_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3624_, v_cs_3625_);
lean_dec_ref(v_cs_3625_);
lean_dec(v_x_3624_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object* v_x_3627_, lean_object* v_cs_3628_){
_start:
{
lean_object* v___x_3629_; 
v___x_3629_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3627_, v_cs_3628_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object* v_x_3630_, lean_object* v_cs_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(v_x_3630_, v_cs_3631_);
lean_dec_ref(v_cs_3631_);
lean_dec(v_x_3630_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(lean_object* v_a_3633_, lean_object* v_y_3634_, lean_object* v_fst_3635_, lean_object* v_s_3636_){
_start:
{
lean_object* v_structs_3637_; lean_object* v_typeIdOf_3638_; lean_object* v_exprToStructId_3639_; lean_object* v_exprToStructIdEntries_3640_; lean_object* v_forbiddenNatModules_3641_; lean_object* v_natStructs_3642_; lean_object* v_natTypeIdOf_3643_; lean_object* v_exprToNatStructId_3644_; lean_object* v___x_3645_; uint8_t v___x_3646_; 
v_structs_3637_ = lean_ctor_get(v_s_3636_, 0);
v_typeIdOf_3638_ = lean_ctor_get(v_s_3636_, 1);
v_exprToStructId_3639_ = lean_ctor_get(v_s_3636_, 2);
v_exprToStructIdEntries_3640_ = lean_ctor_get(v_s_3636_, 3);
v_forbiddenNatModules_3641_ = lean_ctor_get(v_s_3636_, 4);
v_natStructs_3642_ = lean_ctor_get(v_s_3636_, 5);
v_natTypeIdOf_3643_ = lean_ctor_get(v_s_3636_, 6);
v_exprToNatStructId_3644_ = lean_ctor_get(v_s_3636_, 7);
v___x_3645_ = lean_array_get_size(v_structs_3637_);
v___x_3646_ = lean_nat_dec_lt(v_a_3633_, v___x_3645_);
if (v___x_3646_ == 0)
{
lean_dec_ref(v_fst_3635_);
return v_s_3636_;
}
else
{
lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3708_; 
lean_inc_ref(v_exprToNatStructId_3644_);
lean_inc_ref(v_natTypeIdOf_3643_);
lean_inc_ref(v_natStructs_3642_);
lean_inc_ref(v_forbiddenNatModules_3641_);
lean_inc_ref(v_exprToStructIdEntries_3640_);
lean_inc_ref(v_exprToStructId_3639_);
lean_inc_ref(v_typeIdOf_3638_);
lean_inc_ref(v_structs_3637_);
v_isSharedCheck_3708_ = !lean_is_exclusive(v_s_3636_);
if (v_isSharedCheck_3708_ == 0)
{
lean_object* v_unused_3709_; lean_object* v_unused_3710_; lean_object* v_unused_3711_; lean_object* v_unused_3712_; lean_object* v_unused_3713_; lean_object* v_unused_3714_; lean_object* v_unused_3715_; lean_object* v_unused_3716_; 
v_unused_3709_ = lean_ctor_get(v_s_3636_, 7);
lean_dec(v_unused_3709_);
v_unused_3710_ = lean_ctor_get(v_s_3636_, 6);
lean_dec(v_unused_3710_);
v_unused_3711_ = lean_ctor_get(v_s_3636_, 5);
lean_dec(v_unused_3711_);
v_unused_3712_ = lean_ctor_get(v_s_3636_, 4);
lean_dec(v_unused_3712_);
v_unused_3713_ = lean_ctor_get(v_s_3636_, 3);
lean_dec(v_unused_3713_);
v_unused_3714_ = lean_ctor_get(v_s_3636_, 2);
lean_dec(v_unused_3714_);
v_unused_3715_ = lean_ctor_get(v_s_3636_, 1);
lean_dec(v_unused_3715_);
v_unused_3716_ = lean_ctor_get(v_s_3636_, 0);
lean_dec(v_unused_3716_);
v___x_3648_ = v_s_3636_;
v_isShared_3649_ = v_isSharedCheck_3708_;
goto v_resetjp_3647_;
}
else
{
lean_dec(v_s_3636_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3708_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v_v_3650_; lean_object* v_id_3651_; lean_object* v_ringId_x3f_3652_; lean_object* v_type_3653_; lean_object* v_u_3654_; lean_object* v_intModuleInst_3655_; lean_object* v_leInst_x3f_3656_; lean_object* v_ltInst_x3f_3657_; lean_object* v_lawfulOrderLTInst_x3f_3658_; lean_object* v_isPreorderInst_x3f_3659_; lean_object* v_orderedAddInst_x3f_3660_; lean_object* v_isLinearInst_x3f_3661_; lean_object* v_noNatDivInst_x3f_3662_; lean_object* v_ringInst_x3f_3663_; lean_object* v_commRingInst_x3f_3664_; lean_object* v_orderedRingInst_x3f_3665_; lean_object* v_fieldInst_x3f_3666_; lean_object* v_charInst_x3f_3667_; lean_object* v_zero_3668_; lean_object* v_ofNatZero_3669_; lean_object* v_one_x3f_3670_; lean_object* v_leFn_x3f_3671_; lean_object* v_ltFn_x3f_3672_; lean_object* v_addFn_3673_; lean_object* v_zsmulFn_3674_; lean_object* v_nsmulFn_3675_; lean_object* v_zsmulFn_x3f_3676_; lean_object* v_nsmulFn_x3f_3677_; lean_object* v_homomulFn_x3f_3678_; lean_object* v_subFn_3679_; lean_object* v_negFn_3680_; lean_object* v_vars_3681_; lean_object* v_varMap_3682_; lean_object* v_lowers_3683_; lean_object* v_uppers_3684_; lean_object* v_diseqs_3685_; lean_object* v_assignment_3686_; uint8_t v_caseSplits_3687_; lean_object* v_conflict_x3f_3688_; lean_object* v_diseqSplits_3689_; lean_object* v_elimEqs_3690_; lean_object* v_elimStack_3691_; lean_object* v_occurs_3692_; lean_object* v_ignored_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3707_; 
v_v_3650_ = lean_array_fget(v_structs_3637_, v_a_3633_);
v_id_3651_ = lean_ctor_get(v_v_3650_, 0);
v_ringId_x3f_3652_ = lean_ctor_get(v_v_3650_, 1);
v_type_3653_ = lean_ctor_get(v_v_3650_, 2);
v_u_3654_ = lean_ctor_get(v_v_3650_, 3);
v_intModuleInst_3655_ = lean_ctor_get(v_v_3650_, 4);
v_leInst_x3f_3656_ = lean_ctor_get(v_v_3650_, 5);
v_ltInst_x3f_3657_ = lean_ctor_get(v_v_3650_, 6);
v_lawfulOrderLTInst_x3f_3658_ = lean_ctor_get(v_v_3650_, 7);
v_isPreorderInst_x3f_3659_ = lean_ctor_get(v_v_3650_, 8);
v_orderedAddInst_x3f_3660_ = lean_ctor_get(v_v_3650_, 9);
v_isLinearInst_x3f_3661_ = lean_ctor_get(v_v_3650_, 10);
v_noNatDivInst_x3f_3662_ = lean_ctor_get(v_v_3650_, 11);
v_ringInst_x3f_3663_ = lean_ctor_get(v_v_3650_, 12);
v_commRingInst_x3f_3664_ = lean_ctor_get(v_v_3650_, 13);
v_orderedRingInst_x3f_3665_ = lean_ctor_get(v_v_3650_, 14);
v_fieldInst_x3f_3666_ = lean_ctor_get(v_v_3650_, 15);
v_charInst_x3f_3667_ = lean_ctor_get(v_v_3650_, 16);
v_zero_3668_ = lean_ctor_get(v_v_3650_, 17);
v_ofNatZero_3669_ = lean_ctor_get(v_v_3650_, 18);
v_one_x3f_3670_ = lean_ctor_get(v_v_3650_, 19);
v_leFn_x3f_3671_ = lean_ctor_get(v_v_3650_, 20);
v_ltFn_x3f_3672_ = lean_ctor_get(v_v_3650_, 21);
v_addFn_3673_ = lean_ctor_get(v_v_3650_, 22);
v_zsmulFn_3674_ = lean_ctor_get(v_v_3650_, 23);
v_nsmulFn_3675_ = lean_ctor_get(v_v_3650_, 24);
v_zsmulFn_x3f_3676_ = lean_ctor_get(v_v_3650_, 25);
v_nsmulFn_x3f_3677_ = lean_ctor_get(v_v_3650_, 26);
v_homomulFn_x3f_3678_ = lean_ctor_get(v_v_3650_, 27);
v_subFn_3679_ = lean_ctor_get(v_v_3650_, 28);
v_negFn_3680_ = lean_ctor_get(v_v_3650_, 29);
v_vars_3681_ = lean_ctor_get(v_v_3650_, 30);
v_varMap_3682_ = lean_ctor_get(v_v_3650_, 31);
v_lowers_3683_ = lean_ctor_get(v_v_3650_, 32);
v_uppers_3684_ = lean_ctor_get(v_v_3650_, 33);
v_diseqs_3685_ = lean_ctor_get(v_v_3650_, 34);
v_assignment_3686_ = lean_ctor_get(v_v_3650_, 35);
v_caseSplits_3687_ = lean_ctor_get_uint8(v_v_3650_, sizeof(void*)*42);
v_conflict_x3f_3688_ = lean_ctor_get(v_v_3650_, 36);
v_diseqSplits_3689_ = lean_ctor_get(v_v_3650_, 37);
v_elimEqs_3690_ = lean_ctor_get(v_v_3650_, 38);
v_elimStack_3691_ = lean_ctor_get(v_v_3650_, 39);
v_occurs_3692_ = lean_ctor_get(v_v_3650_, 40);
v_ignored_3693_ = lean_ctor_get(v_v_3650_, 41);
v_isSharedCheck_3707_ = !lean_is_exclusive(v_v_3650_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3695_ = v_v_3650_;
v_isShared_3696_ = v_isSharedCheck_3707_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_ignored_3693_);
lean_inc(v_occurs_3692_);
lean_inc(v_elimStack_3691_);
lean_inc(v_elimEqs_3690_);
lean_inc(v_diseqSplits_3689_);
lean_inc(v_conflict_x3f_3688_);
lean_inc(v_assignment_3686_);
lean_inc(v_diseqs_3685_);
lean_inc(v_uppers_3684_);
lean_inc(v_lowers_3683_);
lean_inc(v_varMap_3682_);
lean_inc(v_vars_3681_);
lean_inc(v_negFn_3680_);
lean_inc(v_subFn_3679_);
lean_inc(v_homomulFn_x3f_3678_);
lean_inc(v_nsmulFn_x3f_3677_);
lean_inc(v_zsmulFn_x3f_3676_);
lean_inc(v_nsmulFn_3675_);
lean_inc(v_zsmulFn_3674_);
lean_inc(v_addFn_3673_);
lean_inc(v_ltFn_x3f_3672_);
lean_inc(v_leFn_x3f_3671_);
lean_inc(v_one_x3f_3670_);
lean_inc(v_ofNatZero_3669_);
lean_inc(v_zero_3668_);
lean_inc(v_charInst_x3f_3667_);
lean_inc(v_fieldInst_x3f_3666_);
lean_inc(v_orderedRingInst_x3f_3665_);
lean_inc(v_commRingInst_x3f_3664_);
lean_inc(v_ringInst_x3f_3663_);
lean_inc(v_noNatDivInst_x3f_3662_);
lean_inc(v_isLinearInst_x3f_3661_);
lean_inc(v_orderedAddInst_x3f_3660_);
lean_inc(v_isPreorderInst_x3f_3659_);
lean_inc(v_lawfulOrderLTInst_x3f_3658_);
lean_inc(v_ltInst_x3f_3657_);
lean_inc(v_leInst_x3f_3656_);
lean_inc(v_intModuleInst_3655_);
lean_inc(v_u_3654_);
lean_inc(v_type_3653_);
lean_inc(v_ringId_x3f_3652_);
lean_inc(v_id_3651_);
lean_dec(v_v_3650_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3707_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3697_; lean_object* v_xs_x27_3698_; lean_object* v___x_3699_; lean_object* v___x_3701_; 
v___x_3697_ = lean_box(0);
v_xs_x27_3698_ = lean_array_fset(v_structs_3637_, v_a_3633_, v___x_3697_);
v___x_3699_ = l_Lean_PersistentArray_set___redArg(v_diseqs_3685_, v_y_3634_, v_fst_3635_);
if (v_isShared_3696_ == 0)
{
lean_ctor_set(v___x_3695_, 34, v___x_3699_);
v___x_3701_ = v___x_3695_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_id_3651_);
lean_ctor_set(v_reuseFailAlloc_3706_, 1, v_ringId_x3f_3652_);
lean_ctor_set(v_reuseFailAlloc_3706_, 2, v_type_3653_);
lean_ctor_set(v_reuseFailAlloc_3706_, 3, v_u_3654_);
lean_ctor_set(v_reuseFailAlloc_3706_, 4, v_intModuleInst_3655_);
lean_ctor_set(v_reuseFailAlloc_3706_, 5, v_leInst_x3f_3656_);
lean_ctor_set(v_reuseFailAlloc_3706_, 6, v_ltInst_x3f_3657_);
lean_ctor_set(v_reuseFailAlloc_3706_, 7, v_lawfulOrderLTInst_x3f_3658_);
lean_ctor_set(v_reuseFailAlloc_3706_, 8, v_isPreorderInst_x3f_3659_);
lean_ctor_set(v_reuseFailAlloc_3706_, 9, v_orderedAddInst_x3f_3660_);
lean_ctor_set(v_reuseFailAlloc_3706_, 10, v_isLinearInst_x3f_3661_);
lean_ctor_set(v_reuseFailAlloc_3706_, 11, v_noNatDivInst_x3f_3662_);
lean_ctor_set(v_reuseFailAlloc_3706_, 12, v_ringInst_x3f_3663_);
lean_ctor_set(v_reuseFailAlloc_3706_, 13, v_commRingInst_x3f_3664_);
lean_ctor_set(v_reuseFailAlloc_3706_, 14, v_orderedRingInst_x3f_3665_);
lean_ctor_set(v_reuseFailAlloc_3706_, 15, v_fieldInst_x3f_3666_);
lean_ctor_set(v_reuseFailAlloc_3706_, 16, v_charInst_x3f_3667_);
lean_ctor_set(v_reuseFailAlloc_3706_, 17, v_zero_3668_);
lean_ctor_set(v_reuseFailAlloc_3706_, 18, v_ofNatZero_3669_);
lean_ctor_set(v_reuseFailAlloc_3706_, 19, v_one_x3f_3670_);
lean_ctor_set(v_reuseFailAlloc_3706_, 20, v_leFn_x3f_3671_);
lean_ctor_set(v_reuseFailAlloc_3706_, 21, v_ltFn_x3f_3672_);
lean_ctor_set(v_reuseFailAlloc_3706_, 22, v_addFn_3673_);
lean_ctor_set(v_reuseFailAlloc_3706_, 23, v_zsmulFn_3674_);
lean_ctor_set(v_reuseFailAlloc_3706_, 24, v_nsmulFn_3675_);
lean_ctor_set(v_reuseFailAlloc_3706_, 25, v_zsmulFn_x3f_3676_);
lean_ctor_set(v_reuseFailAlloc_3706_, 26, v_nsmulFn_x3f_3677_);
lean_ctor_set(v_reuseFailAlloc_3706_, 27, v_homomulFn_x3f_3678_);
lean_ctor_set(v_reuseFailAlloc_3706_, 28, v_subFn_3679_);
lean_ctor_set(v_reuseFailAlloc_3706_, 29, v_negFn_3680_);
lean_ctor_set(v_reuseFailAlloc_3706_, 30, v_vars_3681_);
lean_ctor_set(v_reuseFailAlloc_3706_, 31, v_varMap_3682_);
lean_ctor_set(v_reuseFailAlloc_3706_, 32, v_lowers_3683_);
lean_ctor_set(v_reuseFailAlloc_3706_, 33, v_uppers_3684_);
lean_ctor_set(v_reuseFailAlloc_3706_, 34, v___x_3699_);
lean_ctor_set(v_reuseFailAlloc_3706_, 35, v_assignment_3686_);
lean_ctor_set(v_reuseFailAlloc_3706_, 36, v_conflict_x3f_3688_);
lean_ctor_set(v_reuseFailAlloc_3706_, 37, v_diseqSplits_3689_);
lean_ctor_set(v_reuseFailAlloc_3706_, 38, v_elimEqs_3690_);
lean_ctor_set(v_reuseFailAlloc_3706_, 39, v_elimStack_3691_);
lean_ctor_set(v_reuseFailAlloc_3706_, 40, v_occurs_3692_);
lean_ctor_set(v_reuseFailAlloc_3706_, 41, v_ignored_3693_);
lean_ctor_set_uint8(v_reuseFailAlloc_3706_, sizeof(void*)*42, v_caseSplits_3687_);
v___x_3701_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
lean_object* v___x_3702_; lean_object* v___x_3704_; 
v___x_3702_ = lean_array_fset(v_xs_x27_3698_, v_a_3633_, v___x_3701_);
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 0, v___x_3702_);
v___x_3704_ = v___x_3648_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3702_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v_typeIdOf_3638_);
lean_ctor_set(v_reuseFailAlloc_3705_, 2, v_exprToStructId_3639_);
lean_ctor_set(v_reuseFailAlloc_3705_, 3, v_exprToStructIdEntries_3640_);
lean_ctor_set(v_reuseFailAlloc_3705_, 4, v_forbiddenNatModules_3641_);
lean_ctor_set(v_reuseFailAlloc_3705_, 5, v_natStructs_3642_);
lean_ctor_set(v_reuseFailAlloc_3705_, 6, v_natTypeIdOf_3643_);
lean_ctor_set(v_reuseFailAlloc_3705_, 7, v_exprToNatStructId_3644_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed(lean_object* v_a_3717_, lean_object* v_y_3718_, lean_object* v_fst_3719_, lean_object* v_s_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(v_a_3717_, v_y_3718_, v_fst_3719_, v_s_3720_);
lean_dec(v_y_3718_);
lean_dec(v_a_3717_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object* v_a_3722_, lean_object* v_x_3723_, lean_object* v_c_3724_, lean_object* v_as_3725_, size_t v_sz_3726_, size_t v_i_3727_, lean_object* v_b_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v_a_3742_; uint8_t v___x_3746_; 
v___x_3746_ = lean_usize_dec_lt(v_i_3727_, v_sz_3726_);
if (v___x_3746_ == 0)
{
lean_object* v___x_3747_; 
lean_dec_ref(v_c_3724_);
v___x_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3747_, 0, v_b_3728_);
return v___x_3747_;
}
else
{
lean_object* v_a_3748_; lean_object* v_fst_3749_; lean_object* v_snd_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
lean_dec_ref(v_b_3728_);
v_a_3748_ = lean_array_uget_borrowed(v_as_3725_, v_i_3727_);
v_fst_3749_ = lean_ctor_get(v_a_3748_, 0);
v_snd_3750_ = lean_ctor_get(v_a_3748_, 1);
v___x_3751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
lean_inc(v_snd_3750_);
lean_inc(v_fst_3749_);
lean_inc_ref(v_c_3724_);
v___x_3752_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_3722_, v_x_3723_, v_c_3724_, v_fst_3749_, v_snd_3750_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_object* v_a_3753_; 
v_a_3753_ = lean_ctor_get(v___x_3752_, 0);
lean_inc(v_a_3753_);
lean_dec_ref_known(v___x_3752_, 1);
if (lean_obj_tag(v_a_3753_) == 1)
{
lean_object* v_val_3754_; lean_object* v___x_3755_; 
v_val_3754_ = lean_ctor_get(v_a_3753_, 0);
lean_inc(v_val_3754_);
lean_dec_ref_known(v_a_3753_, 1);
v___x_3755_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_val_3754_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v___x_3756_; 
lean_dec_ref_known(v___x_3755_, 1);
v___x_3756_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3766_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3759_ = v___x_3756_;
v_isShared_3760_ = v_isSharedCheck_3766_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3756_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3766_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
uint8_t v___x_3761_; 
v___x_3761_ = lean_unbox(v_a_3757_);
lean_dec(v_a_3757_);
if (v___x_3761_ == 0)
{
lean_del_object(v___x_3759_);
v_a_3742_ = v___x_3751_;
goto v___jp_3741_;
}
else
{
lean_object* v___x_3762_; lean_object* v___x_3764_; 
lean_dec_ref(v_c_3724_);
v___x_3762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v___x_3762_);
v___x_3764_ = v___x_3759_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3762_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_dec_ref(v_c_3724_);
v_a_3767_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3756_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3756_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_dec_ref(v_c_3724_);
v_a_3775_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3755_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3755_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
else
{
lean_object* v___x_3783_; 
lean_dec(v_a_3753_);
v___x_3783_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_snd_3750_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_dec_ref_known(v___x_3783_, 1);
v_a_3742_ = v___x_3751_;
goto v___jp_3741_;
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
lean_dec_ref(v_c_3724_);
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3783_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3783_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
lean_dec_ref(v_c_3724_);
v_a_3792_ = lean_ctor_get(v___x_3752_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3752_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3752_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
v___jp_3741_:
{
size_t v___x_3743_; size_t v___x_3744_; 
v___x_3743_ = ((size_t)1ULL);
v___x_3744_ = lean_usize_add(v_i_3727_, v___x_3743_);
lean_inc_ref(v_a_3742_);
v_i_3727_ = v___x_3744_;
v_b_3728_ = v_a_3742_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object** _args){
lean_object* v_a_3800_ = _args[0];
lean_object* v_x_3801_ = _args[1];
lean_object* v_c_3802_ = _args[2];
lean_object* v_as_3803_ = _args[3];
lean_object* v_sz_3804_ = _args[4];
lean_object* v_i_3805_ = _args[5];
lean_object* v_b_3806_ = _args[6];
lean_object* v___y_3807_ = _args[7];
lean_object* v___y_3808_ = _args[8];
lean_object* v___y_3809_ = _args[9];
lean_object* v___y_3810_ = _args[10];
lean_object* v___y_3811_ = _args[11];
lean_object* v___y_3812_ = _args[12];
lean_object* v___y_3813_ = _args[13];
lean_object* v___y_3814_ = _args[14];
lean_object* v___y_3815_ = _args[15];
lean_object* v___y_3816_ = _args[16];
lean_object* v___y_3817_ = _args[17];
lean_object* v___y_3818_ = _args[18];
_start:
{
size_t v_sz_boxed_3819_; size_t v_i_boxed_3820_; lean_object* v_res_3821_; 
v_sz_boxed_3819_ = lean_unbox_usize(v_sz_3804_);
lean_dec(v_sz_3804_);
v_i_boxed_3820_ = lean_unbox_usize(v_i_3805_);
lean_dec(v_i_3805_);
v_res_3821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3800_, v_x_3801_, v_c_3802_, v_as_3803_, v_sz_boxed_3819_, v_i_boxed_3820_, v_b_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v___y_3809_);
lean_dec(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v_as_3803_);
lean_dec(v_x_3801_);
lean_dec(v_a_3800_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object* v_a_3822_, lean_object* v_x_3823_, lean_object* v_c_3824_, lean_object* v_y_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_){
_start:
{
lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3838_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_3839_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3898_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3842_ = v___x_3839_;
v_isShared_3843_ = v_isSharedCheck_3898_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3839_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3898_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
uint8_t v___x_3844_; 
v___x_3844_ = lean_unbox(v_a_3840_);
lean_dec(v_a_3840_);
if (v___x_3844_ == 0)
{
lean_object* v___x_3845_; 
lean_del_object(v___x_3842_);
v___x_3845_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; lean_object* v___y_3848_; lean_object* v_diseqs_3881_; lean_object* v_size_3882_; uint8_t v___x_3883_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_a_3846_);
lean_dec_ref_known(v___x_3845_, 1);
v_diseqs_3881_ = lean_ctor_get(v_a_3846_, 34);
lean_inc_ref(v_diseqs_3881_);
lean_dec(v_a_3846_);
v_size_3882_ = lean_ctor_get(v_diseqs_3881_, 2);
v___x_3883_ = lean_nat_dec_lt(v_y_3825_, v_size_3882_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; 
lean_dec_ref(v_diseqs_3881_);
v___x_3884_ = l_outOfBounds___redArg(v___x_3838_);
v___y_3848_ = v___x_3884_;
goto v___jp_3847_;
}
else
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3838_, v_diseqs_3881_, v_y_3825_);
lean_dec_ref(v_diseqs_3881_);
v___y_3848_ = v___x_3885_;
goto v___jp_3847_;
}
v___jp_3847_:
{
lean_object* v___x_3849_; lean_object* v_fst_3850_; lean_object* v_snd_3851_; lean_object* v___f_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3849_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3823_, v___y_3848_);
lean_dec_ref(v___y_3848_);
v_fst_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_fst_3850_);
v_snd_3851_ = lean_ctor_get(v___x_3849_, 1);
lean_inc(v_snd_3851_);
lean_dec_ref(v___x_3849_);
lean_inc(v_a_3826_);
v___f_3852_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3852_, 0, v_a_3826_);
lean_closure_set(v___f_3852_, 1, v_y_3825_);
lean_closure_set(v___f_3852_, 2, v_fst_3850_);
v___x_3853_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3854_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3853_, v___f_3852_, v_a_3827_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v___x_3855_; lean_object* v___x_3856_; size_t v_sz_3857_; size_t v___x_3858_; lean_object* v___x_3859_; 
lean_dec_ref_known(v___x_3854_, 1);
v___x_3855_ = lean_box(0);
v___x_3856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_3857_ = lean_array_size(v_snd_3851_);
v___x_3858_ = ((size_t)0ULL);
v___x_3859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3822_, v_x_3823_, v_c_3824_, v_snd_3851_, v_sz_3857_, v___x_3858_, v___x_3856_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
lean_dec(v_snd_3851_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3872_; 
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3862_ = v___x_3859_;
v_isShared_3863_ = v_isSharedCheck_3872_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3859_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3872_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v_fst_3864_; 
v_fst_3864_ = lean_ctor_get(v_a_3860_, 0);
lean_inc(v_fst_3864_);
lean_dec(v_a_3860_);
if (lean_obj_tag(v_fst_3864_) == 0)
{
lean_object* v___x_3866_; 
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 0, v___x_3855_);
v___x_3866_ = v___x_3862_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3855_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
else
{
lean_object* v_val_3868_; lean_object* v___x_3870_; 
v_val_3868_ = lean_ctor_get(v_fst_3864_, 0);
lean_inc(v_val_3868_);
lean_dec_ref_known(v_fst_3864_, 1);
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 0, v_val_3868_);
v___x_3870_ = v___x_3862_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_val_3868_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
v_a_3873_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___x_3859_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3859_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_a_3873_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
else
{
lean_dec(v_snd_3851_);
lean_dec_ref(v_c_3824_);
return v___x_3854_;
}
}
}
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
lean_dec(v_y_3825_);
lean_dec_ref(v_c_3824_);
v_a_3886_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v___x_3845_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3845_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_a_3886_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
else
{
lean_object* v___x_3894_; lean_object* v___x_3896_; 
lean_dec(v_y_3825_);
lean_dec_ref(v_c_3824_);
v___x_3894_ = lean_box(0);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 0, v___x_3894_);
v___x_3896_ = v___x_3842_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3894_);
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
else
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3906_; 
lean_dec(v_y_3825_);
lean_dec_ref(v_c_3824_);
v_a_3899_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3901_ = v___x_3839_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3839_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3899_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object* v_a_3907_, lean_object* v_x_3908_, lean_object* v_c_3909_, lean_object* v_y_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v_a_3907_, v_x_3908_, v_c_3909_, v_y_3910_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_);
lean_dec(v_a_3921_);
lean_dec_ref(v_a_3920_);
lean_dec(v_a_3919_);
lean_dec_ref(v_a_3918_);
lean_dec(v_a_3917_);
lean_dec_ref(v_a_3916_);
lean_dec(v_a_3915_);
lean_dec_ref(v_a_3914_);
lean_dec(v_a_3913_);
lean_dec(v_a_3912_);
lean_dec(v_a_3911_);
lean_dec(v_x_3908_);
lean_dec(v_a_3907_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object* v_a_3924_, lean_object* v_x_3925_, lean_object* v_c_3926_, lean_object* v_y_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_){
_start:
{
lean_object* v___x_3940_; 
lean_inc(v_y_3927_);
lean_inc_ref(v_c_3926_);
lean_inc(v_x_3925_);
lean_inc(v_a_3924_);
v___x_3940_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_3924_, v_x_3925_, v_c_3926_, v_y_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v___x_3941_; 
lean_dec_ref_known(v___x_3940_, 1);
lean_inc(v_y_3927_);
lean_inc_ref(v_c_3926_);
lean_inc(v_x_3925_);
lean_inc(v_a_3924_);
v___x_3941_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_3924_, v_x_3925_, v_c_3926_, v_y_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v___x_3942_; lean_object* v___x_3943_; 
lean_dec_ref_known(v___x_3941_, 1);
v___x_3942_ = lean_nat_to_int(v_a_3924_);
v___x_3943_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v___x_3942_, v_x_3925_, v_c_3926_, v_y_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_);
lean_dec(v_x_3925_);
lean_dec(v___x_3942_);
return v___x_3943_;
}
else
{
lean_dec(v_y_3927_);
lean_dec_ref(v_c_3926_);
lean_dec(v_x_3925_);
lean_dec(v_a_3924_);
return v___x_3941_;
}
}
else
{
lean_dec(v_y_3927_);
lean_dec_ref(v_c_3926_);
lean_dec(v_x_3925_);
lean_dec(v_a_3924_);
return v___x_3940_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object* v_a_3944_, lean_object* v_x_3945_, lean_object* v_c_3946_, lean_object* v_y_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_3944_, v_x_3945_, v_c_3946_, v_y_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_);
lean_dec(v_a_3958_);
lean_dec_ref(v_a_3957_);
lean_dec(v_a_3956_);
lean_dec_ref(v_a_3955_);
lean_dec(v_a_3954_);
lean_dec_ref(v_a_3953_);
lean_dec(v_a_3952_);
lean_dec_ref(v_a_3951_);
lean_dec(v_a_3950_);
lean_dec(v_a_3949_);
lean_dec(v_a_3948_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(lean_object* v_a_3961_, lean_object* v_x_3962_, lean_object* v_s_3963_){
_start:
{
lean_object* v_structs_3964_; lean_object* v_typeIdOf_3965_; lean_object* v_exprToStructId_3966_; lean_object* v_exprToStructIdEntries_3967_; lean_object* v_forbiddenNatModules_3968_; lean_object* v_natStructs_3969_; lean_object* v_natTypeIdOf_3970_; lean_object* v_exprToNatStructId_3971_; lean_object* v___x_3972_; uint8_t v___x_3973_; 
v_structs_3964_ = lean_ctor_get(v_s_3963_, 0);
v_typeIdOf_3965_ = lean_ctor_get(v_s_3963_, 1);
v_exprToStructId_3966_ = lean_ctor_get(v_s_3963_, 2);
v_exprToStructIdEntries_3967_ = lean_ctor_get(v_s_3963_, 3);
v_forbiddenNatModules_3968_ = lean_ctor_get(v_s_3963_, 4);
v_natStructs_3969_ = lean_ctor_get(v_s_3963_, 5);
v_natTypeIdOf_3970_ = lean_ctor_get(v_s_3963_, 6);
v_exprToNatStructId_3971_ = lean_ctor_get(v_s_3963_, 7);
v___x_3972_ = lean_array_get_size(v_structs_3964_);
v___x_3973_ = lean_nat_dec_lt(v_a_3961_, v___x_3972_);
if (v___x_3973_ == 0)
{
return v_s_3963_;
}
else
{
lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_4036_; 
lean_inc_ref(v_exprToNatStructId_3971_);
lean_inc_ref(v_natTypeIdOf_3970_);
lean_inc_ref(v_natStructs_3969_);
lean_inc_ref(v_forbiddenNatModules_3968_);
lean_inc_ref(v_exprToStructIdEntries_3967_);
lean_inc_ref(v_exprToStructId_3966_);
lean_inc_ref(v_typeIdOf_3965_);
lean_inc_ref(v_structs_3964_);
v_isSharedCheck_4036_ = !lean_is_exclusive(v_s_3963_);
if (v_isSharedCheck_4036_ == 0)
{
lean_object* v_unused_4037_; lean_object* v_unused_4038_; lean_object* v_unused_4039_; lean_object* v_unused_4040_; lean_object* v_unused_4041_; lean_object* v_unused_4042_; lean_object* v_unused_4043_; lean_object* v_unused_4044_; 
v_unused_4037_ = lean_ctor_get(v_s_3963_, 7);
lean_dec(v_unused_4037_);
v_unused_4038_ = lean_ctor_get(v_s_3963_, 6);
lean_dec(v_unused_4038_);
v_unused_4039_ = lean_ctor_get(v_s_3963_, 5);
lean_dec(v_unused_4039_);
v_unused_4040_ = lean_ctor_get(v_s_3963_, 4);
lean_dec(v_unused_4040_);
v_unused_4041_ = lean_ctor_get(v_s_3963_, 3);
lean_dec(v_unused_4041_);
v_unused_4042_ = lean_ctor_get(v_s_3963_, 2);
lean_dec(v_unused_4042_);
v_unused_4043_ = lean_ctor_get(v_s_3963_, 1);
lean_dec(v_unused_4043_);
v_unused_4044_ = lean_ctor_get(v_s_3963_, 0);
lean_dec(v_unused_4044_);
v___x_3975_ = v_s_3963_;
v_isShared_3976_ = v_isSharedCheck_4036_;
goto v_resetjp_3974_;
}
else
{
lean_dec(v_s_3963_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_4036_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v_v_3977_; lean_object* v_id_3978_; lean_object* v_ringId_x3f_3979_; lean_object* v_type_3980_; lean_object* v_u_3981_; lean_object* v_intModuleInst_3982_; lean_object* v_leInst_x3f_3983_; lean_object* v_ltInst_x3f_3984_; lean_object* v_lawfulOrderLTInst_x3f_3985_; lean_object* v_isPreorderInst_x3f_3986_; lean_object* v_orderedAddInst_x3f_3987_; lean_object* v_isLinearInst_x3f_3988_; lean_object* v_noNatDivInst_x3f_3989_; lean_object* v_ringInst_x3f_3990_; lean_object* v_commRingInst_x3f_3991_; lean_object* v_orderedRingInst_x3f_3992_; lean_object* v_fieldInst_x3f_3993_; lean_object* v_charInst_x3f_3994_; lean_object* v_zero_3995_; lean_object* v_ofNatZero_3996_; lean_object* v_one_x3f_3997_; lean_object* v_leFn_x3f_3998_; lean_object* v_ltFn_x3f_3999_; lean_object* v_addFn_4000_; lean_object* v_zsmulFn_4001_; lean_object* v_nsmulFn_4002_; lean_object* v_zsmulFn_x3f_4003_; lean_object* v_nsmulFn_x3f_4004_; lean_object* v_homomulFn_x3f_4005_; lean_object* v_subFn_4006_; lean_object* v_negFn_4007_; lean_object* v_vars_4008_; lean_object* v_varMap_4009_; lean_object* v_lowers_4010_; lean_object* v_uppers_4011_; lean_object* v_diseqs_4012_; lean_object* v_assignment_4013_; uint8_t v_caseSplits_4014_; lean_object* v_conflict_x3f_4015_; lean_object* v_diseqSplits_4016_; lean_object* v_elimEqs_4017_; lean_object* v_elimStack_4018_; lean_object* v_occurs_4019_; lean_object* v_ignored_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4035_; 
v_v_3977_ = lean_array_fget(v_structs_3964_, v_a_3961_);
v_id_3978_ = lean_ctor_get(v_v_3977_, 0);
v_ringId_x3f_3979_ = lean_ctor_get(v_v_3977_, 1);
v_type_3980_ = lean_ctor_get(v_v_3977_, 2);
v_u_3981_ = lean_ctor_get(v_v_3977_, 3);
v_intModuleInst_3982_ = lean_ctor_get(v_v_3977_, 4);
v_leInst_x3f_3983_ = lean_ctor_get(v_v_3977_, 5);
v_ltInst_x3f_3984_ = lean_ctor_get(v_v_3977_, 6);
v_lawfulOrderLTInst_x3f_3985_ = lean_ctor_get(v_v_3977_, 7);
v_isPreorderInst_x3f_3986_ = lean_ctor_get(v_v_3977_, 8);
v_orderedAddInst_x3f_3987_ = lean_ctor_get(v_v_3977_, 9);
v_isLinearInst_x3f_3988_ = lean_ctor_get(v_v_3977_, 10);
v_noNatDivInst_x3f_3989_ = lean_ctor_get(v_v_3977_, 11);
v_ringInst_x3f_3990_ = lean_ctor_get(v_v_3977_, 12);
v_commRingInst_x3f_3991_ = lean_ctor_get(v_v_3977_, 13);
v_orderedRingInst_x3f_3992_ = lean_ctor_get(v_v_3977_, 14);
v_fieldInst_x3f_3993_ = lean_ctor_get(v_v_3977_, 15);
v_charInst_x3f_3994_ = lean_ctor_get(v_v_3977_, 16);
v_zero_3995_ = lean_ctor_get(v_v_3977_, 17);
v_ofNatZero_3996_ = lean_ctor_get(v_v_3977_, 18);
v_one_x3f_3997_ = lean_ctor_get(v_v_3977_, 19);
v_leFn_x3f_3998_ = lean_ctor_get(v_v_3977_, 20);
v_ltFn_x3f_3999_ = lean_ctor_get(v_v_3977_, 21);
v_addFn_4000_ = lean_ctor_get(v_v_3977_, 22);
v_zsmulFn_4001_ = lean_ctor_get(v_v_3977_, 23);
v_nsmulFn_4002_ = lean_ctor_get(v_v_3977_, 24);
v_zsmulFn_x3f_4003_ = lean_ctor_get(v_v_3977_, 25);
v_nsmulFn_x3f_4004_ = lean_ctor_get(v_v_3977_, 26);
v_homomulFn_x3f_4005_ = lean_ctor_get(v_v_3977_, 27);
v_subFn_4006_ = lean_ctor_get(v_v_3977_, 28);
v_negFn_4007_ = lean_ctor_get(v_v_3977_, 29);
v_vars_4008_ = lean_ctor_get(v_v_3977_, 30);
v_varMap_4009_ = lean_ctor_get(v_v_3977_, 31);
v_lowers_4010_ = lean_ctor_get(v_v_3977_, 32);
v_uppers_4011_ = lean_ctor_get(v_v_3977_, 33);
v_diseqs_4012_ = lean_ctor_get(v_v_3977_, 34);
v_assignment_4013_ = lean_ctor_get(v_v_3977_, 35);
v_caseSplits_4014_ = lean_ctor_get_uint8(v_v_3977_, sizeof(void*)*42);
v_conflict_x3f_4015_ = lean_ctor_get(v_v_3977_, 36);
v_diseqSplits_4016_ = lean_ctor_get(v_v_3977_, 37);
v_elimEqs_4017_ = lean_ctor_get(v_v_3977_, 38);
v_elimStack_4018_ = lean_ctor_get(v_v_3977_, 39);
v_occurs_4019_ = lean_ctor_get(v_v_3977_, 40);
v_ignored_4020_ = lean_ctor_get(v_v_3977_, 41);
v_isSharedCheck_4035_ = !lean_is_exclusive(v_v_3977_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4022_ = v_v_3977_;
v_isShared_4023_ = v_isSharedCheck_4035_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_ignored_4020_);
lean_inc(v_occurs_4019_);
lean_inc(v_elimStack_4018_);
lean_inc(v_elimEqs_4017_);
lean_inc(v_diseqSplits_4016_);
lean_inc(v_conflict_x3f_4015_);
lean_inc(v_assignment_4013_);
lean_inc(v_diseqs_4012_);
lean_inc(v_uppers_4011_);
lean_inc(v_lowers_4010_);
lean_inc(v_varMap_4009_);
lean_inc(v_vars_4008_);
lean_inc(v_negFn_4007_);
lean_inc(v_subFn_4006_);
lean_inc(v_homomulFn_x3f_4005_);
lean_inc(v_nsmulFn_x3f_4004_);
lean_inc(v_zsmulFn_x3f_4003_);
lean_inc(v_nsmulFn_4002_);
lean_inc(v_zsmulFn_4001_);
lean_inc(v_addFn_4000_);
lean_inc(v_ltFn_x3f_3999_);
lean_inc(v_leFn_x3f_3998_);
lean_inc(v_one_x3f_3997_);
lean_inc(v_ofNatZero_3996_);
lean_inc(v_zero_3995_);
lean_inc(v_charInst_x3f_3994_);
lean_inc(v_fieldInst_x3f_3993_);
lean_inc(v_orderedRingInst_x3f_3992_);
lean_inc(v_commRingInst_x3f_3991_);
lean_inc(v_ringInst_x3f_3990_);
lean_inc(v_noNatDivInst_x3f_3989_);
lean_inc(v_isLinearInst_x3f_3988_);
lean_inc(v_orderedAddInst_x3f_3987_);
lean_inc(v_isPreorderInst_x3f_3986_);
lean_inc(v_lawfulOrderLTInst_x3f_3985_);
lean_inc(v_ltInst_x3f_3984_);
lean_inc(v_leInst_x3f_3983_);
lean_inc(v_intModuleInst_3982_);
lean_inc(v_u_3981_);
lean_inc(v_type_3980_);
lean_inc(v_ringId_x3f_3979_);
lean_inc(v_id_3978_);
lean_dec(v_v_3977_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4035_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4024_; lean_object* v_xs_x27_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4029_; 
v___x_4024_ = lean_box(0);
v_xs_x27_4025_ = lean_array_fset(v_structs_3964_, v_a_3961_, v___x_4024_);
v___x_4026_ = lean_box(1);
v___x_4027_ = l_Lean_PersistentArray_set___redArg(v_occurs_4019_, v_x_3962_, v___x_4026_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 40, v___x_4027_);
v___x_4029_ = v___x_4022_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_id_3978_);
lean_ctor_set(v_reuseFailAlloc_4034_, 1, v_ringId_x3f_3979_);
lean_ctor_set(v_reuseFailAlloc_4034_, 2, v_type_3980_);
lean_ctor_set(v_reuseFailAlloc_4034_, 3, v_u_3981_);
lean_ctor_set(v_reuseFailAlloc_4034_, 4, v_intModuleInst_3982_);
lean_ctor_set(v_reuseFailAlloc_4034_, 5, v_leInst_x3f_3983_);
lean_ctor_set(v_reuseFailAlloc_4034_, 6, v_ltInst_x3f_3984_);
lean_ctor_set(v_reuseFailAlloc_4034_, 7, v_lawfulOrderLTInst_x3f_3985_);
lean_ctor_set(v_reuseFailAlloc_4034_, 8, v_isPreorderInst_x3f_3986_);
lean_ctor_set(v_reuseFailAlloc_4034_, 9, v_orderedAddInst_x3f_3987_);
lean_ctor_set(v_reuseFailAlloc_4034_, 10, v_isLinearInst_x3f_3988_);
lean_ctor_set(v_reuseFailAlloc_4034_, 11, v_noNatDivInst_x3f_3989_);
lean_ctor_set(v_reuseFailAlloc_4034_, 12, v_ringInst_x3f_3990_);
lean_ctor_set(v_reuseFailAlloc_4034_, 13, v_commRingInst_x3f_3991_);
lean_ctor_set(v_reuseFailAlloc_4034_, 14, v_orderedRingInst_x3f_3992_);
lean_ctor_set(v_reuseFailAlloc_4034_, 15, v_fieldInst_x3f_3993_);
lean_ctor_set(v_reuseFailAlloc_4034_, 16, v_charInst_x3f_3994_);
lean_ctor_set(v_reuseFailAlloc_4034_, 17, v_zero_3995_);
lean_ctor_set(v_reuseFailAlloc_4034_, 18, v_ofNatZero_3996_);
lean_ctor_set(v_reuseFailAlloc_4034_, 19, v_one_x3f_3997_);
lean_ctor_set(v_reuseFailAlloc_4034_, 20, v_leFn_x3f_3998_);
lean_ctor_set(v_reuseFailAlloc_4034_, 21, v_ltFn_x3f_3999_);
lean_ctor_set(v_reuseFailAlloc_4034_, 22, v_addFn_4000_);
lean_ctor_set(v_reuseFailAlloc_4034_, 23, v_zsmulFn_4001_);
lean_ctor_set(v_reuseFailAlloc_4034_, 24, v_nsmulFn_4002_);
lean_ctor_set(v_reuseFailAlloc_4034_, 25, v_zsmulFn_x3f_4003_);
lean_ctor_set(v_reuseFailAlloc_4034_, 26, v_nsmulFn_x3f_4004_);
lean_ctor_set(v_reuseFailAlloc_4034_, 27, v_homomulFn_x3f_4005_);
lean_ctor_set(v_reuseFailAlloc_4034_, 28, v_subFn_4006_);
lean_ctor_set(v_reuseFailAlloc_4034_, 29, v_negFn_4007_);
lean_ctor_set(v_reuseFailAlloc_4034_, 30, v_vars_4008_);
lean_ctor_set(v_reuseFailAlloc_4034_, 31, v_varMap_4009_);
lean_ctor_set(v_reuseFailAlloc_4034_, 32, v_lowers_4010_);
lean_ctor_set(v_reuseFailAlloc_4034_, 33, v_uppers_4011_);
lean_ctor_set(v_reuseFailAlloc_4034_, 34, v_diseqs_4012_);
lean_ctor_set(v_reuseFailAlloc_4034_, 35, v_assignment_4013_);
lean_ctor_set(v_reuseFailAlloc_4034_, 36, v_conflict_x3f_4015_);
lean_ctor_set(v_reuseFailAlloc_4034_, 37, v_diseqSplits_4016_);
lean_ctor_set(v_reuseFailAlloc_4034_, 38, v_elimEqs_4017_);
lean_ctor_set(v_reuseFailAlloc_4034_, 39, v_elimStack_4018_);
lean_ctor_set(v_reuseFailAlloc_4034_, 40, v___x_4027_);
lean_ctor_set(v_reuseFailAlloc_4034_, 41, v_ignored_4020_);
lean_ctor_set_uint8(v_reuseFailAlloc_4034_, sizeof(void*)*42, v_caseSplits_4014_);
v___x_4029_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
lean_object* v___x_4030_; lean_object* v___x_4032_; 
v___x_4030_ = lean_array_fset(v_xs_x27_4025_, v_a_3961_, v___x_4029_);
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 0, v___x_4030_);
v___x_4032_ = v___x_3975_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4030_);
lean_ctor_set(v_reuseFailAlloc_4033_, 1, v_typeIdOf_3965_);
lean_ctor_set(v_reuseFailAlloc_4033_, 2, v_exprToStructId_3966_);
lean_ctor_set(v_reuseFailAlloc_4033_, 3, v_exprToStructIdEntries_3967_);
lean_ctor_set(v_reuseFailAlloc_4033_, 4, v_forbiddenNatModules_3968_);
lean_ctor_set(v_reuseFailAlloc_4033_, 5, v_natStructs_3969_);
lean_ctor_set(v_reuseFailAlloc_4033_, 6, v_natTypeIdOf_3970_);
lean_ctor_set(v_reuseFailAlloc_4033_, 7, v_exprToNatStructId_3971_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed(lean_object* v_a_4045_, lean_object* v_x_4046_, lean_object* v_s_4047_){
_start:
{
lean_object* v_res_4048_; 
v_res_4048_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(v_a_4045_, v_x_4046_, v_s_4047_);
lean_dec(v_x_4046_);
lean_dec(v_a_4045_);
return v_res_4048_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object* v_a_4049_, lean_object* v_x_4050_, lean_object* v_c_4051_, lean_object* v_init_4052_, lean_object* v_x_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
if (lean_obj_tag(v_x_4053_) == 0)
{
lean_object* v_k_4066_; lean_object* v_l_4067_; lean_object* v_r_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v_k_4066_ = lean_ctor_get(v_x_4053_, 1);
lean_inc(v_k_4066_);
v_l_4067_ = lean_ctor_get(v_x_4053_, 3);
lean_inc(v_l_4067_);
v_r_4068_ = lean_ctor_get(v_x_4053_, 4);
lean_inc(v_r_4068_);
lean_dec_ref_known(v_x_4053_, 5);
v___x_4069_ = lean_box(0);
lean_inc_ref(v_c_4051_);
lean_inc(v_x_4050_);
lean_inc(v_a_4049_);
v___x_4070_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4049_, v_x_4050_, v_c_4051_, v_init_4052_, v_l_4067_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v___x_4071_; 
lean_dec_ref_known(v___x_4070_, 1);
lean_inc_ref(v_c_4051_);
lean_inc(v_x_4050_);
lean_inc(v_a_4049_);
v___x_4071_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4049_, v_x_4050_, v_c_4051_, v_k_4066_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_dec_ref_known(v___x_4071_, 1);
v_init_4052_ = v___x_4069_;
v_x_4053_ = v_r_4068_;
goto _start;
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_dec(v_r_4068_);
lean_dec_ref(v_c_4051_);
lean_dec(v_x_4050_);
lean_dec(v_a_4049_);
v_a_4073_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4071_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4071_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
else
{
lean_dec(v_r_4068_);
lean_dec(v_k_4066_);
lean_dec_ref(v_c_4051_);
lean_dec(v_x_4050_);
lean_dec(v_a_4049_);
return v___x_4070_;
}
}
else
{
lean_object* v___x_4081_; lean_object* v___x_4082_; 
lean_dec_ref(v_c_4051_);
lean_dec(v_x_4050_);
lean_dec(v_a_4049_);
v___x_4081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4081_, 0, v_init_4052_);
v___x_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4081_);
return v___x_4082_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object** _args){
lean_object* v_a_4083_ = _args[0];
lean_object* v_x_4084_ = _args[1];
lean_object* v_c_4085_ = _args[2];
lean_object* v_init_4086_ = _args[3];
lean_object* v_x_4087_ = _args[4];
lean_object* v___y_4088_ = _args[5];
lean_object* v___y_4089_ = _args[6];
lean_object* v___y_4090_ = _args[7];
lean_object* v___y_4091_ = _args[8];
lean_object* v___y_4092_ = _args[9];
lean_object* v___y_4093_ = _args[10];
lean_object* v___y_4094_ = _args[11];
lean_object* v___y_4095_ = _args[12];
lean_object* v___y_4096_ = _args[13];
lean_object* v___y_4097_ = _args[14];
lean_object* v___y_4098_ = _args[15];
lean_object* v___y_4099_ = _args[16];
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4083_, v_x_4084_, v_c_4085_, v_init_4086_, v_x_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec(v___y_4089_);
lean_dec(v___y_4088_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object* v_a_4101_, lean_object* v_x_4102_, lean_object* v_c_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_){
_start:
{
lean_object* v___f_4116_; lean_object* v___x_4117_; 
lean_inc(v_x_4102_);
lean_inc(v_a_4104_);
v___f_4116_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4116_, 0, v_a_4104_);
lean_closure_set(v___f_4116_, 1, v_x_4102_);
v___x_4117_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_object* v_a_4118_; lean_object* v___y_4120_; lean_object* v_occurs_4142_; lean_object* v_size_4143_; lean_object* v___x_4144_; uint8_t v___x_4145_; 
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
lean_inc(v_a_4118_);
lean_dec_ref_known(v___x_4117_, 1);
v_occurs_4142_ = lean_ctor_get(v_a_4118_, 40);
lean_inc_ref(v_occurs_4142_);
lean_dec(v_a_4118_);
v_size_4143_ = lean_ctor_get(v_occurs_4142_, 2);
v___x_4144_ = lean_box(1);
v___x_4145_ = lean_nat_dec_lt(v_x_4102_, v_size_4143_);
if (v___x_4145_ == 0)
{
lean_object* v___x_4146_; 
lean_dec_ref(v_occurs_4142_);
v___x_4146_ = l_outOfBounds___redArg(v___x_4144_);
v___y_4120_ = v___x_4146_;
goto v___jp_4119_;
}
else
{
lean_object* v___x_4147_; 
v___x_4147_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4144_, v_occurs_4142_, v_x_4102_);
lean_dec_ref(v_occurs_4142_);
v___y_4120_ = v___x_4147_;
goto v___jp_4119_;
}
v___jp_4119_:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4121_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4122_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4121_, v___f_4116_, v_a_4105_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_object* v___x_4123_; 
lean_dec_ref_known(v___x_4122_, 1);
lean_inc_ref(v_c_4103_);
lean_inc_n(v_x_4102_, 2);
lean_inc(v_a_4101_);
v___x_4123_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4101_, v_x_4102_, v_c_4103_, v_x_4102_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_object* v___x_4124_; lean_object* v___x_4125_; 
lean_dec_ref_known(v___x_4123_, 1);
v___x_4124_ = lean_box(0);
v___x_4125_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4101_, v_x_4102_, v_c_4103_, v___x_4124_, v___y_4120_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4132_; 
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4132_ == 0)
{
lean_object* v_unused_4133_; 
v_unused_4133_ = lean_ctor_get(v___x_4125_, 0);
lean_dec(v_unused_4133_);
v___x_4127_ = v___x_4125_;
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
else
{
lean_dec(v___x_4125_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4130_; 
if (v_isShared_4128_ == 0)
{
lean_ctor_set(v___x_4127_, 0, v___x_4124_);
v___x_4130_ = v___x_4127_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v___x_4124_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
v_a_4134_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___x_4125_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4125_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
else
{
lean_dec(v___y_4120_);
lean_dec_ref(v_c_4103_);
lean_dec(v_x_4102_);
lean_dec(v_a_4101_);
return v___x_4123_;
}
}
else
{
lean_dec(v___y_4120_);
lean_dec_ref(v_c_4103_);
lean_dec(v_x_4102_);
lean_dec(v_a_4101_);
return v___x_4122_;
}
}
}
else
{
lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4155_; 
lean_dec_ref(v___f_4116_);
lean_dec_ref(v_c_4103_);
lean_dec(v_x_4102_);
lean_dec(v_a_4101_);
v_a_4148_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4150_ = v___x_4117_;
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_4117_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4153_; 
if (v_isShared_4151_ == 0)
{
v___x_4153_ = v___x_4150_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_a_4148_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___boxed(lean_object* v_a_4156_, lean_object* v_x_4157_, lean_object* v_c_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v_a_4156_, v_x_4157_, v_c_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_a_4165_);
lean_dec_ref(v_a_4164_);
lean_dec(v_a_4163_);
lean_dec_ref(v_a_4162_);
lean_dec(v_a_4161_);
lean_dec(v_a_4160_);
lean_dec(v_a_4159_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(lean_object* v_c_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_){
_start:
{
lean_object* v_p_4189_; 
v_p_4189_ = lean_ctor_get(v_c_4172_, 0);
if (lean_obj_tag(v_p_4189_) == 1)
{
lean_object* v_k_4190_; lean_object* v_v_4191_; lean_object* v_p_4192_; lean_object* v_y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___x_4243_; lean_object* v___x_4244_; uint8_t v___x_4245_; 
v_k_4190_ = lean_ctor_get(v_p_4189_, 0);
v_v_4191_ = lean_ctor_get(v_p_4189_, 1);
v_p_4192_ = lean_ctor_get(v_p_4189_, 2);
v___x_4243_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_4244_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4245_ = lean_int_dec_eq(v_k_4190_, v___x_4244_);
if (v___x_4245_ == 0)
{
uint8_t v___x_4246_; 
v___x_4246_ = lean_int_dec_eq(v_k_4190_, v___x_4243_);
if (v___x_4246_ == 0)
{
goto v___jp_4185_;
}
else
{
if (lean_obj_tag(v_p_4192_) == 1)
{
lean_object* v_k_4247_; lean_object* v_v_4248_; lean_object* v_p_4249_; uint8_t v___x_4250_; 
v_k_4247_ = lean_ctor_get(v_p_4192_, 0);
v_v_4248_ = lean_ctor_get(v_p_4192_, 1);
v_p_4249_ = lean_ctor_get(v_p_4192_, 2);
v___x_4250_ = lean_int_dec_eq(v_k_4247_, v___x_4244_);
if (v___x_4250_ == 0)
{
goto v___jp_4185_;
}
else
{
if (lean_obj_tag(v_p_4249_) == 0)
{
v_y_4194_ = v_v_4248_;
v___y_4195_ = v_a_4173_;
v___y_4196_ = v_a_4174_;
v___y_4197_ = v_a_4175_;
v___y_4198_ = v_a_4176_;
v___y_4199_ = v_a_4177_;
v___y_4200_ = v_a_4178_;
v___y_4201_ = v_a_4179_;
v___y_4202_ = v_a_4180_;
v___y_4203_ = v_a_4181_;
v___y_4204_ = v_a_4182_;
v___y_4205_ = v_a_4183_;
goto v___jp_4193_;
}
else
{
goto v___jp_4185_;
}
}
}
else
{
goto v___jp_4185_;
}
}
}
else
{
if (lean_obj_tag(v_p_4192_) == 1)
{
lean_object* v_k_4251_; lean_object* v_v_4252_; lean_object* v_p_4253_; uint8_t v___x_4254_; 
v_k_4251_ = lean_ctor_get(v_p_4192_, 0);
v_v_4252_ = lean_ctor_get(v_p_4192_, 1);
v_p_4253_ = lean_ctor_get(v_p_4192_, 2);
v___x_4254_ = lean_int_dec_eq(v_k_4251_, v___x_4243_);
if (v___x_4254_ == 0)
{
goto v___jp_4185_;
}
else
{
if (lean_obj_tag(v_p_4253_) == 0)
{
v_y_4194_ = v_v_4252_;
v___y_4195_ = v_a_4173_;
v___y_4196_ = v_a_4174_;
v___y_4197_ = v_a_4175_;
v___y_4198_ = v_a_4176_;
v___y_4199_ = v_a_4177_;
v___y_4200_ = v_a_4178_;
v___y_4201_ = v_a_4179_;
v___y_4202_ = v_a_4180_;
v___y_4203_ = v_a_4181_;
v___y_4204_ = v_a_4182_;
v___y_4205_ = v_a_4183_;
goto v___jp_4193_;
}
else
{
goto v___jp_4185_;
}
}
}
else
{
goto v___jp_4185_;
}
}
v___jp_4193_:
{
lean_object* v___x_4206_; 
v___x_4206_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_v_4191_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v_a_4207_; lean_object* v___x_4208_; 
v_a_4207_ = lean_ctor_get(v___x_4206_, 0);
lean_inc(v_a_4207_);
lean_dec_ref_known(v___x_4206_, 1);
v___x_4208_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; lean_object* v___x_4210_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_a_4209_);
lean_dec_ref_known(v___x_4208_, 1);
v___x_4210_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_4207_, v_a_4209_, v___y_4196_);
lean_dec(v_a_4209_);
lean_dec(v_a_4207_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4226_; 
v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4213_ = v___x_4210_;
v_isShared_4214_ = v_isSharedCheck_4226_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4210_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4226_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
uint8_t v___x_4215_; 
v___x_4215_ = lean_unbox(v_a_4211_);
lean_dec(v_a_4211_);
if (v___x_4215_ == 0)
{
uint8_t v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4219_; 
v___x_4216_ = 1;
v___x_4217_ = lean_box(v___x_4216_);
if (v_isShared_4214_ == 0)
{
lean_ctor_set(v___x_4213_, 0, v___x_4217_);
v___x_4219_ = v___x_4213_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4217_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
else
{
uint8_t v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4224_; 
v___x_4221_ = 0;
v___x_4222_ = lean_box(v___x_4221_);
if (v_isShared_4214_ == 0)
{
lean_ctor_set(v___x_4213_, 0, v___x_4222_);
v___x_4224_ = v___x_4213_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4222_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
else
{
return v___x_4210_;
}
}
else
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4234_; 
lean_dec(v_a_4207_);
v_a_4227_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_4208_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4208_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4227_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
v_a_4235_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4206_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4206_);
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
else
{
goto v___jp_4185_;
}
v___jp_4185_:
{
uint8_t v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4186_ = 0;
v___x_4187_ = lean_box(v___x_4186_);
v___x_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4187_);
return v___x_4188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq___boxed(lean_object* v_c_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_){
_start:
{
lean_object* v_res_4268_; 
v_res_4268_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v_c_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_, v_a_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_);
lean_dec(v_a_4266_);
lean_dec_ref(v_a_4265_);
lean_dec(v_a_4264_);
lean_dec_ref(v_a_4263_);
lean_dec(v_a_4262_);
lean_dec_ref(v_a_4261_);
lean_dec(v_a_4260_);
lean_dec_ref(v_a_4259_);
lean_dec(v_a_4258_);
lean_dec(v_a_4257_);
lean_dec(v_a_4256_);
lean_dec_ref(v_c_4255_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(lean_object* v_c_4269_){
_start:
{
lean_object* v_p_4271_; 
v_p_4271_ = lean_ctor_get(v_c_4269_, 0);
if (lean_obj_tag(v_p_4271_) == 1)
{
lean_object* v_k_4272_; lean_object* v___x_4273_; uint8_t v___x_4274_; 
v_k_4272_ = lean_ctor_get(v_p_4271_, 0);
v___x_4273_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_4274_ = lean_int_dec_lt(v_k_4272_, v___x_4273_);
if (v___x_4274_ == 0)
{
lean_object* v___x_4275_; 
v___x_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4275_, 0, v_c_4269_);
return v___x_4275_;
}
else
{
lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4276_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_4271_);
v___x_4277_ = l_Lean_Grind_Linarith_Poly_mul(v_p_4271_, v___x_4276_);
v___x_4278_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4278_, 0, v_c_4269_);
v___x_4279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4277_);
lean_ctor_set(v___x_4279_, 1, v___x_4278_);
v___x_4280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4279_);
return v___x_4280_;
}
}
else
{
lean_object* v___x_4281_; 
v___x_4281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4281_, 0, v_c_4269_);
return v___x_4281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg___boxed(lean_object* v_c_4282_, lean_object* v_a_4283_){
_start:
{
lean_object* v_res_4284_; 
v_res_4284_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4282_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(lean_object* v_c_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4285_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___boxed(lean_object* v_c_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_){
_start:
{
lean_object* v_res_4312_; 
v_res_4312_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(v_c_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_);
lean_dec(v_a_4310_);
lean_dec_ref(v_a_4309_);
lean_dec(v_a_4308_);
lean_dec_ref(v_a_4307_);
lean_dec(v_a_4306_);
lean_dec_ref(v_a_4305_);
lean_dec(v_a_4304_);
lean_dec_ref(v_a_4303_);
lean_dec(v_a_4302_);
lean_dec(v_a_4301_);
lean_dec(v_a_4300_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(lean_object* v___y_4313_, lean_object* v_snd_4314_, lean_object* v_fst_4315_, lean_object* v_s_4316_){
_start:
{
lean_object* v_structs_4317_; lean_object* v_typeIdOf_4318_; lean_object* v_exprToStructId_4319_; lean_object* v_exprToStructIdEntries_4320_; lean_object* v_forbiddenNatModules_4321_; lean_object* v_natStructs_4322_; lean_object* v_natTypeIdOf_4323_; lean_object* v_exprToNatStructId_4324_; lean_object* v___x_4325_; uint8_t v___x_4326_; 
v_structs_4317_ = lean_ctor_get(v_s_4316_, 0);
v_typeIdOf_4318_ = lean_ctor_get(v_s_4316_, 1);
v_exprToStructId_4319_ = lean_ctor_get(v_s_4316_, 2);
v_exprToStructIdEntries_4320_ = lean_ctor_get(v_s_4316_, 3);
v_forbiddenNatModules_4321_ = lean_ctor_get(v_s_4316_, 4);
v_natStructs_4322_ = lean_ctor_get(v_s_4316_, 5);
v_natTypeIdOf_4323_ = lean_ctor_get(v_s_4316_, 6);
v_exprToNatStructId_4324_ = lean_ctor_get(v_s_4316_, 7);
v___x_4325_ = lean_array_get_size(v_structs_4317_);
v___x_4326_ = lean_nat_dec_lt(v___y_4313_, v___x_4325_);
if (v___x_4326_ == 0)
{
lean_dec(v_fst_4315_);
lean_dec_ref(v_snd_4314_);
return v_s_4316_;
}
else
{
lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4390_; 
lean_inc_ref(v_exprToNatStructId_4324_);
lean_inc_ref(v_natTypeIdOf_4323_);
lean_inc_ref(v_natStructs_4322_);
lean_inc_ref(v_forbiddenNatModules_4321_);
lean_inc_ref(v_exprToStructIdEntries_4320_);
lean_inc_ref(v_exprToStructId_4319_);
lean_inc_ref(v_typeIdOf_4318_);
lean_inc_ref(v_structs_4317_);
v_isSharedCheck_4390_ = !lean_is_exclusive(v_s_4316_);
if (v_isSharedCheck_4390_ == 0)
{
lean_object* v_unused_4391_; lean_object* v_unused_4392_; lean_object* v_unused_4393_; lean_object* v_unused_4394_; lean_object* v_unused_4395_; lean_object* v_unused_4396_; lean_object* v_unused_4397_; lean_object* v_unused_4398_; 
v_unused_4391_ = lean_ctor_get(v_s_4316_, 7);
lean_dec(v_unused_4391_);
v_unused_4392_ = lean_ctor_get(v_s_4316_, 6);
lean_dec(v_unused_4392_);
v_unused_4393_ = lean_ctor_get(v_s_4316_, 5);
lean_dec(v_unused_4393_);
v_unused_4394_ = lean_ctor_get(v_s_4316_, 4);
lean_dec(v_unused_4394_);
v_unused_4395_ = lean_ctor_get(v_s_4316_, 3);
lean_dec(v_unused_4395_);
v_unused_4396_ = lean_ctor_get(v_s_4316_, 2);
lean_dec(v_unused_4396_);
v_unused_4397_ = lean_ctor_get(v_s_4316_, 1);
lean_dec(v_unused_4397_);
v_unused_4398_ = lean_ctor_get(v_s_4316_, 0);
lean_dec(v_unused_4398_);
v___x_4328_ = v_s_4316_;
v_isShared_4329_ = v_isSharedCheck_4390_;
goto v_resetjp_4327_;
}
else
{
lean_dec(v_s_4316_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4390_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v_v_4330_; lean_object* v_id_4331_; lean_object* v_ringId_x3f_4332_; lean_object* v_type_4333_; lean_object* v_u_4334_; lean_object* v_intModuleInst_4335_; lean_object* v_leInst_x3f_4336_; lean_object* v_ltInst_x3f_4337_; lean_object* v_lawfulOrderLTInst_x3f_4338_; lean_object* v_isPreorderInst_x3f_4339_; lean_object* v_orderedAddInst_x3f_4340_; lean_object* v_isLinearInst_x3f_4341_; lean_object* v_noNatDivInst_x3f_4342_; lean_object* v_ringInst_x3f_4343_; lean_object* v_commRingInst_x3f_4344_; lean_object* v_orderedRingInst_x3f_4345_; lean_object* v_fieldInst_x3f_4346_; lean_object* v_charInst_x3f_4347_; lean_object* v_zero_4348_; lean_object* v_ofNatZero_4349_; lean_object* v_one_x3f_4350_; lean_object* v_leFn_x3f_4351_; lean_object* v_ltFn_x3f_4352_; lean_object* v_addFn_4353_; lean_object* v_zsmulFn_4354_; lean_object* v_nsmulFn_4355_; lean_object* v_zsmulFn_x3f_4356_; lean_object* v_nsmulFn_x3f_4357_; lean_object* v_homomulFn_x3f_4358_; lean_object* v_subFn_4359_; lean_object* v_negFn_4360_; lean_object* v_vars_4361_; lean_object* v_varMap_4362_; lean_object* v_lowers_4363_; lean_object* v_uppers_4364_; lean_object* v_diseqs_4365_; lean_object* v_assignment_4366_; uint8_t v_caseSplits_4367_; lean_object* v_conflict_x3f_4368_; lean_object* v_diseqSplits_4369_; lean_object* v_elimEqs_4370_; lean_object* v_elimStack_4371_; lean_object* v_occurs_4372_; lean_object* v_ignored_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4389_; 
v_v_4330_ = lean_array_fget(v_structs_4317_, v___y_4313_);
v_id_4331_ = lean_ctor_get(v_v_4330_, 0);
v_ringId_x3f_4332_ = lean_ctor_get(v_v_4330_, 1);
v_type_4333_ = lean_ctor_get(v_v_4330_, 2);
v_u_4334_ = lean_ctor_get(v_v_4330_, 3);
v_intModuleInst_4335_ = lean_ctor_get(v_v_4330_, 4);
v_leInst_x3f_4336_ = lean_ctor_get(v_v_4330_, 5);
v_ltInst_x3f_4337_ = lean_ctor_get(v_v_4330_, 6);
v_lawfulOrderLTInst_x3f_4338_ = lean_ctor_get(v_v_4330_, 7);
v_isPreorderInst_x3f_4339_ = lean_ctor_get(v_v_4330_, 8);
v_orderedAddInst_x3f_4340_ = lean_ctor_get(v_v_4330_, 9);
v_isLinearInst_x3f_4341_ = lean_ctor_get(v_v_4330_, 10);
v_noNatDivInst_x3f_4342_ = lean_ctor_get(v_v_4330_, 11);
v_ringInst_x3f_4343_ = lean_ctor_get(v_v_4330_, 12);
v_commRingInst_x3f_4344_ = lean_ctor_get(v_v_4330_, 13);
v_orderedRingInst_x3f_4345_ = lean_ctor_get(v_v_4330_, 14);
v_fieldInst_x3f_4346_ = lean_ctor_get(v_v_4330_, 15);
v_charInst_x3f_4347_ = lean_ctor_get(v_v_4330_, 16);
v_zero_4348_ = lean_ctor_get(v_v_4330_, 17);
v_ofNatZero_4349_ = lean_ctor_get(v_v_4330_, 18);
v_one_x3f_4350_ = lean_ctor_get(v_v_4330_, 19);
v_leFn_x3f_4351_ = lean_ctor_get(v_v_4330_, 20);
v_ltFn_x3f_4352_ = lean_ctor_get(v_v_4330_, 21);
v_addFn_4353_ = lean_ctor_get(v_v_4330_, 22);
v_zsmulFn_4354_ = lean_ctor_get(v_v_4330_, 23);
v_nsmulFn_4355_ = lean_ctor_get(v_v_4330_, 24);
v_zsmulFn_x3f_4356_ = lean_ctor_get(v_v_4330_, 25);
v_nsmulFn_x3f_4357_ = lean_ctor_get(v_v_4330_, 26);
v_homomulFn_x3f_4358_ = lean_ctor_get(v_v_4330_, 27);
v_subFn_4359_ = lean_ctor_get(v_v_4330_, 28);
v_negFn_4360_ = lean_ctor_get(v_v_4330_, 29);
v_vars_4361_ = lean_ctor_get(v_v_4330_, 30);
v_varMap_4362_ = lean_ctor_get(v_v_4330_, 31);
v_lowers_4363_ = lean_ctor_get(v_v_4330_, 32);
v_uppers_4364_ = lean_ctor_get(v_v_4330_, 33);
v_diseqs_4365_ = lean_ctor_get(v_v_4330_, 34);
v_assignment_4366_ = lean_ctor_get(v_v_4330_, 35);
v_caseSplits_4367_ = lean_ctor_get_uint8(v_v_4330_, sizeof(void*)*42);
v_conflict_x3f_4368_ = lean_ctor_get(v_v_4330_, 36);
v_diseqSplits_4369_ = lean_ctor_get(v_v_4330_, 37);
v_elimEqs_4370_ = lean_ctor_get(v_v_4330_, 38);
v_elimStack_4371_ = lean_ctor_get(v_v_4330_, 39);
v_occurs_4372_ = lean_ctor_get(v_v_4330_, 40);
v_ignored_4373_ = lean_ctor_get(v_v_4330_, 41);
v_isSharedCheck_4389_ = !lean_is_exclusive(v_v_4330_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4375_ = v_v_4330_;
v_isShared_4376_ = v_isSharedCheck_4389_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_ignored_4373_);
lean_inc(v_occurs_4372_);
lean_inc(v_elimStack_4371_);
lean_inc(v_elimEqs_4370_);
lean_inc(v_diseqSplits_4369_);
lean_inc(v_conflict_x3f_4368_);
lean_inc(v_assignment_4366_);
lean_inc(v_diseqs_4365_);
lean_inc(v_uppers_4364_);
lean_inc(v_lowers_4363_);
lean_inc(v_varMap_4362_);
lean_inc(v_vars_4361_);
lean_inc(v_negFn_4360_);
lean_inc(v_subFn_4359_);
lean_inc(v_homomulFn_x3f_4358_);
lean_inc(v_nsmulFn_x3f_4357_);
lean_inc(v_zsmulFn_x3f_4356_);
lean_inc(v_nsmulFn_4355_);
lean_inc(v_zsmulFn_4354_);
lean_inc(v_addFn_4353_);
lean_inc(v_ltFn_x3f_4352_);
lean_inc(v_leFn_x3f_4351_);
lean_inc(v_one_x3f_4350_);
lean_inc(v_ofNatZero_4349_);
lean_inc(v_zero_4348_);
lean_inc(v_charInst_x3f_4347_);
lean_inc(v_fieldInst_x3f_4346_);
lean_inc(v_orderedRingInst_x3f_4345_);
lean_inc(v_commRingInst_x3f_4344_);
lean_inc(v_ringInst_x3f_4343_);
lean_inc(v_noNatDivInst_x3f_4342_);
lean_inc(v_isLinearInst_x3f_4341_);
lean_inc(v_orderedAddInst_x3f_4340_);
lean_inc(v_isPreorderInst_x3f_4339_);
lean_inc(v_lawfulOrderLTInst_x3f_4338_);
lean_inc(v_ltInst_x3f_4337_);
lean_inc(v_leInst_x3f_4336_);
lean_inc(v_intModuleInst_4335_);
lean_inc(v_u_4334_);
lean_inc(v_type_4333_);
lean_inc(v_ringId_x3f_4332_);
lean_inc(v_id_4331_);
lean_dec(v_v_4330_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4389_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4377_; lean_object* v_xs_x27_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4383_; 
v___x_4377_ = lean_box(0);
v_xs_x27_4378_ = lean_array_fset(v_structs_4317_, v___y_4313_, v___x_4377_);
v___x_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4379_, 0, v_snd_4314_);
v___x_4380_ = l_Lean_PersistentArray_set___redArg(v_elimEqs_4370_, v_fst_4315_, v___x_4379_);
v___x_4381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4381_, 0, v_fst_4315_);
lean_ctor_set(v___x_4381_, 1, v_elimStack_4371_);
if (v_isShared_4376_ == 0)
{
lean_ctor_set(v___x_4375_, 39, v___x_4381_);
lean_ctor_set(v___x_4375_, 38, v___x_4380_);
v___x_4383_ = v___x_4375_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_id_4331_);
lean_ctor_set(v_reuseFailAlloc_4388_, 1, v_ringId_x3f_4332_);
lean_ctor_set(v_reuseFailAlloc_4388_, 2, v_type_4333_);
lean_ctor_set(v_reuseFailAlloc_4388_, 3, v_u_4334_);
lean_ctor_set(v_reuseFailAlloc_4388_, 4, v_intModuleInst_4335_);
lean_ctor_set(v_reuseFailAlloc_4388_, 5, v_leInst_x3f_4336_);
lean_ctor_set(v_reuseFailAlloc_4388_, 6, v_ltInst_x3f_4337_);
lean_ctor_set(v_reuseFailAlloc_4388_, 7, v_lawfulOrderLTInst_x3f_4338_);
lean_ctor_set(v_reuseFailAlloc_4388_, 8, v_isPreorderInst_x3f_4339_);
lean_ctor_set(v_reuseFailAlloc_4388_, 9, v_orderedAddInst_x3f_4340_);
lean_ctor_set(v_reuseFailAlloc_4388_, 10, v_isLinearInst_x3f_4341_);
lean_ctor_set(v_reuseFailAlloc_4388_, 11, v_noNatDivInst_x3f_4342_);
lean_ctor_set(v_reuseFailAlloc_4388_, 12, v_ringInst_x3f_4343_);
lean_ctor_set(v_reuseFailAlloc_4388_, 13, v_commRingInst_x3f_4344_);
lean_ctor_set(v_reuseFailAlloc_4388_, 14, v_orderedRingInst_x3f_4345_);
lean_ctor_set(v_reuseFailAlloc_4388_, 15, v_fieldInst_x3f_4346_);
lean_ctor_set(v_reuseFailAlloc_4388_, 16, v_charInst_x3f_4347_);
lean_ctor_set(v_reuseFailAlloc_4388_, 17, v_zero_4348_);
lean_ctor_set(v_reuseFailAlloc_4388_, 18, v_ofNatZero_4349_);
lean_ctor_set(v_reuseFailAlloc_4388_, 19, v_one_x3f_4350_);
lean_ctor_set(v_reuseFailAlloc_4388_, 20, v_leFn_x3f_4351_);
lean_ctor_set(v_reuseFailAlloc_4388_, 21, v_ltFn_x3f_4352_);
lean_ctor_set(v_reuseFailAlloc_4388_, 22, v_addFn_4353_);
lean_ctor_set(v_reuseFailAlloc_4388_, 23, v_zsmulFn_4354_);
lean_ctor_set(v_reuseFailAlloc_4388_, 24, v_nsmulFn_4355_);
lean_ctor_set(v_reuseFailAlloc_4388_, 25, v_zsmulFn_x3f_4356_);
lean_ctor_set(v_reuseFailAlloc_4388_, 26, v_nsmulFn_x3f_4357_);
lean_ctor_set(v_reuseFailAlloc_4388_, 27, v_homomulFn_x3f_4358_);
lean_ctor_set(v_reuseFailAlloc_4388_, 28, v_subFn_4359_);
lean_ctor_set(v_reuseFailAlloc_4388_, 29, v_negFn_4360_);
lean_ctor_set(v_reuseFailAlloc_4388_, 30, v_vars_4361_);
lean_ctor_set(v_reuseFailAlloc_4388_, 31, v_varMap_4362_);
lean_ctor_set(v_reuseFailAlloc_4388_, 32, v_lowers_4363_);
lean_ctor_set(v_reuseFailAlloc_4388_, 33, v_uppers_4364_);
lean_ctor_set(v_reuseFailAlloc_4388_, 34, v_diseqs_4365_);
lean_ctor_set(v_reuseFailAlloc_4388_, 35, v_assignment_4366_);
lean_ctor_set(v_reuseFailAlloc_4388_, 36, v_conflict_x3f_4368_);
lean_ctor_set(v_reuseFailAlloc_4388_, 37, v_diseqSplits_4369_);
lean_ctor_set(v_reuseFailAlloc_4388_, 38, v___x_4380_);
lean_ctor_set(v_reuseFailAlloc_4388_, 39, v___x_4381_);
lean_ctor_set(v_reuseFailAlloc_4388_, 40, v_occurs_4372_);
lean_ctor_set(v_reuseFailAlloc_4388_, 41, v_ignored_4373_);
lean_ctor_set_uint8(v_reuseFailAlloc_4388_, sizeof(void*)*42, v_caseSplits_4367_);
v___x_4383_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
lean_object* v___x_4384_; lean_object* v___x_4386_; 
v___x_4384_ = lean_array_fset(v_xs_x27_4378_, v___y_4313_, v___x_4383_);
if (v_isShared_4329_ == 0)
{
lean_ctor_set(v___x_4328_, 0, v___x_4384_);
v___x_4386_ = v___x_4328_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v___x_4384_);
lean_ctor_set(v_reuseFailAlloc_4387_, 1, v_typeIdOf_4318_);
lean_ctor_set(v_reuseFailAlloc_4387_, 2, v_exprToStructId_4319_);
lean_ctor_set(v_reuseFailAlloc_4387_, 3, v_exprToStructIdEntries_4320_);
lean_ctor_set(v_reuseFailAlloc_4387_, 4, v_forbiddenNatModules_4321_);
lean_ctor_set(v_reuseFailAlloc_4387_, 5, v_natStructs_4322_);
lean_ctor_set(v_reuseFailAlloc_4387_, 6, v_natTypeIdOf_4323_);
lean_ctor_set(v_reuseFailAlloc_4387_, 7, v_exprToNatStructId_4324_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed(lean_object* v___y_4399_, lean_object* v_snd_4400_, lean_object* v_fst_4401_, lean_object* v_s_4402_){
_start:
{
lean_object* v_res_4403_; 
v_res_4403_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(v___y_4399_, v_snd_4400_, v_fst_4401_, v_s_4402_);
lean_dec(v___y_4399_);
return v_res_4403_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1(void){
_start:
{
lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0));
v___x_4406_ = l_Lean_stringToMessageData(v___x_4405_);
return v___x_4406_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4(void){
_start:
{
lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4413_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4414_ = l_Lean_Name_append(v___x_4413_, v___x_4412_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object* v_c_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_){
_start:
{
lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4453_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v_toCold_4494_; lean_object* v_options_4495_; lean_object* v_inheritedTraceOptions_4496_; uint8_t v_hasTrace_4497_; lean_object* v___y_4499_; lean_object* v___y_4500_; lean_object* v___y_4501_; lean_object* v___y_4502_; lean_object* v___y_4503_; lean_object* v___y_4504_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v_options_4514_; lean_object* v_inheritedTraceOptions_4515_; lean_object* v___y_4516_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; 
v_toCold_4494_ = lean_ctor_get(v_a_4425_, 0);
v_options_4495_ = lean_ctor_get(v_toCold_4494_, 2);
v_inheritedTraceOptions_4496_ = lean_ctor_get(v_toCold_4494_, 11);
v_hasTrace_4497_ = lean_ctor_get_uint8(v_options_4495_, sizeof(void*)*1);
if (v_hasTrace_4497_ == 0)
{
v___y_4533_ = v_a_4416_;
v___y_4534_ = v_a_4417_;
v___y_4535_ = v_a_4418_;
v___y_4536_ = v_a_4419_;
v___y_4537_ = v_a_4420_;
v___y_4538_ = v_a_4421_;
v___y_4539_ = v_a_4422_;
v___y_4540_ = v_a_4423_;
v___y_4541_ = v_a_4424_;
v___y_4542_ = v_a_4425_;
v___y_4543_ = v_a_4426_;
goto v___jp_4532_;
}
else
{
lean_object* v_cls_4641_; lean_object* v___x_4642_; uint8_t v___x_4643_; 
v_cls_4641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_4642_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_4643_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4496_, v_options_4495_, v___x_4642_);
if (v___x_4643_ == 0)
{
v___y_4533_ = v_a_4416_;
v___y_4534_ = v_a_4417_;
v___y_4535_ = v_a_4418_;
v___y_4536_ = v_a_4419_;
v___y_4537_ = v_a_4420_;
v___y_4538_ = v_a_4421_;
v___y_4539_ = v_a_4422_;
v___y_4540_ = v_a_4423_;
v___y_4541_ = v_a_4424_;
v___y_4542_ = v_a_4425_;
v___y_4543_ = v_a_4426_;
goto v___jp_4532_;
}
else
{
lean_object* v___x_4644_; 
v___x_4644_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_object* v_a_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; 
v_a_4645_ = lean_ctor_get(v___x_4644_, 0);
lean_inc(v_a_4645_);
lean_dec_ref_known(v___x_4644_, 1);
v___x_4646_ = l_Lean_MessageData_ofExpr(v_a_4645_);
v___x_4647_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4641_, v___x_4646_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_);
if (lean_obj_tag(v___x_4647_) == 0)
{
lean_dec_ref_known(v___x_4647_, 1);
v___y_4533_ = v_a_4416_;
v___y_4534_ = v_a_4417_;
v___y_4535_ = v_a_4418_;
v___y_4536_ = v_a_4419_;
v___y_4537_ = v_a_4420_;
v___y_4538_ = v_a_4421_;
v___y_4539_ = v_a_4422_;
v___y_4540_ = v_a_4423_;
v___y_4541_ = v_a_4424_;
v___y_4542_ = v_a_4425_;
v___y_4543_ = v_a_4426_;
goto v___jp_4532_;
}
else
{
lean_dec_ref(v_c_4415_);
return v___x_4647_;
}
}
else
{
lean_object* v_a_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4655_; 
lean_dec_ref(v_c_4415_);
v_a_4648_ = lean_ctor_get(v___x_4644_, 0);
v_isSharedCheck_4655_ = !lean_is_exclusive(v___x_4644_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4650_ = v___x_4644_;
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_a_4648_);
lean_dec(v___x_4644_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v___x_4653_; 
if (v_isShared_4651_ == 0)
{
v___x_4653_ = v___x_4650_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v_a_4648_);
v___x_4653_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
return v___x_4653_;
}
}
}
}
}
v___jp_4428_:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4429_ = lean_box(0);
v___x_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4429_);
return v___x_4430_;
}
v___jp_4431_:
{
lean_object* v___f_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
lean_inc(v___y_4437_);
v___f_4448_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4448_, 0, v___y_4437_);
lean_closure_set(v___f_4448_, 1, v___y_4433_);
lean_closure_set(v___f_4448_, 2, v___y_4432_);
v___x_4449_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4450_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4449_, v___f_4448_, v___y_4438_);
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_object* v___x_4451_; 
lean_dec_ref_known(v___x_4450_, 1);
v___x_4451_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v___y_4436_, v___y_4434_, v___y_4435_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_);
return v___x_4451_;
}
else
{
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec(v___y_4434_);
return v___x_4450_;
}
}
v___jp_4452_:
{
lean_object* v___x_4469_; 
v___x_4469_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
if (lean_obj_tag(v___x_4469_) == 0)
{
lean_object* v_a_4470_; uint8_t v_caseSplits_4471_; 
v_a_4470_ = lean_ctor_get(v___x_4469_, 0);
lean_inc(v_a_4470_);
lean_dec_ref_known(v___x_4469_, 1);
v_caseSplits_4471_ = lean_ctor_get_uint8(v_a_4470_, sizeof(void*)*42);
lean_dec(v_a_4470_);
if (v_caseSplits_4471_ == 0)
{
lean_object* v___x_4472_; 
v___x_4472_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v___y_4456_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
if (lean_obj_tag(v___x_4472_) == 0)
{
lean_object* v_a_4473_; uint8_t v___x_4474_; 
v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
lean_inc(v_a_4473_);
lean_dec_ref_known(v___x_4472_, 1);
v___x_4474_ = lean_unbox(v_a_4473_);
lean_dec(v_a_4473_);
if (v___x_4474_ == 0)
{
v___y_4432_ = v___y_4453_;
v___y_4433_ = v___y_4454_;
v___y_4434_ = v___y_4455_;
v___y_4435_ = v___y_4456_;
v___y_4436_ = v___y_4457_;
v___y_4437_ = v___y_4458_;
v___y_4438_ = v___y_4459_;
v___y_4439_ = v___y_4460_;
v___y_4440_ = v___y_4461_;
v___y_4441_ = v___y_4462_;
v___y_4442_ = v___y_4463_;
v___y_4443_ = v___y_4464_;
v___y_4444_ = v___y_4465_;
v___y_4445_ = v___y_4466_;
v___y_4446_ = v___y_4467_;
v___y_4447_ = v___y_4468_;
goto v___jp_4431_;
}
else
{
lean_object* v___x_4475_; lean_object* v_a_4476_; lean_object* v___x_4477_; 
lean_inc_ref(v___y_4456_);
v___x_4475_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v___y_4456_);
v_a_4476_ = lean_ctor_get(v___x_4475_, 0);
lean_inc(v_a_4476_);
lean_dec_ref(v___x_4475_);
v___x_4477_ = l_Lean_Meta_Grind_Arith_Linear_propagateImpEq(v_a_4476_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_dec_ref_known(v___x_4477_, 1);
v___y_4432_ = v___y_4453_;
v___y_4433_ = v___y_4454_;
v___y_4434_ = v___y_4455_;
v___y_4435_ = v___y_4456_;
v___y_4436_ = v___y_4457_;
v___y_4437_ = v___y_4458_;
v___y_4438_ = v___y_4459_;
v___y_4439_ = v___y_4460_;
v___y_4440_ = v___y_4461_;
v___y_4441_ = v___y_4462_;
v___y_4442_ = v___y_4463_;
v___y_4443_ = v___y_4464_;
v___y_4444_ = v___y_4465_;
v___y_4445_ = v___y_4466_;
v___y_4446_ = v___y_4467_;
v___y_4447_ = v___y_4468_;
goto v___jp_4431_;
}
else
{
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
lean_dec(v___y_4453_);
return v___x_4477_;
}
}
}
else
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4485_; 
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
lean_dec(v___y_4453_);
v_a_4478_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4480_ = v___x_4472_;
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4472_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4483_; 
if (v_isShared_4481_ == 0)
{
v___x_4483_ = v___x_4480_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_a_4478_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
return v___x_4483_;
}
}
}
}
else
{
v___y_4432_ = v___y_4453_;
v___y_4433_ = v___y_4454_;
v___y_4434_ = v___y_4455_;
v___y_4435_ = v___y_4456_;
v___y_4436_ = v___y_4457_;
v___y_4437_ = v___y_4458_;
v___y_4438_ = v___y_4459_;
v___y_4439_ = v___y_4460_;
v___y_4440_ = v___y_4461_;
v___y_4441_ = v___y_4462_;
v___y_4442_ = v___y_4463_;
v___y_4443_ = v___y_4464_;
v___y_4444_ = v___y_4465_;
v___y_4445_ = v___y_4466_;
v___y_4446_ = v___y_4467_;
v___y_4447_ = v___y_4468_;
goto v___jp_4431_;
}
}
else
{
lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4493_; 
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
lean_dec(v___y_4453_);
v_a_4486_ = lean_ctor_get(v___x_4469_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4469_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4488_ = v___x_4469_;
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_dec(v___x_4469_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4491_; 
if (v_isShared_4489_ == 0)
{
v___x_4491_ = v___x_4488_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4486_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
}
v___jp_4498_:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; uint8_t v___x_4519_; 
v___x_4517_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_4518_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_4519_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4515_, v_options_4514_, v___x_4518_);
if (v___x_4519_ == 0)
{
v___y_4453_ = v___y_4499_;
v___y_4454_ = v___y_4500_;
v___y_4455_ = v___y_4501_;
v___y_4456_ = v___y_4502_;
v___y_4457_ = v___y_4503_;
v___y_4458_ = v___y_4504_;
v___y_4459_ = v___y_4505_;
v___y_4460_ = v___y_4506_;
v___y_4461_ = v___y_4507_;
v___y_4462_ = v___y_4508_;
v___y_4463_ = v___y_4509_;
v___y_4464_ = v___y_4510_;
v___y_4465_ = v___y_4511_;
v___y_4466_ = v___y_4512_;
v___y_4467_ = v___y_4513_;
v___y_4468_ = v___y_4516_;
goto v___jp_4452_;
}
else
{
lean_object* v___x_4520_; 
v___x_4520_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v___y_4502_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4516_);
if (lean_obj_tag(v___x_4520_) == 0)
{
lean_object* v_a_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; 
v_a_4521_ = lean_ctor_get(v___x_4520_, 0);
lean_inc(v_a_4521_);
lean_dec_ref_known(v___x_4520_, 1);
v___x_4522_ = l_Lean_MessageData_ofExpr(v_a_4521_);
v___x_4523_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4517_, v___x_4522_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4516_);
if (lean_obj_tag(v___x_4523_) == 0)
{
lean_dec_ref_known(v___x_4523_, 1);
v___y_4453_ = v___y_4499_;
v___y_4454_ = v___y_4500_;
v___y_4455_ = v___y_4501_;
v___y_4456_ = v___y_4502_;
v___y_4457_ = v___y_4503_;
v___y_4458_ = v___y_4504_;
v___y_4459_ = v___y_4505_;
v___y_4460_ = v___y_4506_;
v___y_4461_ = v___y_4507_;
v___y_4462_ = v___y_4508_;
v___y_4463_ = v___y_4509_;
v___y_4464_ = v___y_4510_;
v___y_4465_ = v___y_4511_;
v___y_4466_ = v___y_4512_;
v___y_4467_ = v___y_4513_;
v___y_4468_ = v___y_4516_;
goto v___jp_4452_;
}
else
{
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
return v___x_4523_;
}
}
else
{
lean_object* v_a_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4531_; 
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
v_a_4524_ = lean_ctor_get(v___x_4520_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4526_ = v___x_4520_;
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_a_4524_);
lean_dec(v___x_4520_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4529_; 
if (v_isShared_4527_ == 0)
{
v___x_4529_ = v___x_4526_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_a_4524_);
v___x_4529_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
return v___x_4529_;
}
}
}
}
}
v___jp_4532_:
{
lean_object* v___x_4544_; 
lean_inc_ref(v___y_4542_);
v___x_4544_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_4415_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_);
if (lean_obj_tag(v___x_4544_) == 0)
{
lean_object* v_a_4545_; lean_object* v_p_4546_; lean_object* v___x_4547_; uint8_t v___x_4548_; 
v_a_4545_ = lean_ctor_get(v___x_4544_, 0);
lean_inc(v_a_4545_);
lean_dec_ref_known(v___x_4544_, 1);
v_p_4546_ = lean_ctor_get(v_a_4545_, 0);
v___x_4547_ = lean_box(0);
v___x_4548_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_4546_, v___x_4547_);
if (v___x_4548_ == 0)
{
lean_object* v___x_4549_; 
v___x_4549_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_a_4545_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v_a_4550_; lean_object* v_snd_4551_; lean_object* v_toCold_4552_; lean_object* v_options_4553_; uint8_t v_hasTrace_4554_; 
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
lean_inc(v_a_4550_);
lean_dec_ref_known(v___x_4549_, 1);
v_snd_4551_ = lean_ctor_get(v_a_4550_, 1);
lean_inc(v_snd_4551_);
v_toCold_4552_ = lean_ctor_get(v___y_4542_, 0);
v_options_4553_ = lean_ctor_get(v_toCold_4552_, 2);
v_hasTrace_4554_ = lean_ctor_get_uint8(v_options_4553_, sizeof(void*)*1);
if (v_hasTrace_4554_ == 0)
{
lean_object* v_fst_4555_; lean_object* v_fst_4556_; lean_object* v_snd_4557_; 
v_fst_4555_ = lean_ctor_get(v_a_4550_, 0);
lean_inc(v_fst_4555_);
lean_dec(v_a_4550_);
v_fst_4556_ = lean_ctor_get(v_snd_4551_, 0);
lean_inc_n(v_fst_4556_, 2);
v_snd_4557_ = lean_ctor_get(v_snd_4551_, 1);
lean_inc_n(v_snd_4557_, 2);
lean_dec(v_snd_4551_);
v___y_4453_ = v_fst_4556_;
v___y_4454_ = v_snd_4557_;
v___y_4455_ = v_fst_4556_;
v___y_4456_ = v_snd_4557_;
v___y_4457_ = v_fst_4555_;
v___y_4458_ = v___y_4533_;
v___y_4459_ = v___y_4534_;
v___y_4460_ = v___y_4535_;
v___y_4461_ = v___y_4536_;
v___y_4462_ = v___y_4537_;
v___y_4463_ = v___y_4538_;
v___y_4464_ = v___y_4539_;
v___y_4465_ = v___y_4540_;
v___y_4466_ = v___y_4541_;
v___y_4467_ = v___y_4542_;
v___y_4468_ = v___y_4543_;
goto v___jp_4452_;
}
else
{
lean_object* v_fst_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4604_; 
v_fst_4558_ = lean_ctor_get(v_a_4550_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v_a_4550_);
if (v_isSharedCheck_4604_ == 0)
{
lean_object* v_unused_4605_; 
v_unused_4605_ = lean_ctor_get(v_a_4550_, 1);
lean_dec(v_unused_4605_);
v___x_4560_ = v_a_4550_;
v_isShared_4561_ = v_isSharedCheck_4604_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_fst_4558_);
lean_dec(v_a_4550_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4604_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v_fst_4562_; lean_object* v_snd_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4603_; 
v_fst_4562_ = lean_ctor_get(v_snd_4551_, 0);
v_snd_4563_ = lean_ctor_get(v_snd_4551_, 1);
v_isSharedCheck_4603_ = !lean_is_exclusive(v_snd_4551_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4565_ = v_snd_4551_;
v_isShared_4566_ = v_isSharedCheck_4603_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_snd_4563_);
lean_inc(v_fst_4562_);
lean_dec(v_snd_4551_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4603_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v_inheritedTraceOptions_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; uint8_t v___x_4570_; 
v_inheritedTraceOptions_4567_ = lean_ctor_get(v_toCold_4552_, 11);
v___x_4568_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_4569_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_4570_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4567_, v_options_4553_, v___x_4569_);
if (v___x_4570_ == 0)
{
lean_del_object(v___x_4565_);
lean_del_object(v___x_4560_);
lean_inc(v_snd_4563_);
lean_inc(v_fst_4562_);
v___y_4499_ = v_fst_4562_;
v___y_4500_ = v_snd_4563_;
v___y_4501_ = v_fst_4562_;
v___y_4502_ = v_snd_4563_;
v___y_4503_ = v_fst_4558_;
v___y_4504_ = v___y_4533_;
v___y_4505_ = v___y_4534_;
v___y_4506_ = v___y_4535_;
v___y_4507_ = v___y_4536_;
v___y_4508_ = v___y_4537_;
v___y_4509_ = v___y_4538_;
v___y_4510_ = v___y_4539_;
v___y_4511_ = v___y_4540_;
v___y_4512_ = v___y_4541_;
v___y_4513_ = v___y_4542_;
v_options_4514_ = v_options_4553_;
v_inheritedTraceOptions_4515_ = v_inheritedTraceOptions_4567_;
v___y_4516_ = v___y_4543_;
goto v___jp_4498_;
}
else
{
lean_object* v___x_4571_; 
v___x_4571_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_4562_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_);
if (lean_obj_tag(v___x_4571_) == 0)
{
lean_object* v_a_4572_; lean_object* v___x_4573_; 
v_a_4572_ = lean_ctor_get(v___x_4571_, 0);
lean_inc(v_a_4572_);
lean_dec_ref_known(v___x_4571_, 1);
v___x_4573_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_4563_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_);
if (lean_obj_tag(v___x_4573_) == 0)
{
lean_object* v_a_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4578_; 
v_a_4574_ = lean_ctor_get(v___x_4573_, 0);
lean_inc(v_a_4574_);
lean_dec_ref_known(v___x_4573_, 1);
v___x_4575_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1);
v___x_4576_ = l_Lean_MessageData_ofExpr(v_a_4572_);
if (v_isShared_4566_ == 0)
{
lean_ctor_set_tag(v___x_4565_, 7);
lean_ctor_set(v___x_4565_, 1, v___x_4576_);
lean_ctor_set(v___x_4565_, 0, v___x_4575_);
v___x_4578_ = v___x_4565_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4575_);
lean_ctor_set(v_reuseFailAlloc_4586_, 1, v___x_4576_);
v___x_4578_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
lean_object* v___x_4579_; lean_object* v___x_4581_; 
v___x_4579_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_4561_ == 0)
{
lean_ctor_set_tag(v___x_4560_, 7);
lean_ctor_set(v___x_4560_, 1, v___x_4579_);
lean_ctor_set(v___x_4560_, 0, v___x_4578_);
v___x_4581_ = v___x_4560_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v___x_4578_);
lean_ctor_set(v_reuseFailAlloc_4585_, 1, v___x_4579_);
v___x_4581_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
v___x_4582_ = l_Lean_MessageData_ofExpr(v_a_4574_);
v___x_4583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4581_);
lean_ctor_set(v___x_4583_, 1, v___x_4582_);
v___x_4584_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4568_, v___x_4583_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_);
if (lean_obj_tag(v___x_4584_) == 0)
{
lean_dec_ref_known(v___x_4584_, 1);
lean_inc(v_snd_4563_);
lean_inc(v_fst_4562_);
v___y_4499_ = v_fst_4562_;
v___y_4500_ = v_snd_4563_;
v___y_4501_ = v_fst_4562_;
v___y_4502_ = v_snd_4563_;
v___y_4503_ = v_fst_4558_;
v___y_4504_ = v___y_4533_;
v___y_4505_ = v___y_4534_;
v___y_4506_ = v___y_4535_;
v___y_4507_ = v___y_4536_;
v___y_4508_ = v___y_4537_;
v___y_4509_ = v___y_4538_;
v___y_4510_ = v___y_4539_;
v___y_4511_ = v___y_4540_;
v___y_4512_ = v___y_4541_;
v___y_4513_ = v___y_4542_;
v_options_4514_ = v_options_4553_;
v_inheritedTraceOptions_4515_ = v_inheritedTraceOptions_4567_;
v___y_4516_ = v___y_4543_;
goto v___jp_4498_;
}
else
{
lean_dec(v_snd_4563_);
lean_dec(v_fst_4562_);
lean_dec(v_fst_4558_);
return v___x_4584_;
}
}
}
}
else
{
lean_object* v_a_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4594_; 
lean_dec(v_a_4572_);
lean_del_object(v___x_4565_);
lean_dec(v_snd_4563_);
lean_dec(v_fst_4562_);
lean_del_object(v___x_4560_);
lean_dec(v_fst_4558_);
v_a_4587_ = lean_ctor_get(v___x_4573_, 0);
v_isSharedCheck_4594_ = !lean_is_exclusive(v___x_4573_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4589_ = v___x_4573_;
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_a_4587_);
lean_dec(v___x_4573_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v___x_4592_; 
if (v_isShared_4590_ == 0)
{
v___x_4592_ = v___x_4589_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_a_4587_);
v___x_4592_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
return v___x_4592_;
}
}
}
}
else
{
lean_object* v_a_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4602_; 
lean_del_object(v___x_4565_);
lean_dec(v_snd_4563_);
lean_dec(v_fst_4562_);
lean_del_object(v___x_4560_);
lean_dec(v_fst_4558_);
v_a_4595_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4602_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4597_ = v___x_4571_;
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_a_4595_);
lean_dec(v___x_4571_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
lean_object* v___x_4600_; 
if (v_isShared_4598_ == 0)
{
v___x_4600_ = v___x_4597_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_a_4595_);
v___x_4600_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
return v___x_4600_;
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
lean_object* v_a_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4613_; 
v_a_4606_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4608_ = v___x_4549_;
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_a_4606_);
lean_dec(v___x_4549_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v___x_4611_; 
if (v_isShared_4609_ == 0)
{
v___x_4611_ = v___x_4608_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_a_4606_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
}
}
else
{
lean_object* v_toCold_4614_; lean_object* v_options_4615_; uint8_t v_hasTrace_4616_; 
v_toCold_4614_ = lean_ctor_get(v___y_4542_, 0);
v_options_4615_ = lean_ctor_get(v_toCold_4614_, 2);
v_hasTrace_4616_ = lean_ctor_get_uint8(v_options_4615_, sizeof(void*)*1);
if (v_hasTrace_4616_ == 0)
{
lean_dec(v_a_4545_);
goto v___jp_4428_;
}
else
{
lean_object* v_inheritedTraceOptions_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; uint8_t v___x_4620_; 
v_inheritedTraceOptions_4617_ = lean_ctor_get(v_toCold_4614_, 11);
v___x_4618_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4619_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4);
v___x_4620_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4617_, v_options_4615_, v___x_4619_);
if (v___x_4620_ == 0)
{
lean_dec(v_a_4545_);
goto v___jp_4428_;
}
else
{
lean_object* v___x_4621_; 
v___x_4621_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_a_4545_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_);
lean_dec(v_a_4545_);
if (lean_obj_tag(v___x_4621_) == 0)
{
lean_object* v_a_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v_a_4622_ = lean_ctor_get(v___x_4621_, 0);
lean_inc(v_a_4622_);
lean_dec_ref_known(v___x_4621_, 1);
v___x_4623_ = l_Lean_MessageData_ofExpr(v_a_4622_);
v___x_4624_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4618_, v___x_4623_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_dec_ref_known(v___x_4624_, 1);
goto v___jp_4428_;
}
else
{
return v___x_4624_;
}
}
else
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4632_; 
v_a_4625_ = lean_ctor_get(v___x_4621_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4621_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4627_ = v___x_4621_;
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4621_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4630_; 
if (v_isShared_4628_ == 0)
{
v___x_4630_ = v___x_4627_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_a_4625_);
v___x_4630_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
return v___x_4630_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4633_; lean_object* v___x_4635_; uint8_t v_isShared_4636_; uint8_t v_isSharedCheck_4640_; 
v_a_4633_ = lean_ctor_get(v___x_4544_, 0);
v_isSharedCheck_4640_ = !lean_is_exclusive(v___x_4544_);
if (v_isSharedCheck_4640_ == 0)
{
v___x_4635_ = v___x_4544_;
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
else
{
lean_inc(v_a_4633_);
lean_dec(v___x_4544_);
v___x_4635_ = lean_box(0);
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
v_resetjp_4634_:
{
lean_object* v___x_4638_; 
if (v_isShared_4636_ == 0)
{
v___x_4638_ = v___x_4635_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_a_4633_);
v___x_4638_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
return v___x_4638_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object* v_c_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_){
_start:
{
lean_object* v_res_4669_; 
v_res_4669_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v_c_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
lean_dec(v_a_4667_);
lean_dec_ref(v_a_4666_);
lean_dec(v_a_4665_);
lean_dec_ref(v_a_4664_);
lean_dec(v_a_4663_);
lean_dec_ref(v_a_4662_);
lean_dec(v_a_4661_);
lean_dec_ref(v_a_4660_);
lean_dec(v_a_4659_);
lean_dec(v_a_4658_);
lean_dec(v_a_4657_);
return v_res_4669_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2(void){
_start:
{
lean_object* v_cls_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
v_cls_4674_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4675_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4676_ = l_Lean_Name_append(v___x_4675_, v_cls_4674_);
return v___x_4676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object* v_a_4677_, lean_object* v_b_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_){
_start:
{
lean_object* v_toCold_4687_; lean_object* v_options_4688_; uint8_t v_hasTrace_4689_; 
v_toCold_4687_ = lean_ctor_get(v_a_4681_, 0);
v_options_4688_ = lean_ctor_get(v_toCold_4687_, 2);
v_hasTrace_4689_ = lean_ctor_get_uint8(v_options_4688_, sizeof(void*)*1);
if (v_hasTrace_4689_ == 0)
{
lean_dec_ref(v_b_4678_);
lean_dec_ref(v_a_4677_);
goto v___jp_4684_;
}
else
{
lean_object* v_inheritedTraceOptions_4690_; lean_object* v_cls_4691_; lean_object* v___x_4692_; uint8_t v___x_4693_; 
v_inheritedTraceOptions_4690_ = lean_ctor_get(v_toCold_4687_, 11);
v_cls_4691_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4692_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2);
v___x_4693_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4690_, v_options_4688_, v___x_4692_);
if (v___x_4693_ == 0)
{
lean_dec_ref(v_b_4678_);
lean_dec_ref(v_a_4677_);
goto v___jp_4684_;
}
else
{
lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
v___x_4694_ = l_Lean_MessageData_ofExpr(v_a_4677_);
v___x_4695_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_4696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4696_, 0, v___x_4694_);
lean_ctor_set(v___x_4696_, 1, v___x_4695_);
v___x_4697_ = l_Lean_MessageData_ofExpr(v_b_4678_);
v___x_4698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4698_, 0, v___x_4696_);
lean_ctor_set(v___x_4698_, 1, v___x_4697_);
v___x_4699_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4691_, v___x_4698_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_);
return v___x_4699_;
}
}
v___jp_4684_:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; 
v___x_4685_ = lean_box(0);
v___x_4686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4686_, 0, v___x_4685_);
return v___x_4686_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object* v_a_4700_, lean_object* v_b_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_){
_start:
{
lean_object* v_res_4707_; 
v_res_4707_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4700_, v_b_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_);
lean_dec(v_a_4705_);
lean_dec_ref(v_a_4704_);
lean_dec(v_a_4703_);
lean_dec_ref(v_a_4702_);
return v_res_4707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object* v_a_4708_, lean_object* v_b_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_){
_start:
{
lean_object* v___x_4722_; 
v___x_4722_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4708_, v_b_4709_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_);
return v___x_4722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object* v_a_4723_, lean_object* v_b_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(v_a_4723_, v_b_4724_, v_a_4725_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_);
lean_dec(v_a_4735_);
lean_dec_ref(v_a_4734_);
lean_dec(v_a_4733_);
lean_dec_ref(v_a_4732_);
lean_dec(v_a_4731_);
lean_dec_ref(v_a_4730_);
lean_dec(v_a_4729_);
lean_dec_ref(v_a_4728_);
lean_dec(v_a_4727_);
lean_dec(v_a_4726_);
lean_dec(v_a_4725_);
return v_res_4737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object* v_a_4738_, lean_object* v_b_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_){
_start:
{
uint8_t v___x_4752_; lean_object* v___x_4753_; 
v___x_4752_ = 0;
lean_inc_ref(v_a_4738_);
v___x_4753_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_4738_, v___x_4752_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_);
if (lean_obj_tag(v___x_4753_) == 0)
{
lean_object* v_a_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4793_; 
v_a_4754_ = lean_ctor_get(v___x_4753_, 0);
v_isSharedCheck_4793_ = !lean_is_exclusive(v___x_4753_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4756_ = v___x_4753_;
v_isShared_4757_ = v_isSharedCheck_4793_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_a_4754_);
lean_dec(v___x_4753_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4793_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
if (lean_obj_tag(v_a_4754_) == 1)
{
lean_object* v_val_4758_; lean_object* v___x_4759_; 
lean_del_object(v___x_4756_);
v_val_4758_ = lean_ctor_get(v_a_4754_, 0);
lean_inc(v_val_4758_);
lean_dec_ref_known(v_a_4754_, 1);
lean_inc_ref(v_b_4739_);
v___x_4759_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_4739_, v___x_4752_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_);
if (lean_obj_tag(v___x_4759_) == 0)
{
lean_object* v_a_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4780_; 
v_a_4760_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4780_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4780_ == 0)
{
v___x_4762_ = v___x_4759_;
v_isShared_4763_ = v_isSharedCheck_4780_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_a_4760_);
lean_dec(v___x_4759_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4780_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
if (lean_obj_tag(v_a_4760_) == 1)
{
lean_object* v_val_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; uint8_t v___x_4768_; 
v_val_4764_ = lean_ctor_get(v_a_4760_, 0);
lean_inc_n(v_val_4764_, 2);
lean_dec_ref_known(v_a_4760_, 1);
lean_inc(v_val_4758_);
v___x_4765_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4765_, 0, v_val_4758_);
lean_ctor_set(v___x_4765_, 1, v_val_4764_);
v___x_4766_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4765_);
v___x_4767_ = lean_box(0);
v___x_4768_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4766_, v___x_4767_);
if (v___x_4768_ == 0)
{
lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; 
lean_del_object(v___x_4762_);
v___x_4769_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4769_, 0, v_a_4738_);
lean_ctor_set(v___x_4769_, 1, v_b_4739_);
lean_ctor_set(v___x_4769_, 2, v_val_4758_);
lean_ctor_set(v___x_4769_, 3, v_val_4764_);
v___x_4770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4770_, 0, v___x_4766_);
lean_ctor_set(v___x_4770_, 1, v___x_4769_);
v___x_4771_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_4770_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_);
return v___x_4771_;
}
else
{
lean_object* v___x_4772_; lean_object* v___x_4774_; 
lean_dec(v___x_4766_);
lean_dec(v_val_4764_);
lean_dec(v_val_4758_);
lean_dec_ref(v_b_4739_);
lean_dec_ref(v_a_4738_);
v___x_4772_ = lean_box(0);
if (v_isShared_4763_ == 0)
{
lean_ctor_set(v___x_4762_, 0, v___x_4772_);
v___x_4774_ = v___x_4762_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v___x_4772_);
v___x_4774_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
return v___x_4774_;
}
}
}
else
{
lean_object* v___x_4776_; lean_object* v___x_4778_; 
lean_dec(v_a_4760_);
lean_dec(v_val_4758_);
lean_dec_ref(v_b_4739_);
lean_dec_ref(v_a_4738_);
v___x_4776_ = lean_box(0);
if (v_isShared_4763_ == 0)
{
lean_ctor_set(v___x_4762_, 0, v___x_4776_);
v___x_4778_ = v___x_4762_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v___x_4776_);
v___x_4778_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
return v___x_4778_;
}
}
}
}
else
{
lean_object* v_a_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4788_; 
lean_dec(v_val_4758_);
lean_dec_ref(v_b_4739_);
lean_dec_ref(v_a_4738_);
v_a_4781_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4788_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4783_ = v___x_4759_;
v_isShared_4784_ = v_isSharedCheck_4788_;
goto v_resetjp_4782_;
}
else
{
lean_inc(v_a_4781_);
lean_dec(v___x_4759_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4788_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
lean_object* v___x_4786_; 
if (v_isShared_4784_ == 0)
{
v___x_4786_ = v___x_4783_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v_a_4781_);
v___x_4786_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
return v___x_4786_;
}
}
}
}
else
{
lean_object* v___x_4789_; lean_object* v___x_4791_; 
lean_dec(v_a_4754_);
lean_dec_ref(v_b_4739_);
lean_dec_ref(v_a_4738_);
v___x_4789_ = lean_box(0);
if (v_isShared_4757_ == 0)
{
lean_ctor_set(v___x_4756_, 0, v___x_4789_);
v___x_4791_ = v___x_4756_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___x_4789_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
}
}
else
{
lean_object* v_a_4794_; lean_object* v___x_4796_; uint8_t v_isShared_4797_; uint8_t v_isSharedCheck_4801_; 
lean_dec_ref(v_b_4739_);
lean_dec_ref(v_a_4738_);
v_a_4794_ = lean_ctor_get(v___x_4753_, 0);
v_isSharedCheck_4801_ = !lean_is_exclusive(v___x_4753_);
if (v_isSharedCheck_4801_ == 0)
{
v___x_4796_ = v___x_4753_;
v_isShared_4797_ = v_isSharedCheck_4801_;
goto v_resetjp_4795_;
}
else
{
lean_inc(v_a_4794_);
lean_dec(v___x_4753_);
v___x_4796_ = lean_box(0);
v_isShared_4797_ = v_isSharedCheck_4801_;
goto v_resetjp_4795_;
}
v_resetjp_4795_:
{
lean_object* v___x_4799_; 
if (v_isShared_4797_ == 0)
{
v___x_4799_ = v___x_4796_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v_a_4794_);
v___x_4799_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
return v___x_4799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___boxed(lean_object* v_a_4802_, lean_object* v_b_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_){
_start:
{
lean_object* v_res_4816_; 
v_res_4816_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_4802_, v_b_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_);
lean_dec(v_a_4814_);
lean_dec_ref(v_a_4813_);
lean_dec(v_a_4812_);
lean_dec_ref(v_a_4811_);
lean_dec(v_a_4810_);
lean_dec_ref(v_a_4809_);
lean_dec(v_a_4808_);
lean_dec_ref(v_a_4807_);
lean_dec(v_a_4806_);
lean_dec(v_a_4805_);
lean_dec(v_a_4804_);
return v_res_4816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(lean_object* v_a_4817_, lean_object* v_b_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_){
_start:
{
lean_object* v___x_4831_; 
v___x_4831_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_);
if (lean_obj_tag(v___x_4831_) == 0)
{
lean_object* v_a_4832_; lean_object* v___x_4833_; 
v_a_4832_ = lean_ctor_get(v___x_4831_, 0);
lean_inc(v_a_4832_);
lean_dec_ref_known(v___x_4831_, 1);
lean_inc_ref(v_a_4817_);
v___x_4833_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_4817_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_);
if (lean_obj_tag(v___x_4833_) == 0)
{
lean_object* v_a_4834_; lean_object* v_fst_4835_; lean_object* v___x_4836_; 
v_a_4834_ = lean_ctor_get(v___x_4833_, 0);
lean_inc(v_a_4834_);
lean_dec_ref_known(v___x_4833_, 1);
v_fst_4835_ = lean_ctor_get(v_a_4834_, 0);
lean_inc(v_fst_4835_);
lean_dec(v_a_4834_);
lean_inc_ref(v_b_4818_);
v___x_4836_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_);
if (lean_obj_tag(v___x_4836_) == 0)
{
lean_object* v_a_4837_; lean_object* v_fst_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4901_; 
v_a_4837_ = lean_ctor_get(v___x_4836_, 0);
lean_inc(v_a_4837_);
lean_dec_ref_known(v___x_4836_, 1);
v_fst_4838_ = lean_ctor_get(v_a_4837_, 0);
v_isSharedCheck_4901_ = !lean_is_exclusive(v_a_4837_);
if (v_isSharedCheck_4901_ == 0)
{
lean_object* v_unused_4902_; 
v_unused_4902_ = lean_ctor_get(v_a_4837_, 1);
lean_dec(v_unused_4902_);
v___x_4840_ = v_a_4837_;
v_isShared_4841_ = v_isSharedCheck_4901_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_fst_4838_);
lean_dec(v_a_4837_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4901_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v_id_4842_; lean_object* v_structId_4843_; uint8_t v___x_4844_; lean_object* v___x_4845_; 
v_id_4842_ = lean_ctor_get(v_a_4832_, 0);
lean_inc(v_id_4842_);
v_structId_4843_ = lean_ctor_get(v_a_4832_, 1);
lean_inc(v_structId_4843_);
lean_dec(v_a_4832_);
v___x_4844_ = 0;
v___x_4845_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4835_, v___x_4844_, v_structId_4843_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_);
if (lean_obj_tag(v___x_4845_) == 0)
{
lean_object* v_a_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4892_; 
v_a_4846_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4848_ = v___x_4845_;
v_isShared_4849_ = v_isSharedCheck_4892_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_a_4846_);
lean_dec(v___x_4845_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4892_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
if (lean_obj_tag(v_a_4846_) == 1)
{
lean_object* v_val_4850_; lean_object* v___x_4851_; 
lean_del_object(v___x_4848_);
v_val_4850_ = lean_ctor_get(v_a_4846_, 0);
lean_inc(v_val_4850_);
lean_dec_ref_known(v_a_4846_, 1);
v___x_4851_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4838_, v___x_4844_, v_structId_4843_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_a_4852_; lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_4879_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4879_ == 0)
{
v___x_4854_ = v___x_4851_;
v_isShared_4855_ = v_isSharedCheck_4879_;
goto v_resetjp_4853_;
}
else
{
lean_inc(v_a_4852_);
lean_dec(v___x_4851_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_4879_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
if (lean_obj_tag(v_a_4852_) == 1)
{
lean_object* v_val_4856_; lean_object* v___x_4858_; 
v_val_4856_ = lean_ctor_get(v_a_4852_, 0);
lean_inc_n(v_val_4856_, 2);
lean_dec_ref_known(v_a_4852_, 1);
lean_inc(v_val_4850_);
if (v_isShared_4841_ == 0)
{
lean_ctor_set_tag(v___x_4840_, 3);
lean_ctor_set(v___x_4840_, 1, v_val_4856_);
lean_ctor_set(v___x_4840_, 0, v_val_4850_);
v___x_4858_ = v___x_4840_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_val_4850_);
lean_ctor_set(v_reuseFailAlloc_4874_, 1, v_val_4856_);
v___x_4858_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
lean_object* v___x_4859_; lean_object* v___x_4860_; uint8_t v___x_4861_; 
v___x_4859_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4858_);
v___x_4860_ = lean_box(0);
v___x_4861_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4859_, v___x_4860_);
if (v___x_4861_ == 0)
{
lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; 
lean_del_object(v___x_4854_);
lean_inc(v_val_4856_);
lean_inc(v_val_4850_);
lean_inc(v_id_4842_);
lean_inc_ref(v_b_4818_);
lean_inc_ref(v_a_4817_);
v___x_4862_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4862_, 0, v_a_4817_);
lean_ctor_set(v___x_4862_, 1, v_b_4818_);
lean_ctor_set(v___x_4862_, 2, v_id_4842_);
lean_ctor_set(v___x_4862_, 3, v_val_4850_);
lean_ctor_set(v___x_4862_, 4, v_val_4856_);
lean_inc(v___x_4859_);
v___x_4863_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4863_, 0, v___x_4859_);
lean_ctor_set(v___x_4863_, 1, v___x_4862_);
lean_ctor_set_uint8(v___x_4863_, sizeof(void*)*2, v___x_4844_);
v___x_4864_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4863_, v_structId_4843_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_);
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; 
lean_dec_ref_known(v___x_4864_, 1);
v___x_4865_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4866_ = l_Lean_Grind_Linarith_Poly_mul(v___x_4859_, v___x_4865_);
v___x_4867_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4867_, 0, v_b_4818_);
lean_ctor_set(v___x_4867_, 1, v_a_4817_);
lean_ctor_set(v___x_4867_, 2, v_id_4842_);
lean_ctor_set(v___x_4867_, 3, v_val_4856_);
lean_ctor_set(v___x_4867_, 4, v_val_4850_);
v___x_4868_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4868_, 0, v___x_4866_);
lean_ctor_set(v___x_4868_, 1, v___x_4867_);
lean_ctor_set_uint8(v___x_4868_, sizeof(void*)*2, v___x_4844_);
v___x_4869_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4868_, v_structId_4843_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_);
lean_dec(v_structId_4843_);
return v___x_4869_;
}
else
{
lean_dec(v___x_4859_);
lean_dec(v_val_4856_);
lean_dec(v_val_4850_);
lean_dec(v_structId_4843_);
lean_dec(v_id_4842_);
lean_dec_ref(v_b_4818_);
lean_dec_ref(v_a_4817_);
return v___x_4864_;
}
}
else
{
lean_object* v___x_4870_; lean_object* v___x_4872_; 
lean_dec(v___x_4859_);
lean_dec(v_val_4856_);
lean_dec(v_val_4850_);
lean_dec(v_structId_4843_);
lean_dec(v_id_4842_);
lean_dec_ref(v_b_4818_);
lean_dec_ref(v_a_4817_);
v___x_4870_ = lean_box(0);
if (v_isShared_4855_ == 0)
{
lean_ctor_set(v___x_4854_, 0, v___x_4870_);
v___x_4872_ = v___x_4854_;
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
lean_object* v___x_4875_; lean_object* v___x_4877_; 
lean_dec(v_a_4852_);
lean_dec(v_val_4850_);
lean_dec(v_structId_4843_);
lean_dec(v_id_4842_);
lean_del_object(v___x_4840_);
lean_dec_ref(v_b_4818_);
lean_dec_ref(v_a_4817_);
v___x_4875_ = lean_box(0);
if (v_isShared_4855_ == 0)
{
lean_ctor_set(v___x_4854_, 0, v___x_4875_);
v___x_4877_ = v___x_4854_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4875_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
}
}
else
{
lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4887_; 
lean_dec(v_val_4850_);
lean_dec(v_structId_4843_);
lean_dec(v_id_4842_);
lean_del_object(v___x_4840_);
lean_dec_ref(v_b_4818_);
lean_dec_ref(v_a_4817_);
v_a_4880_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4887_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4882_ = v___x_4851_;
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4851_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v___x_4885_; 
if (v_isShared_4883_ == 0)
{
v___x_4885_ = v___x_4882_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v_a_4880_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
}
else
{
lean_object* v___x_4888_; lean_object* v___x_4890_; 
lean_dec(v_a_4846_);
lean_dec(v_structId_4843_);
lean_dec(v_id_4842_);
lean_del_object(v___x_4840_);
lean_dec(v_fst_4838_);
lean_dec_ref(v_b_4818_);
lean_dec_ref(v_a_4817_);
v___x_4888_ = lean_box(0);
if (v_isShared_4849_ == 0)
{
lean_ctor_set(v___x_4848_, 0, v___x_4888_);
v___x_4890_ = v___x_4848_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v___x_4888_);
v___x_4890_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
return v___x_4890_;
}
}
}
}
else
{
lean_object* v_a_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4900_; 
lean_dec(v_structId_4843_);
lean_dec(v_id_4842_);
lean_del_object(v___x_4840_);
lean_dec(v_fst_4838_);
lean_dec_ref(v_b_4818_);
lean_dec_ref(v_a_4817_);
v_a_4893_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4895_ = v___x_4845_;
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_a_4893_);
lean_dec(v___x_4845_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
lean_object* v___x_4898_; 
if (v_isShared_4896_ == 0)
{
v___x_4898_ = v___x_4895_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v_a_4893_);
v___x_4898_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
return v___x_4898_;
}
}
}
}
}
else
{
lean_object* v_a_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4910_; 
lean_dec(v_fst_4835_);
lean_dec(v_a_4832_);
lean_dec_ref(v_b_4818_);
lean_dec_ref(v_a_4817_);
v_a_4903_ = lean_ctor_get(v___x_4836_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___x_4836_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4905_ = v___x_4836_;
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_a_4903_);
lean_dec(v___x_4836_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
lean_object* v___x_4908_; 
if (v_isShared_4906_ == 0)
{
v___x_4908_ = v___x_4905_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_a_4903_);
v___x_4908_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
return v___x_4908_;
}
}
}
}
else
{
lean_object* v_a_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4918_; 
lean_dec(v_a_4832_);
lean_dec_ref(v_b_4818_);
lean_dec_ref(v_a_4817_);
v_a_4911_ = lean_ctor_get(v___x_4833_, 0);
v_isSharedCheck_4918_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_4918_ == 0)
{
v___x_4913_ = v___x_4833_;
v_isShared_4914_ = v_isSharedCheck_4918_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_a_4911_);
lean_dec(v___x_4833_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4918_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v___x_4916_; 
if (v_isShared_4914_ == 0)
{
v___x_4916_ = v___x_4913_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_a_4911_);
v___x_4916_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
return v___x_4916_;
}
}
}
}
else
{
lean_object* v_a_4919_; lean_object* v___x_4921_; uint8_t v_isShared_4922_; uint8_t v_isSharedCheck_4926_; 
lean_dec_ref(v_b_4818_);
lean_dec_ref(v_a_4817_);
v_a_4919_ = lean_ctor_get(v___x_4831_, 0);
v_isSharedCheck_4926_ = !lean_is_exclusive(v___x_4831_);
if (v_isSharedCheck_4926_ == 0)
{
v___x_4921_ = v___x_4831_;
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
else
{
lean_inc(v_a_4919_);
lean_dec(v___x_4831_);
v___x_4921_ = lean_box(0);
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
v_resetjp_4920_:
{
lean_object* v___x_4924_; 
if (v_isShared_4922_ == 0)
{
v___x_4924_ = v___x_4921_;
goto v_reusejp_4923_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v_a_4919_);
v___x_4924_ = v_reuseFailAlloc_4925_;
goto v_reusejp_4923_;
}
v_reusejp_4923_:
{
return v___x_4924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27___boxed(lean_object* v_a_4927_, lean_object* v_b_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_){
_start:
{
lean_object* v_res_4941_; 
v_res_4941_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_4927_, v_b_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_);
lean_dec(v_a_4939_);
lean_dec_ref(v_a_4938_);
lean_dec(v_a_4937_);
lean_dec_ref(v_a_4936_);
lean_dec(v_a_4935_);
lean_dec_ref(v_a_4934_);
lean_dec(v_a_4933_);
lean_dec_ref(v_a_4932_);
lean_dec(v_a_4931_);
lean_dec(v_a_4930_);
lean_dec(v_a_4929_);
return v_res_4941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(lean_object* v_a_4942_, lean_object* v_b_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_){
_start:
{
lean_object* v___x_4956_; 
v___x_4956_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_);
if (lean_obj_tag(v___x_4956_) == 0)
{
lean_object* v_a_4957_; lean_object* v___x_4958_; 
v_a_4957_ = lean_ctor_get(v___x_4956_, 0);
lean_inc(v_a_4957_);
lean_dec_ref_known(v___x_4956_, 1);
lean_inc_ref(v_a_4942_);
v___x_4958_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_4942_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_);
if (lean_obj_tag(v___x_4958_) == 0)
{
lean_object* v_a_4959_; lean_object* v_fst_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_5036_; 
v_a_4959_ = lean_ctor_get(v___x_4958_, 0);
lean_inc(v_a_4959_);
lean_dec_ref_known(v___x_4958_, 1);
v_fst_4960_ = lean_ctor_get(v_a_4959_, 0);
v_isSharedCheck_5036_ = !lean_is_exclusive(v_a_4959_);
if (v_isSharedCheck_5036_ == 0)
{
lean_object* v_unused_5037_; 
v_unused_5037_ = lean_ctor_get(v_a_4959_, 1);
lean_dec(v_unused_5037_);
v___x_4962_ = v_a_4959_;
v_isShared_4963_ = v_isSharedCheck_5036_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_fst_4960_);
lean_dec(v_a_4959_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_5036_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
lean_object* v___x_4964_; 
lean_inc_ref(v_b_4943_);
v___x_4964_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_);
if (lean_obj_tag(v___x_4964_) == 0)
{
lean_object* v_a_4965_; lean_object* v_fst_4966_; lean_object* v___x_4968_; uint8_t v_isShared_4969_; uint8_t v_isSharedCheck_5026_; 
v_a_4965_ = lean_ctor_get(v___x_4964_, 0);
lean_inc(v_a_4965_);
lean_dec_ref_known(v___x_4964_, 1);
v_fst_4966_ = lean_ctor_get(v_a_4965_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v_a_4965_);
if (v_isSharedCheck_5026_ == 0)
{
lean_object* v_unused_5027_; 
v_unused_5027_ = lean_ctor_get(v_a_4965_, 1);
lean_dec(v_unused_5027_);
v___x_4968_ = v_a_4965_;
v_isShared_4969_ = v_isSharedCheck_5026_;
goto v_resetjp_4967_;
}
else
{
lean_inc(v_fst_4966_);
lean_dec(v_a_4965_);
v___x_4968_ = lean_box(0);
v_isShared_4969_ = v_isSharedCheck_5026_;
goto v_resetjp_4967_;
}
v_resetjp_4967_:
{
lean_object* v_id_4970_; lean_object* v_structId_4971_; uint8_t v___x_4972_; lean_object* v___x_4973_; 
v_id_4970_ = lean_ctor_get(v_a_4957_, 0);
lean_inc(v_id_4970_);
v_structId_4971_ = lean_ctor_get(v_a_4957_, 1);
lean_inc(v_structId_4971_);
lean_dec(v_a_4957_);
v___x_4972_ = 0;
v___x_4973_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4960_, v___x_4972_, v_structId_4971_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_);
if (lean_obj_tag(v___x_4973_) == 0)
{
lean_object* v_a_4974_; lean_object* v___x_4976_; uint8_t v_isShared_4977_; uint8_t v_isSharedCheck_5017_; 
v_a_4974_ = lean_ctor_get(v___x_4973_, 0);
v_isSharedCheck_5017_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_4976_ = v___x_4973_;
v_isShared_4977_ = v_isSharedCheck_5017_;
goto v_resetjp_4975_;
}
else
{
lean_inc(v_a_4974_);
lean_dec(v___x_4973_);
v___x_4976_ = lean_box(0);
v_isShared_4977_ = v_isSharedCheck_5017_;
goto v_resetjp_4975_;
}
v_resetjp_4975_:
{
if (lean_obj_tag(v_a_4974_) == 1)
{
lean_object* v_val_4978_; lean_object* v___x_4979_; 
lean_del_object(v___x_4976_);
v_val_4978_ = lean_ctor_get(v_a_4974_, 0);
lean_inc(v_val_4978_);
lean_dec_ref_known(v_a_4974_, 1);
v___x_4979_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4966_, v___x_4972_, v_structId_4971_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_);
if (lean_obj_tag(v___x_4979_) == 0)
{
lean_object* v_a_4980_; lean_object* v___x_4982_; uint8_t v_isShared_4983_; uint8_t v_isSharedCheck_5004_; 
v_a_4980_ = lean_ctor_get(v___x_4979_, 0);
v_isSharedCheck_5004_ = !lean_is_exclusive(v___x_4979_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4982_ = v___x_4979_;
v_isShared_4983_ = v_isSharedCheck_5004_;
goto v_resetjp_4981_;
}
else
{
lean_inc(v_a_4980_);
lean_dec(v___x_4979_);
v___x_4982_ = lean_box(0);
v_isShared_4983_ = v_isSharedCheck_5004_;
goto v_resetjp_4981_;
}
v_resetjp_4981_:
{
if (lean_obj_tag(v_a_4980_) == 1)
{
lean_object* v_val_4984_; lean_object* v___x_4986_; 
v_val_4984_ = lean_ctor_get(v_a_4980_, 0);
lean_inc_n(v_val_4984_, 2);
lean_dec_ref_known(v_a_4980_, 1);
lean_inc(v_val_4978_);
if (v_isShared_4969_ == 0)
{
lean_ctor_set_tag(v___x_4968_, 3);
lean_ctor_set(v___x_4968_, 1, v_val_4984_);
lean_ctor_set(v___x_4968_, 0, v_val_4978_);
v___x_4986_ = v___x_4968_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_val_4978_);
lean_ctor_set(v_reuseFailAlloc_4999_, 1, v_val_4984_);
v___x_4986_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
lean_object* v___x_4987_; lean_object* v___x_4988_; uint8_t v___x_4989_; 
v___x_4987_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4986_);
v___x_4988_ = lean_box(0);
v___x_4989_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4987_, v___x_4988_);
if (v___x_4989_ == 0)
{
lean_object* v___x_4990_; lean_object* v___x_4992_; 
lean_del_object(v___x_4982_);
v___x_4990_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_4990_, 0, v_a_4942_);
lean_ctor_set(v___x_4990_, 1, v_b_4943_);
lean_ctor_set(v___x_4990_, 2, v_id_4970_);
lean_ctor_set(v___x_4990_, 3, v_val_4978_);
lean_ctor_set(v___x_4990_, 4, v_val_4984_);
if (v_isShared_4963_ == 0)
{
lean_ctor_set(v___x_4962_, 1, v___x_4990_);
lean_ctor_set(v___x_4962_, 0, v___x_4987_);
v___x_4992_ = v___x_4962_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4994_; 
v_reuseFailAlloc_4994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4994_, 0, v___x_4987_);
lean_ctor_set(v_reuseFailAlloc_4994_, 1, v___x_4990_);
v___x_4992_ = v_reuseFailAlloc_4994_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
lean_object* v___x_4993_; 
v___x_4993_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_4992_, v_structId_4971_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_);
lean_dec(v_structId_4971_);
return v___x_4993_;
}
}
else
{
lean_object* v___x_4995_; lean_object* v___x_4997_; 
lean_dec(v___x_4987_);
lean_dec(v_val_4984_);
lean_dec(v_val_4978_);
lean_dec(v_structId_4971_);
lean_dec(v_id_4970_);
lean_del_object(v___x_4962_);
lean_dec_ref(v_b_4943_);
lean_dec_ref(v_a_4942_);
v___x_4995_ = lean_box(0);
if (v_isShared_4983_ == 0)
{
lean_ctor_set(v___x_4982_, 0, v___x_4995_);
v___x_4997_ = v___x_4982_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v___x_4995_);
v___x_4997_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
return v___x_4997_;
}
}
}
}
else
{
lean_object* v___x_5000_; lean_object* v___x_5002_; 
lean_dec(v_a_4980_);
lean_dec(v_val_4978_);
lean_dec(v_structId_4971_);
lean_dec(v_id_4970_);
lean_del_object(v___x_4968_);
lean_del_object(v___x_4962_);
lean_dec_ref(v_b_4943_);
lean_dec_ref(v_a_4942_);
v___x_5000_ = lean_box(0);
if (v_isShared_4983_ == 0)
{
lean_ctor_set(v___x_4982_, 0, v___x_5000_);
v___x_5002_ = v___x_4982_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5003_; 
v_reuseFailAlloc_5003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5003_, 0, v___x_5000_);
v___x_5002_ = v_reuseFailAlloc_5003_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
return v___x_5002_;
}
}
}
}
else
{
lean_object* v_a_5005_; lean_object* v___x_5007_; uint8_t v_isShared_5008_; uint8_t v_isSharedCheck_5012_; 
lean_dec(v_val_4978_);
lean_dec(v_structId_4971_);
lean_dec(v_id_4970_);
lean_del_object(v___x_4968_);
lean_del_object(v___x_4962_);
lean_dec_ref(v_b_4943_);
lean_dec_ref(v_a_4942_);
v_a_5005_ = lean_ctor_get(v___x_4979_, 0);
v_isSharedCheck_5012_ = !lean_is_exclusive(v___x_4979_);
if (v_isSharedCheck_5012_ == 0)
{
v___x_5007_ = v___x_4979_;
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
else
{
lean_inc(v_a_5005_);
lean_dec(v___x_4979_);
v___x_5007_ = lean_box(0);
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
v_resetjp_5006_:
{
lean_object* v___x_5010_; 
if (v_isShared_5008_ == 0)
{
v___x_5010_ = v___x_5007_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v_a_5005_);
v___x_5010_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
return v___x_5010_;
}
}
}
}
else
{
lean_object* v___x_5013_; lean_object* v___x_5015_; 
lean_dec(v_a_4974_);
lean_dec(v_structId_4971_);
lean_dec(v_id_4970_);
lean_del_object(v___x_4968_);
lean_dec(v_fst_4966_);
lean_del_object(v___x_4962_);
lean_dec_ref(v_b_4943_);
lean_dec_ref(v_a_4942_);
v___x_5013_ = lean_box(0);
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 0, v___x_5013_);
v___x_5015_ = v___x_4976_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v___x_5013_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
}
}
else
{
lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5025_; 
lean_dec(v_structId_4971_);
lean_dec(v_id_4970_);
lean_del_object(v___x_4968_);
lean_dec(v_fst_4966_);
lean_del_object(v___x_4962_);
lean_dec_ref(v_b_4943_);
lean_dec_ref(v_a_4942_);
v_a_5018_ = lean_ctor_get(v___x_4973_, 0);
v_isSharedCheck_5025_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_5025_ == 0)
{
v___x_5020_ = v___x_4973_;
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v___x_4973_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5023_; 
if (v_isShared_5021_ == 0)
{
v___x_5023_ = v___x_5020_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_a_5018_);
v___x_5023_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
return v___x_5023_;
}
}
}
}
}
else
{
lean_object* v_a_5028_; lean_object* v___x_5030_; uint8_t v_isShared_5031_; uint8_t v_isSharedCheck_5035_; 
lean_del_object(v___x_4962_);
lean_dec(v_fst_4960_);
lean_dec(v_a_4957_);
lean_dec_ref(v_b_4943_);
lean_dec_ref(v_a_4942_);
v_a_5028_ = lean_ctor_get(v___x_4964_, 0);
v_isSharedCheck_5035_ = !lean_is_exclusive(v___x_4964_);
if (v_isSharedCheck_5035_ == 0)
{
v___x_5030_ = v___x_4964_;
v_isShared_5031_ = v_isSharedCheck_5035_;
goto v_resetjp_5029_;
}
else
{
lean_inc(v_a_5028_);
lean_dec(v___x_4964_);
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
else
{
lean_object* v_a_5038_; lean_object* v___x_5040_; uint8_t v_isShared_5041_; uint8_t v_isSharedCheck_5045_; 
lean_dec(v_a_4957_);
lean_dec_ref(v_b_4943_);
lean_dec_ref(v_a_4942_);
v_a_5038_ = lean_ctor_get(v___x_4958_, 0);
v_isSharedCheck_5045_ = !lean_is_exclusive(v___x_4958_);
if (v_isSharedCheck_5045_ == 0)
{
v___x_5040_ = v___x_4958_;
v_isShared_5041_ = v_isSharedCheck_5045_;
goto v_resetjp_5039_;
}
else
{
lean_inc(v_a_5038_);
lean_dec(v___x_4958_);
v___x_5040_ = lean_box(0);
v_isShared_5041_ = v_isSharedCheck_5045_;
goto v_resetjp_5039_;
}
v_resetjp_5039_:
{
lean_object* v___x_5043_; 
if (v_isShared_5041_ == 0)
{
v___x_5043_ = v___x_5040_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v_a_5038_);
v___x_5043_ = v_reuseFailAlloc_5044_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
return v___x_5043_;
}
}
}
}
else
{
lean_object* v_a_5046_; lean_object* v___x_5048_; uint8_t v_isShared_5049_; uint8_t v_isSharedCheck_5053_; 
lean_dec_ref(v_b_4943_);
lean_dec_ref(v_a_4942_);
v_a_5046_ = lean_ctor_get(v___x_4956_, 0);
v_isSharedCheck_5053_ = !lean_is_exclusive(v___x_4956_);
if (v_isSharedCheck_5053_ == 0)
{
v___x_5048_ = v___x_4956_;
v_isShared_5049_ = v_isSharedCheck_5053_;
goto v_resetjp_5047_;
}
else
{
lean_inc(v_a_5046_);
lean_dec(v___x_4956_);
v___x_5048_ = lean_box(0);
v_isShared_5049_ = v_isSharedCheck_5053_;
goto v_resetjp_5047_;
}
v_resetjp_5047_:
{
lean_object* v___x_5051_; 
if (v_isShared_5049_ == 0)
{
v___x_5051_ = v___x_5048_;
goto v_reusejp_5050_;
}
else
{
lean_object* v_reuseFailAlloc_5052_; 
v_reuseFailAlloc_5052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5052_, 0, v_a_5046_);
v___x_5051_ = v_reuseFailAlloc_5052_;
goto v_reusejp_5050_;
}
v_reusejp_5050_:
{
return v___x_5051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq___boxed(lean_object* v_a_5054_, lean_object* v_b_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_){
_start:
{
lean_object* v_res_5068_; 
v_res_5068_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5054_, v_b_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_);
lean_dec(v_a_5066_);
lean_dec_ref(v_a_5065_);
lean_dec(v_a_5064_);
lean_dec_ref(v_a_5063_);
lean_dec(v_a_5062_);
lean_dec_ref(v_a_5061_);
lean_dec(v_a_5060_);
lean_dec_ref(v_a_5059_);
lean_dec(v_a_5058_);
lean_dec(v_a_5057_);
lean_dec(v_a_5056_);
return v_res_5068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq(lean_object* v_a_5069_, lean_object* v_b_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_){
_start:
{
size_t v___x_5082_; size_t v___x_5083_; uint8_t v___x_5084_; 
v___x_5082_ = lean_ptr_addr(v_a_5069_);
v___x_5083_ = lean_ptr_addr(v_b_5070_);
v___x_5084_ = lean_usize_dec_eq(v___x_5082_, v___x_5083_);
if (v___x_5084_ == 0)
{
lean_object* v___x_5085_; 
v___x_5085_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5069_, v_b_5070_, v_a_5071_, v_a_5079_);
if (lean_obj_tag(v___x_5085_) == 0)
{
lean_object* v_a_5086_; 
v_a_5086_ = lean_ctor_get(v___x_5085_, 0);
lean_inc(v_a_5086_);
lean_dec_ref_known(v___x_5085_, 1);
if (lean_obj_tag(v_a_5086_) == 1)
{
lean_object* v_val_5087_; lean_object* v___x_5088_; 
v_val_5087_ = lean_ctor_get(v_a_5086_, 0);
lean_inc(v_val_5087_);
lean_dec_ref_known(v_a_5086_, 1);
v___x_5088_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_val_5087_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_);
if (lean_obj_tag(v___x_5088_) == 0)
{
lean_object* v_a_5089_; uint8_t v___x_5090_; 
v_a_5089_ = lean_ctor_get(v___x_5088_, 0);
lean_inc(v_a_5089_);
lean_dec_ref_known(v___x_5088_, 1);
v___x_5090_ = lean_unbox(v_a_5089_);
lean_dec(v_a_5089_);
if (v___x_5090_ == 0)
{
lean_object* v___x_5091_; 
v___x_5091_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5087_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_);
if (lean_obj_tag(v___x_5091_) == 0)
{
lean_object* v_a_5092_; uint8_t v___x_5093_; 
v_a_5092_ = lean_ctor_get(v___x_5091_, 0);
lean_inc(v_a_5092_);
lean_dec_ref_known(v___x_5091_, 1);
v___x_5093_ = lean_unbox(v_a_5092_);
lean_dec(v_a_5092_);
if (v___x_5093_ == 0)
{
lean_object* v___x_5094_; 
v___x_5094_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_5069_, v_b_5070_, v_val_5087_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_);
lean_dec(v_val_5087_);
return v___x_5094_;
}
else
{
lean_object* v___x_5095_; 
lean_dec(v_val_5087_);
v___x_5095_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_5069_, v_b_5070_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_);
return v___x_5095_;
}
}
else
{
lean_object* v_a_5096_; lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5103_; 
lean_dec(v_val_5087_);
lean_dec_ref(v_b_5070_);
lean_dec_ref(v_a_5069_);
v_a_5096_ = lean_ctor_get(v___x_5091_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_5091_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5098_ = v___x_5091_;
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_a_5096_);
lean_dec(v___x_5091_);
v___x_5098_ = lean_box(0);
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
v_resetjp_5097_:
{
lean_object* v___x_5101_; 
if (v_isShared_5099_ == 0)
{
v___x_5101_ = v___x_5098_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v_a_5096_);
v___x_5101_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
return v___x_5101_;
}
}
}
}
else
{
lean_object* v___x_5104_; 
v___x_5104_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5087_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_);
if (lean_obj_tag(v___x_5104_) == 0)
{
lean_object* v_a_5105_; uint8_t v___x_5106_; 
v_a_5105_ = lean_ctor_get(v___x_5104_, 0);
lean_inc(v_a_5105_);
lean_dec_ref_known(v___x_5104_, 1);
v___x_5106_ = lean_unbox(v_a_5105_);
lean_dec(v_a_5105_);
if (v___x_5106_ == 0)
{
lean_object* v___x_5107_; 
v___x_5107_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_5069_, v_b_5070_, v_val_5087_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_);
lean_dec(v_val_5087_);
return v___x_5107_;
}
else
{
lean_object* v___x_5108_; 
v___x_5108_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_5069_, v_b_5070_, v_val_5087_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_);
lean_dec(v_val_5087_);
return v___x_5108_;
}
}
else
{
lean_object* v_a_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5116_; 
lean_dec(v_val_5087_);
lean_dec_ref(v_b_5070_);
lean_dec_ref(v_a_5069_);
v_a_5109_ = lean_ctor_get(v___x_5104_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v___x_5104_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5111_ = v___x_5104_;
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_a_5109_);
lean_dec(v___x_5104_);
v___x_5111_ = lean_box(0);
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
v_resetjp_5110_:
{
lean_object* v___x_5114_; 
if (v_isShared_5112_ == 0)
{
v___x_5114_ = v___x_5111_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_a_5109_);
v___x_5114_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5113_;
}
v_reusejp_5113_:
{
return v___x_5114_;
}
}
}
}
}
else
{
lean_object* v_a_5117_; lean_object* v___x_5119_; uint8_t v_isShared_5120_; uint8_t v_isSharedCheck_5124_; 
lean_dec(v_val_5087_);
lean_dec_ref(v_b_5070_);
lean_dec_ref(v_a_5069_);
v_a_5117_ = lean_ctor_get(v___x_5088_, 0);
v_isSharedCheck_5124_ = !lean_is_exclusive(v___x_5088_);
if (v_isSharedCheck_5124_ == 0)
{
v___x_5119_ = v___x_5088_;
v_isShared_5120_ = v_isSharedCheck_5124_;
goto v_resetjp_5118_;
}
else
{
lean_inc(v_a_5117_);
lean_dec(v___x_5088_);
v___x_5119_ = lean_box(0);
v_isShared_5120_ = v_isSharedCheck_5124_;
goto v_resetjp_5118_;
}
v_resetjp_5118_:
{
lean_object* v___x_5122_; 
if (v_isShared_5120_ == 0)
{
v___x_5122_ = v___x_5119_;
goto v_reusejp_5121_;
}
else
{
lean_object* v_reuseFailAlloc_5123_; 
v_reuseFailAlloc_5123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5123_, 0, v_a_5117_);
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
lean_object* v___x_5125_; 
lean_dec(v_a_5086_);
v___x_5125_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5069_, v_b_5070_, v_a_5071_, v_a_5079_);
if (lean_obj_tag(v___x_5125_) == 0)
{
lean_object* v_a_5126_; lean_object* v___x_5128_; uint8_t v_isShared_5129_; uint8_t v_isSharedCheck_5148_; 
v_a_5126_ = lean_ctor_get(v___x_5125_, 0);
v_isSharedCheck_5148_ = !lean_is_exclusive(v___x_5125_);
if (v_isSharedCheck_5148_ == 0)
{
v___x_5128_ = v___x_5125_;
v_isShared_5129_ = v_isSharedCheck_5148_;
goto v_resetjp_5127_;
}
else
{
lean_inc(v_a_5126_);
lean_dec(v___x_5125_);
v___x_5128_ = lean_box(0);
v_isShared_5129_ = v_isSharedCheck_5148_;
goto v_resetjp_5127_;
}
v_resetjp_5127_:
{
if (lean_obj_tag(v_a_5126_) == 1)
{
lean_object* v_val_5130_; lean_object* v___x_5131_; 
lean_del_object(v___x_5128_);
v_val_5130_ = lean_ctor_get(v_a_5126_, 0);
lean_inc(v_val_5130_);
lean_dec_ref_known(v_a_5126_, 1);
v___x_5131_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_5130_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_);
if (lean_obj_tag(v___x_5131_) == 0)
{
lean_object* v_a_5132_; lean_object* v_orderedAddInst_x3f_5133_; 
v_a_5132_ = lean_ctor_get(v___x_5131_, 0);
lean_inc(v_a_5132_);
lean_dec_ref_known(v___x_5131_, 1);
v_orderedAddInst_x3f_5133_ = lean_ctor_get(v_a_5132_, 9);
lean_inc(v_orderedAddInst_x3f_5133_);
lean_dec(v_a_5132_);
if (lean_obj_tag(v_orderedAddInst_x3f_5133_) == 0)
{
lean_object* v___x_5134_; 
v___x_5134_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5069_, v_b_5070_, v_val_5130_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_);
lean_dec(v_val_5130_);
return v___x_5134_;
}
else
{
lean_object* v___x_5135_; 
lean_dec_ref_known(v_orderedAddInst_x3f_5133_, 1);
v___x_5135_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5069_, v_b_5070_, v_val_5130_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_);
lean_dec(v_val_5130_);
return v___x_5135_;
}
}
else
{
lean_object* v_a_5136_; lean_object* v___x_5138_; uint8_t v_isShared_5139_; uint8_t v_isSharedCheck_5143_; 
lean_dec(v_val_5130_);
lean_dec_ref(v_b_5070_);
lean_dec_ref(v_a_5069_);
v_a_5136_ = lean_ctor_get(v___x_5131_, 0);
v_isSharedCheck_5143_ = !lean_is_exclusive(v___x_5131_);
if (v_isSharedCheck_5143_ == 0)
{
v___x_5138_ = v___x_5131_;
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
else
{
lean_inc(v_a_5136_);
lean_dec(v___x_5131_);
v___x_5138_ = lean_box(0);
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
v_resetjp_5137_:
{
lean_object* v___x_5141_; 
if (v_isShared_5139_ == 0)
{
v___x_5141_ = v___x_5138_;
goto v_reusejp_5140_;
}
else
{
lean_object* v_reuseFailAlloc_5142_; 
v_reuseFailAlloc_5142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5142_, 0, v_a_5136_);
v___x_5141_ = v_reuseFailAlloc_5142_;
goto v_reusejp_5140_;
}
v_reusejp_5140_:
{
return v___x_5141_;
}
}
}
}
else
{
lean_object* v___x_5144_; lean_object* v___x_5146_; 
lean_dec(v_a_5126_);
lean_dec_ref(v_b_5070_);
lean_dec_ref(v_a_5069_);
v___x_5144_ = lean_box(0);
if (v_isShared_5129_ == 0)
{
lean_ctor_set(v___x_5128_, 0, v___x_5144_);
v___x_5146_ = v___x_5128_;
goto v_reusejp_5145_;
}
else
{
lean_object* v_reuseFailAlloc_5147_; 
v_reuseFailAlloc_5147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5147_, 0, v___x_5144_);
v___x_5146_ = v_reuseFailAlloc_5147_;
goto v_reusejp_5145_;
}
v_reusejp_5145_:
{
return v___x_5146_;
}
}
}
}
else
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5156_; 
lean_dec_ref(v_b_5070_);
lean_dec_ref(v_a_5069_);
v_a_5149_ = lean_ctor_get(v___x_5125_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5125_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5151_ = v___x_5125_;
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5125_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5154_; 
if (v_isShared_5152_ == 0)
{
v___x_5154_ = v___x_5151_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_a_5149_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
return v___x_5154_;
}
}
}
}
}
else
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5164_; 
lean_dec_ref(v_b_5070_);
lean_dec_ref(v_a_5069_);
v_a_5157_ = lean_ctor_get(v___x_5085_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5085_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5159_ = v___x_5085_;
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___x_5085_);
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
else
{
lean_object* v___x_5165_; lean_object* v___x_5166_; 
lean_dec_ref(v_b_5070_);
lean_dec_ref(v_a_5069_);
v___x_5165_ = lean_box(0);
v___x_5166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5166_, 0, v___x_5165_);
return v___x_5166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed(lean_object* v_a_5167_, lean_object* v_b_5168_, lean_object* v_a_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_){
_start:
{
lean_object* v_res_5180_; 
v_res_5180_ = l_Lean_Meta_Grind_Arith_Linear_processNewEq(v_a_5167_, v_b_5168_, v_a_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_, v_a_5175_, v_a_5176_, v_a_5177_, v_a_5178_);
lean_dec(v_a_5178_);
lean_dec_ref(v_a_5177_);
lean_dec(v_a_5176_);
lean_dec_ref(v_a_5175_);
lean_dec(v_a_5174_);
lean_dec_ref(v_a_5173_);
lean_dec(v_a_5172_);
lean_dec_ref(v_a_5171_);
lean_dec(v_a_5170_);
lean_dec(v_a_5169_);
return v_res_5180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object* v_a_5181_, lean_object* v_b_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_){
_start:
{
uint8_t v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; 
v___x_5195_ = 0;
v___x_5196_ = lean_box(v___x_5195_);
lean_inc_ref(v_a_5181_);
v___x_5197_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 2);
lean_closure_set(v___x_5197_, 0, v_a_5181_);
lean_closure_set(v___x_5197_, 1, v___x_5196_);
v___x_5198_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5197_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_);
if (lean_obj_tag(v___x_5198_) == 0)
{
lean_object* v_a_5199_; lean_object* v___x_5201_; uint8_t v_isShared_5202_; uint8_t v_isSharedCheck_5300_; 
v_a_5199_ = lean_ctor_get(v___x_5198_, 0);
v_isSharedCheck_5300_ = !lean_is_exclusive(v___x_5198_);
if (v_isSharedCheck_5300_ == 0)
{
v___x_5201_ = v___x_5198_;
v_isShared_5202_ = v_isSharedCheck_5300_;
goto v_resetjp_5200_;
}
else
{
lean_inc(v_a_5199_);
lean_dec(v___x_5198_);
v___x_5201_ = lean_box(0);
v_isShared_5202_ = v_isSharedCheck_5300_;
goto v_resetjp_5200_;
}
v_resetjp_5200_:
{
if (lean_obj_tag(v_a_5199_) == 1)
{
lean_object* v_val_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; 
lean_del_object(v___x_5201_);
v_val_5203_ = lean_ctor_get(v_a_5199_, 0);
lean_inc(v_val_5203_);
lean_dec_ref_known(v_a_5199_, 1);
v___x_5204_ = lean_box(v___x_5195_);
lean_inc_ref(v_b_5182_);
v___x_5205_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 2);
lean_closure_set(v___x_5205_, 0, v_b_5182_);
lean_closure_set(v___x_5205_, 1, v___x_5204_);
v___x_5206_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5205_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_);
if (lean_obj_tag(v___x_5206_) == 0)
{
lean_object* v_a_5207_; lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5287_; 
v_a_5207_ = lean_ctor_get(v___x_5206_, 0);
v_isSharedCheck_5287_ = !lean_is_exclusive(v___x_5206_);
if (v_isSharedCheck_5287_ == 0)
{
v___x_5209_ = v___x_5206_;
v_isShared_5210_ = v_isSharedCheck_5287_;
goto v_resetjp_5208_;
}
else
{
lean_inc(v_a_5207_);
lean_dec(v___x_5206_);
v___x_5209_ = lean_box(0);
v_isShared_5210_ = v_isSharedCheck_5287_;
goto v_resetjp_5208_;
}
v_resetjp_5208_:
{
if (lean_obj_tag(v_a_5207_) == 1)
{
lean_object* v_val_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; 
lean_del_object(v___x_5209_);
v_val_5211_ = lean_ctor_get(v_a_5207_, 0);
lean_inc_n(v_val_5211_, 2);
lean_dec_ref_known(v_a_5207_, 1);
lean_inc(v_val_5203_);
v___x_5212_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_5212_, 0, v_val_5203_);
lean_ctor_set(v___x_5212_, 1, v_val_5211_);
v___x_5213_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_5212_);
lean_inc_ref(v_b_5182_);
lean_inc_ref(v_a_5181_);
v___x_5214_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5214_, 0, v_a_5181_);
lean_ctor_set(v___x_5214_, 1, v_b_5182_);
lean_ctor_set(v___x_5214_, 2, v_val_5203_);
lean_ctor_set(v___x_5214_, 3, v_val_5211_);
v___x_5215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5215_, 0, v___x_5213_);
lean_ctor_set(v___x_5215_, 1, v___x_5214_);
v___x_5216_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(v___x_5215_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_);
if (lean_obj_tag(v___x_5216_) == 0)
{
lean_object* v_a_5217_; lean_object* v_p_5218_; lean_object* v___x_5219_; 
v_a_5217_ = lean_ctor_get(v___x_5216_, 0);
lean_inc(v_a_5217_);
lean_dec_ref_known(v___x_5216_, 1);
v_p_5218_ = lean_ctor_get(v_a_5217_, 0);
v___x_5219_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5181_, v_a_5184_);
lean_dec_ref(v_a_5181_);
if (lean_obj_tag(v___x_5219_) == 0)
{
lean_object* v_a_5220_; lean_object* v___x_5221_; 
v_a_5220_ = lean_ctor_get(v___x_5219_, 0);
lean_inc(v_a_5220_);
lean_dec_ref_known(v___x_5219_, 1);
v___x_5221_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5182_, v_a_5184_);
lean_dec_ref(v_b_5182_);
if (lean_obj_tag(v___x_5221_) == 0)
{
lean_object* v_a_5222_; lean_object* v___y_5224_; uint8_t v___x_5258_; 
v_a_5222_ = lean_ctor_get(v___x_5221_, 0);
lean_inc(v_a_5222_);
lean_dec_ref_known(v___x_5221_, 1);
v___x_5258_ = lean_nat_dec_le(v_a_5220_, v_a_5222_);
if (v___x_5258_ == 0)
{
lean_dec(v_a_5222_);
v___y_5224_ = v_a_5220_;
goto v___jp_5223_;
}
else
{
lean_dec(v_a_5220_);
v___y_5224_ = v_a_5222_;
goto v___jp_5223_;
}
v___jp_5223_:
{
lean_object* v___x_5225_; 
lean_inc_ref(v_p_5218_);
v___x_5225_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_5218_, v___y_5224_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_);
if (lean_obj_tag(v___x_5225_) == 0)
{
lean_object* v_a_5226_; lean_object* v___x_5227_; 
v_a_5226_ = lean_ctor_get(v___x_5225_, 0);
lean_inc(v_a_5226_);
lean_dec_ref_known(v___x_5225_, 1);
v___x_5227_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5226_, v___x_5195_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_);
if (lean_obj_tag(v___x_5227_) == 0)
{
lean_object* v_a_5228_; lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5241_; 
v_a_5228_ = lean_ctor_get(v___x_5227_, 0);
v_isSharedCheck_5241_ = !lean_is_exclusive(v___x_5227_);
if (v_isSharedCheck_5241_ == 0)
{
v___x_5230_ = v___x_5227_;
v_isShared_5231_ = v_isSharedCheck_5241_;
goto v_resetjp_5229_;
}
else
{
lean_inc(v_a_5228_);
lean_dec(v___x_5227_);
v___x_5230_ = lean_box(0);
v_isShared_5231_ = v_isSharedCheck_5241_;
goto v_resetjp_5229_;
}
v_resetjp_5229_:
{
if (lean_obj_tag(v_a_5228_) == 1)
{
lean_object* v_val_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; 
lean_del_object(v___x_5230_);
v_val_5232_ = lean_ctor_get(v_a_5228_, 0);
lean_inc_n(v_val_5232_, 2);
lean_dec_ref_known(v_a_5228_, 1);
v___x_5233_ = l_Lean_Grind_Linarith_Expr_norm(v_val_5232_);
v___x_5234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5234_, 0, v_a_5217_);
lean_ctor_set(v___x_5234_, 1, v_val_5232_);
v___x_5235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5235_, 0, v___x_5233_);
lean_ctor_set(v___x_5235_, 1, v___x_5234_);
v___x_5236_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5235_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_);
return v___x_5236_;
}
else
{
lean_object* v___x_5237_; lean_object* v___x_5239_; 
lean_dec(v_a_5228_);
lean_dec(v_a_5217_);
v___x_5237_ = lean_box(0);
if (v_isShared_5231_ == 0)
{
lean_ctor_set(v___x_5230_, 0, v___x_5237_);
v___x_5239_ = v___x_5230_;
goto v_reusejp_5238_;
}
else
{
lean_object* v_reuseFailAlloc_5240_; 
v_reuseFailAlloc_5240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5240_, 0, v___x_5237_);
v___x_5239_ = v_reuseFailAlloc_5240_;
goto v_reusejp_5238_;
}
v_reusejp_5238_:
{
return v___x_5239_;
}
}
}
}
else
{
lean_object* v_a_5242_; lean_object* v___x_5244_; uint8_t v_isShared_5245_; uint8_t v_isSharedCheck_5249_; 
lean_dec(v_a_5217_);
v_a_5242_ = lean_ctor_get(v___x_5227_, 0);
v_isSharedCheck_5249_ = !lean_is_exclusive(v___x_5227_);
if (v_isSharedCheck_5249_ == 0)
{
v___x_5244_ = v___x_5227_;
v_isShared_5245_ = v_isSharedCheck_5249_;
goto v_resetjp_5243_;
}
else
{
lean_inc(v_a_5242_);
lean_dec(v___x_5227_);
v___x_5244_ = lean_box(0);
v_isShared_5245_ = v_isSharedCheck_5249_;
goto v_resetjp_5243_;
}
v_resetjp_5243_:
{
lean_object* v___x_5247_; 
if (v_isShared_5245_ == 0)
{
v___x_5247_ = v___x_5244_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v_a_5242_);
v___x_5247_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
return v___x_5247_;
}
}
}
}
else
{
lean_object* v_a_5250_; lean_object* v___x_5252_; uint8_t v_isShared_5253_; uint8_t v_isSharedCheck_5257_; 
lean_dec(v_a_5217_);
v_a_5250_ = lean_ctor_get(v___x_5225_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v___x_5225_);
if (v_isSharedCheck_5257_ == 0)
{
v___x_5252_ = v___x_5225_;
v_isShared_5253_ = v_isSharedCheck_5257_;
goto v_resetjp_5251_;
}
else
{
lean_inc(v_a_5250_);
lean_dec(v___x_5225_);
v___x_5252_ = lean_box(0);
v_isShared_5253_ = v_isSharedCheck_5257_;
goto v_resetjp_5251_;
}
v_resetjp_5251_:
{
lean_object* v___x_5255_; 
if (v_isShared_5253_ == 0)
{
v___x_5255_ = v___x_5252_;
goto v_reusejp_5254_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v_a_5250_);
v___x_5255_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5254_;
}
v_reusejp_5254_:
{
return v___x_5255_;
}
}
}
}
}
else
{
lean_object* v_a_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5266_; 
lean_dec(v_a_5220_);
lean_dec(v_a_5217_);
v_a_5259_ = lean_ctor_get(v___x_5221_, 0);
v_isSharedCheck_5266_ = !lean_is_exclusive(v___x_5221_);
if (v_isSharedCheck_5266_ == 0)
{
v___x_5261_ = v___x_5221_;
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_a_5259_);
lean_dec(v___x_5221_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v___x_5264_; 
if (v_isShared_5262_ == 0)
{
v___x_5264_ = v___x_5261_;
goto v_reusejp_5263_;
}
else
{
lean_object* v_reuseFailAlloc_5265_; 
v_reuseFailAlloc_5265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5265_, 0, v_a_5259_);
v___x_5264_ = v_reuseFailAlloc_5265_;
goto v_reusejp_5263_;
}
v_reusejp_5263_:
{
return v___x_5264_;
}
}
}
}
else
{
lean_object* v_a_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5274_; 
lean_dec(v_a_5217_);
lean_dec_ref(v_b_5182_);
v_a_5267_ = lean_ctor_get(v___x_5219_, 0);
v_isSharedCheck_5274_ = !lean_is_exclusive(v___x_5219_);
if (v_isSharedCheck_5274_ == 0)
{
v___x_5269_ = v___x_5219_;
v_isShared_5270_ = v_isSharedCheck_5274_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_a_5267_);
lean_dec(v___x_5219_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5274_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
lean_object* v___x_5272_; 
if (v_isShared_5270_ == 0)
{
v___x_5272_ = v___x_5269_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5273_; 
v_reuseFailAlloc_5273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5273_, 0, v_a_5267_);
v___x_5272_ = v_reuseFailAlloc_5273_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
return v___x_5272_;
}
}
}
}
else
{
lean_object* v_a_5275_; lean_object* v___x_5277_; uint8_t v_isShared_5278_; uint8_t v_isSharedCheck_5282_; 
lean_dec_ref(v_b_5182_);
lean_dec_ref(v_a_5181_);
v_a_5275_ = lean_ctor_get(v___x_5216_, 0);
v_isSharedCheck_5282_ = !lean_is_exclusive(v___x_5216_);
if (v_isSharedCheck_5282_ == 0)
{
v___x_5277_ = v___x_5216_;
v_isShared_5278_ = v_isSharedCheck_5282_;
goto v_resetjp_5276_;
}
else
{
lean_inc(v_a_5275_);
lean_dec(v___x_5216_);
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
lean_dec(v_a_5207_);
lean_dec(v_val_5203_);
lean_dec_ref(v_b_5182_);
lean_dec_ref(v_a_5181_);
v___x_5283_ = lean_box(0);
if (v_isShared_5210_ == 0)
{
lean_ctor_set(v___x_5209_, 0, v___x_5283_);
v___x_5285_ = v___x_5209_;
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
lean_dec(v_val_5203_);
lean_dec_ref(v_b_5182_);
lean_dec_ref(v_a_5181_);
v_a_5288_ = lean_ctor_get(v___x_5206_, 0);
v_isSharedCheck_5295_ = !lean_is_exclusive(v___x_5206_);
if (v_isSharedCheck_5295_ == 0)
{
v___x_5290_ = v___x_5206_;
v_isShared_5291_ = v_isSharedCheck_5295_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_a_5288_);
lean_dec(v___x_5206_);
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
else
{
lean_object* v___x_5296_; lean_object* v___x_5298_; 
lean_dec(v_a_5199_);
lean_dec_ref(v_b_5182_);
lean_dec_ref(v_a_5181_);
v___x_5296_ = lean_box(0);
if (v_isShared_5202_ == 0)
{
lean_ctor_set(v___x_5201_, 0, v___x_5296_);
v___x_5298_ = v___x_5201_;
goto v_reusejp_5297_;
}
else
{
lean_object* v_reuseFailAlloc_5299_; 
v_reuseFailAlloc_5299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5299_, 0, v___x_5296_);
v___x_5298_ = v_reuseFailAlloc_5299_;
goto v_reusejp_5297_;
}
v_reusejp_5297_:
{
return v___x_5298_;
}
}
}
}
else
{
lean_object* v_a_5301_; lean_object* v___x_5303_; uint8_t v_isShared_5304_; uint8_t v_isSharedCheck_5308_; 
lean_dec_ref(v_b_5182_);
lean_dec_ref(v_a_5181_);
v_a_5301_ = lean_ctor_get(v___x_5198_, 0);
v_isSharedCheck_5308_ = !lean_is_exclusive(v___x_5198_);
if (v_isSharedCheck_5308_ == 0)
{
v___x_5303_ = v___x_5198_;
v_isShared_5304_ = v_isSharedCheck_5308_;
goto v_resetjp_5302_;
}
else
{
lean_inc(v_a_5301_);
lean_dec(v___x_5198_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq___boxed(lean_object* v_a_5309_, lean_object* v_b_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_){
_start:
{
lean_object* v_res_5323_; 
v_res_5323_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5309_, v_b_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_);
lean_dec(v_a_5321_);
lean_dec_ref(v_a_5320_);
lean_dec(v_a_5319_);
lean_dec_ref(v_a_5318_);
lean_dec(v_a_5317_);
lean_dec_ref(v_a_5316_);
lean_dec(v_a_5315_);
lean_dec_ref(v_a_5314_);
lean_dec(v_a_5313_);
lean_dec(v_a_5312_);
lean_dec(v_a_5311_);
return v_res_5323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(lean_object* v_a_5324_, lean_object* v_b_5325_, lean_object* v_a_5326_, lean_object* v_a_5327_, lean_object* v_a_5328_, lean_object* v_a_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_, lean_object* v_a_5336_){
_start:
{
uint8_t v___x_5338_; lean_object* v___x_5339_; 
v___x_5338_ = 0;
lean_inc_ref(v_a_5324_);
v___x_5339_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5324_, v___x_5338_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_);
if (lean_obj_tag(v___x_5339_) == 0)
{
lean_object* v_a_5340_; lean_object* v___x_5342_; uint8_t v_isShared_5343_; uint8_t v_isSharedCheck_5373_; 
v_a_5340_ = lean_ctor_get(v___x_5339_, 0);
v_isSharedCheck_5373_ = !lean_is_exclusive(v___x_5339_);
if (v_isSharedCheck_5373_ == 0)
{
v___x_5342_ = v___x_5339_;
v_isShared_5343_ = v_isSharedCheck_5373_;
goto v_resetjp_5341_;
}
else
{
lean_inc(v_a_5340_);
lean_dec(v___x_5339_);
v___x_5342_ = lean_box(0);
v_isShared_5343_ = v_isSharedCheck_5373_;
goto v_resetjp_5341_;
}
v_resetjp_5341_:
{
if (lean_obj_tag(v_a_5340_) == 1)
{
lean_object* v_val_5344_; lean_object* v___x_5345_; 
lean_del_object(v___x_5342_);
v_val_5344_ = lean_ctor_get(v_a_5340_, 0);
lean_inc(v_val_5344_);
lean_dec_ref_known(v_a_5340_, 1);
lean_inc_ref(v_b_5325_);
v___x_5345_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_5325_, v___x_5338_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_);
if (lean_obj_tag(v___x_5345_) == 0)
{
lean_object* v_a_5346_; lean_object* v___x_5348_; uint8_t v_isShared_5349_; uint8_t v_isSharedCheck_5360_; 
v_a_5346_ = lean_ctor_get(v___x_5345_, 0);
v_isSharedCheck_5360_ = !lean_is_exclusive(v___x_5345_);
if (v_isSharedCheck_5360_ == 0)
{
v___x_5348_ = v___x_5345_;
v_isShared_5349_ = v_isSharedCheck_5360_;
goto v_resetjp_5347_;
}
else
{
lean_inc(v_a_5346_);
lean_dec(v___x_5345_);
v___x_5348_ = lean_box(0);
v_isShared_5349_ = v_isSharedCheck_5360_;
goto v_resetjp_5347_;
}
v_resetjp_5347_:
{
if (lean_obj_tag(v_a_5346_) == 1)
{
lean_object* v_val_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; 
lean_del_object(v___x_5348_);
v_val_5350_ = lean_ctor_get(v_a_5346_, 0);
lean_inc_n(v_val_5350_, 2);
lean_dec_ref_known(v_a_5346_, 1);
lean_inc(v_val_5344_);
v___x_5351_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5351_, 0, v_val_5344_);
lean_ctor_set(v___x_5351_, 1, v_val_5350_);
v___x_5352_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5351_);
v___x_5353_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5353_, 0, v_a_5324_);
lean_ctor_set(v___x_5353_, 1, v_b_5325_);
lean_ctor_set(v___x_5353_, 2, v_val_5344_);
lean_ctor_set(v___x_5353_, 3, v_val_5350_);
v___x_5354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5354_, 0, v___x_5352_);
lean_ctor_set(v___x_5354_, 1, v___x_5353_);
v___x_5355_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5354_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_);
return v___x_5355_;
}
else
{
lean_object* v___x_5356_; lean_object* v___x_5358_; 
lean_dec(v_a_5346_);
lean_dec(v_val_5344_);
lean_dec_ref(v_b_5325_);
lean_dec_ref(v_a_5324_);
v___x_5356_ = lean_box(0);
if (v_isShared_5349_ == 0)
{
lean_ctor_set(v___x_5348_, 0, v___x_5356_);
v___x_5358_ = v___x_5348_;
goto v_reusejp_5357_;
}
else
{
lean_object* v_reuseFailAlloc_5359_; 
v_reuseFailAlloc_5359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5359_, 0, v___x_5356_);
v___x_5358_ = v_reuseFailAlloc_5359_;
goto v_reusejp_5357_;
}
v_reusejp_5357_:
{
return v___x_5358_;
}
}
}
}
else
{
lean_object* v_a_5361_; lean_object* v___x_5363_; uint8_t v_isShared_5364_; uint8_t v_isSharedCheck_5368_; 
lean_dec(v_val_5344_);
lean_dec_ref(v_b_5325_);
lean_dec_ref(v_a_5324_);
v_a_5361_ = lean_ctor_get(v___x_5345_, 0);
v_isSharedCheck_5368_ = !lean_is_exclusive(v___x_5345_);
if (v_isSharedCheck_5368_ == 0)
{
v___x_5363_ = v___x_5345_;
v_isShared_5364_ = v_isSharedCheck_5368_;
goto v_resetjp_5362_;
}
else
{
lean_inc(v_a_5361_);
lean_dec(v___x_5345_);
v___x_5363_ = lean_box(0);
v_isShared_5364_ = v_isSharedCheck_5368_;
goto v_resetjp_5362_;
}
v_resetjp_5362_:
{
lean_object* v___x_5366_; 
if (v_isShared_5364_ == 0)
{
v___x_5366_ = v___x_5363_;
goto v_reusejp_5365_;
}
else
{
lean_object* v_reuseFailAlloc_5367_; 
v_reuseFailAlloc_5367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_a_5361_);
v___x_5366_ = v_reuseFailAlloc_5367_;
goto v_reusejp_5365_;
}
v_reusejp_5365_:
{
return v___x_5366_;
}
}
}
}
else
{
lean_object* v___x_5369_; lean_object* v___x_5371_; 
lean_dec(v_a_5340_);
lean_dec_ref(v_b_5325_);
lean_dec_ref(v_a_5324_);
v___x_5369_ = lean_box(0);
if (v_isShared_5343_ == 0)
{
lean_ctor_set(v___x_5342_, 0, v___x_5369_);
v___x_5371_ = v___x_5342_;
goto v_reusejp_5370_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v___x_5369_);
v___x_5371_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5370_;
}
v_reusejp_5370_:
{
return v___x_5371_;
}
}
}
}
else
{
lean_object* v_a_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5381_; 
lean_dec_ref(v_b_5325_);
lean_dec_ref(v_a_5324_);
v_a_5374_ = lean_ctor_get(v___x_5339_, 0);
v_isSharedCheck_5381_ = !lean_is_exclusive(v___x_5339_);
if (v_isSharedCheck_5381_ == 0)
{
v___x_5376_ = v___x_5339_;
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_a_5374_);
lean_dec(v___x_5339_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
lean_object* v___x_5379_; 
if (v_isShared_5377_ == 0)
{
v___x_5379_ = v___x_5376_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v_a_5374_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq___boxed(lean_object* v_a_5382_, lean_object* v_b_5383_, lean_object* v_a_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_, lean_object* v_a_5388_, lean_object* v_a_5389_, lean_object* v_a_5390_, lean_object* v_a_5391_, lean_object* v_a_5392_, lean_object* v_a_5393_, lean_object* v_a_5394_, lean_object* v_a_5395_){
_start:
{
lean_object* v_res_5396_; 
v_res_5396_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5382_, v_b_5383_, v_a_5384_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_, v_a_5392_, v_a_5393_, v_a_5394_);
lean_dec(v_a_5394_);
lean_dec_ref(v_a_5393_);
lean_dec(v_a_5392_);
lean_dec_ref(v_a_5391_);
lean_dec(v_a_5390_);
lean_dec_ref(v_a_5389_);
lean_dec(v_a_5388_);
lean_dec_ref(v_a_5387_);
lean_dec(v_a_5386_);
lean_dec(v_a_5385_);
lean_dec(v_a_5384_);
return v_res_5396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(lean_object* v_a_5397_, lean_object* v_b_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_){
_start:
{
lean_object* v___x_5411_; 
v___x_5411_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_);
if (lean_obj_tag(v___x_5411_) == 0)
{
lean_object* v_a_5412_; lean_object* v_addRightCancelInst_x3f_5413_; 
v_a_5412_ = lean_ctor_get(v___x_5411_, 0);
lean_inc(v_a_5412_);
lean_dec_ref_known(v___x_5411_, 1);
v_addRightCancelInst_x3f_5413_ = lean_ctor_get(v_a_5412_, 11);
if (lean_obj_tag(v_addRightCancelInst_x3f_5413_) == 0)
{
lean_object* v___x_5414_; 
lean_dec(v_a_5412_);
v___x_5414_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(v_a_5397_, v_b_5398_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_);
return v___x_5414_;
}
else
{
lean_object* v_id_5415_; lean_object* v_structId_5416_; lean_object* v___x_5417_; 
v_id_5415_ = lean_ctor_get(v_a_5412_, 0);
lean_inc(v_id_5415_);
v_structId_5416_ = lean_ctor_get(v_a_5412_, 1);
lean_inc(v_structId_5416_);
lean_dec(v_a_5412_);
lean_inc_ref(v_a_5397_);
v___x_5417_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5397_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_);
if (lean_obj_tag(v___x_5417_) == 0)
{
lean_object* v_a_5418_; lean_object* v_fst_5419_; lean_object* v___x_5421_; uint8_t v_isShared_5422_; uint8_t v_isSharedCheck_5487_; 
v_a_5418_ = lean_ctor_get(v___x_5417_, 0);
lean_inc(v_a_5418_);
lean_dec_ref_known(v___x_5417_, 1);
v_fst_5419_ = lean_ctor_get(v_a_5418_, 0);
v_isSharedCheck_5487_ = !lean_is_exclusive(v_a_5418_);
if (v_isSharedCheck_5487_ == 0)
{
lean_object* v_unused_5488_; 
v_unused_5488_ = lean_ctor_get(v_a_5418_, 1);
lean_dec(v_unused_5488_);
v___x_5421_ = v_a_5418_;
v_isShared_5422_ = v_isSharedCheck_5487_;
goto v_resetjp_5420_;
}
else
{
lean_inc(v_fst_5419_);
lean_dec(v_a_5418_);
v___x_5421_ = lean_box(0);
v_isShared_5422_ = v_isSharedCheck_5487_;
goto v_resetjp_5420_;
}
v_resetjp_5420_:
{
lean_object* v___x_5423_; 
lean_inc_ref(v_b_5398_);
v___x_5423_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5398_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_);
if (lean_obj_tag(v___x_5423_) == 0)
{
lean_object* v_a_5424_; lean_object* v_fst_5425_; lean_object* v___x_5427_; uint8_t v_isShared_5428_; uint8_t v_isSharedCheck_5477_; 
v_a_5424_ = lean_ctor_get(v___x_5423_, 0);
lean_inc(v_a_5424_);
lean_dec_ref_known(v___x_5423_, 1);
v_fst_5425_ = lean_ctor_get(v_a_5424_, 0);
v_isSharedCheck_5477_ = !lean_is_exclusive(v_a_5424_);
if (v_isSharedCheck_5477_ == 0)
{
lean_object* v_unused_5478_; 
v_unused_5478_ = lean_ctor_get(v_a_5424_, 1);
lean_dec(v_unused_5478_);
v___x_5427_ = v_a_5424_;
v_isShared_5428_ = v_isSharedCheck_5477_;
goto v_resetjp_5426_;
}
else
{
lean_inc(v_fst_5425_);
lean_dec(v_a_5424_);
v___x_5427_ = lean_box(0);
v_isShared_5428_ = v_isSharedCheck_5477_;
goto v_resetjp_5426_;
}
v_resetjp_5426_:
{
uint8_t v___x_5429_; lean_object* v___x_5430_; 
v___x_5429_ = 0;
v___x_5430_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5419_, v___x_5429_, v_structId_5416_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_);
if (lean_obj_tag(v___x_5430_) == 0)
{
lean_object* v_a_5431_; lean_object* v___x_5433_; uint8_t v_isShared_5434_; uint8_t v_isSharedCheck_5468_; 
v_a_5431_ = lean_ctor_get(v___x_5430_, 0);
v_isSharedCheck_5468_ = !lean_is_exclusive(v___x_5430_);
if (v_isSharedCheck_5468_ == 0)
{
v___x_5433_ = v___x_5430_;
v_isShared_5434_ = v_isSharedCheck_5468_;
goto v_resetjp_5432_;
}
else
{
lean_inc(v_a_5431_);
lean_dec(v___x_5430_);
v___x_5433_ = lean_box(0);
v_isShared_5434_ = v_isSharedCheck_5468_;
goto v_resetjp_5432_;
}
v_resetjp_5432_:
{
if (lean_obj_tag(v_a_5431_) == 1)
{
lean_object* v_val_5435_; lean_object* v___x_5436_; 
lean_del_object(v___x_5433_);
v_val_5435_ = lean_ctor_get(v_a_5431_, 0);
lean_inc(v_val_5435_);
lean_dec_ref_known(v_a_5431_, 1);
v___x_5436_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5425_, v___x_5429_, v_structId_5416_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_);
if (lean_obj_tag(v___x_5436_) == 0)
{
lean_object* v_a_5437_; lean_object* v___x_5439_; uint8_t v_isShared_5440_; uint8_t v_isSharedCheck_5455_; 
v_a_5437_ = lean_ctor_get(v___x_5436_, 0);
v_isSharedCheck_5455_ = !lean_is_exclusive(v___x_5436_);
if (v_isSharedCheck_5455_ == 0)
{
v___x_5439_ = v___x_5436_;
v_isShared_5440_ = v_isSharedCheck_5455_;
goto v_resetjp_5438_;
}
else
{
lean_inc(v_a_5437_);
lean_dec(v___x_5436_);
v___x_5439_ = lean_box(0);
v_isShared_5440_ = v_isSharedCheck_5455_;
goto v_resetjp_5438_;
}
v_resetjp_5438_:
{
if (lean_obj_tag(v_a_5437_) == 1)
{
lean_object* v_val_5441_; lean_object* v___x_5443_; 
lean_del_object(v___x_5439_);
v_val_5441_ = lean_ctor_get(v_a_5437_, 0);
lean_inc_n(v_val_5441_, 2);
lean_dec_ref_known(v_a_5437_, 1);
lean_inc(v_val_5435_);
if (v_isShared_5428_ == 0)
{
lean_ctor_set_tag(v___x_5427_, 3);
lean_ctor_set(v___x_5427_, 1, v_val_5441_);
lean_ctor_set(v___x_5427_, 0, v_val_5435_);
v___x_5443_ = v___x_5427_;
goto v_reusejp_5442_;
}
else
{
lean_object* v_reuseFailAlloc_5450_; 
v_reuseFailAlloc_5450_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5450_, 0, v_val_5435_);
lean_ctor_set(v_reuseFailAlloc_5450_, 1, v_val_5441_);
v___x_5443_ = v_reuseFailAlloc_5450_;
goto v_reusejp_5442_;
}
v_reusejp_5442_:
{
lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5447_; 
v___x_5444_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5443_);
v___x_5445_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5445_, 0, v_a_5397_);
lean_ctor_set(v___x_5445_, 1, v_b_5398_);
lean_ctor_set(v___x_5445_, 2, v_id_5415_);
lean_ctor_set(v___x_5445_, 3, v_val_5435_);
lean_ctor_set(v___x_5445_, 4, v_val_5441_);
if (v_isShared_5422_ == 0)
{
lean_ctor_set(v___x_5421_, 1, v___x_5445_);
lean_ctor_set(v___x_5421_, 0, v___x_5444_);
v___x_5447_ = v___x_5421_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5449_; 
v_reuseFailAlloc_5449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5449_, 0, v___x_5444_);
lean_ctor_set(v_reuseFailAlloc_5449_, 1, v___x_5445_);
v___x_5447_ = v_reuseFailAlloc_5449_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
lean_object* v___x_5448_; 
v___x_5448_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5447_, v_structId_5416_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_);
lean_dec(v_structId_5416_);
return v___x_5448_;
}
}
}
else
{
lean_object* v___x_5451_; lean_object* v___x_5453_; 
lean_dec(v_a_5437_);
lean_dec(v_val_5435_);
lean_del_object(v___x_5427_);
lean_del_object(v___x_5421_);
lean_dec(v_structId_5416_);
lean_dec(v_id_5415_);
lean_dec_ref(v_b_5398_);
lean_dec_ref(v_a_5397_);
v___x_5451_ = lean_box(0);
if (v_isShared_5440_ == 0)
{
lean_ctor_set(v___x_5439_, 0, v___x_5451_);
v___x_5453_ = v___x_5439_;
goto v_reusejp_5452_;
}
else
{
lean_object* v_reuseFailAlloc_5454_; 
v_reuseFailAlloc_5454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5454_, 0, v___x_5451_);
v___x_5453_ = v_reuseFailAlloc_5454_;
goto v_reusejp_5452_;
}
v_reusejp_5452_:
{
return v___x_5453_;
}
}
}
}
else
{
lean_object* v_a_5456_; lean_object* v___x_5458_; uint8_t v_isShared_5459_; uint8_t v_isSharedCheck_5463_; 
lean_dec(v_val_5435_);
lean_del_object(v___x_5427_);
lean_del_object(v___x_5421_);
lean_dec(v_structId_5416_);
lean_dec(v_id_5415_);
lean_dec_ref(v_b_5398_);
lean_dec_ref(v_a_5397_);
v_a_5456_ = lean_ctor_get(v___x_5436_, 0);
v_isSharedCheck_5463_ = !lean_is_exclusive(v___x_5436_);
if (v_isSharedCheck_5463_ == 0)
{
v___x_5458_ = v___x_5436_;
v_isShared_5459_ = v_isSharedCheck_5463_;
goto v_resetjp_5457_;
}
else
{
lean_inc(v_a_5456_);
lean_dec(v___x_5436_);
v___x_5458_ = lean_box(0);
v_isShared_5459_ = v_isSharedCheck_5463_;
goto v_resetjp_5457_;
}
v_resetjp_5457_:
{
lean_object* v___x_5461_; 
if (v_isShared_5459_ == 0)
{
v___x_5461_ = v___x_5458_;
goto v_reusejp_5460_;
}
else
{
lean_object* v_reuseFailAlloc_5462_; 
v_reuseFailAlloc_5462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5462_, 0, v_a_5456_);
v___x_5461_ = v_reuseFailAlloc_5462_;
goto v_reusejp_5460_;
}
v_reusejp_5460_:
{
return v___x_5461_;
}
}
}
}
else
{
lean_object* v___x_5464_; lean_object* v___x_5466_; 
lean_dec(v_a_5431_);
lean_del_object(v___x_5427_);
lean_dec(v_fst_5425_);
lean_del_object(v___x_5421_);
lean_dec(v_structId_5416_);
lean_dec(v_id_5415_);
lean_dec_ref(v_b_5398_);
lean_dec_ref(v_a_5397_);
v___x_5464_ = lean_box(0);
if (v_isShared_5434_ == 0)
{
lean_ctor_set(v___x_5433_, 0, v___x_5464_);
v___x_5466_ = v___x_5433_;
goto v_reusejp_5465_;
}
else
{
lean_object* v_reuseFailAlloc_5467_; 
v_reuseFailAlloc_5467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5467_, 0, v___x_5464_);
v___x_5466_ = v_reuseFailAlloc_5467_;
goto v_reusejp_5465_;
}
v_reusejp_5465_:
{
return v___x_5466_;
}
}
}
}
else
{
lean_object* v_a_5469_; lean_object* v___x_5471_; uint8_t v_isShared_5472_; uint8_t v_isSharedCheck_5476_; 
lean_del_object(v___x_5427_);
lean_dec(v_fst_5425_);
lean_del_object(v___x_5421_);
lean_dec(v_structId_5416_);
lean_dec(v_id_5415_);
lean_dec_ref(v_b_5398_);
lean_dec_ref(v_a_5397_);
v_a_5469_ = lean_ctor_get(v___x_5430_, 0);
v_isSharedCheck_5476_ = !lean_is_exclusive(v___x_5430_);
if (v_isSharedCheck_5476_ == 0)
{
v___x_5471_ = v___x_5430_;
v_isShared_5472_ = v_isSharedCheck_5476_;
goto v_resetjp_5470_;
}
else
{
lean_inc(v_a_5469_);
lean_dec(v___x_5430_);
v___x_5471_ = lean_box(0);
v_isShared_5472_ = v_isSharedCheck_5476_;
goto v_resetjp_5470_;
}
v_resetjp_5470_:
{
lean_object* v___x_5474_; 
if (v_isShared_5472_ == 0)
{
v___x_5474_ = v___x_5471_;
goto v_reusejp_5473_;
}
else
{
lean_object* v_reuseFailAlloc_5475_; 
v_reuseFailAlloc_5475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5475_, 0, v_a_5469_);
v___x_5474_ = v_reuseFailAlloc_5475_;
goto v_reusejp_5473_;
}
v_reusejp_5473_:
{
return v___x_5474_;
}
}
}
}
}
else
{
lean_object* v_a_5479_; lean_object* v___x_5481_; uint8_t v_isShared_5482_; uint8_t v_isSharedCheck_5486_; 
lean_del_object(v___x_5421_);
lean_dec(v_fst_5419_);
lean_dec(v_structId_5416_);
lean_dec(v_id_5415_);
lean_dec_ref(v_b_5398_);
lean_dec_ref(v_a_5397_);
v_a_5479_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5486_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5486_ == 0)
{
v___x_5481_ = v___x_5423_;
v_isShared_5482_ = v_isSharedCheck_5486_;
goto v_resetjp_5480_;
}
else
{
lean_inc(v_a_5479_);
lean_dec(v___x_5423_);
v___x_5481_ = lean_box(0);
v_isShared_5482_ = v_isSharedCheck_5486_;
goto v_resetjp_5480_;
}
v_resetjp_5480_:
{
lean_object* v___x_5484_; 
if (v_isShared_5482_ == 0)
{
v___x_5484_ = v___x_5481_;
goto v_reusejp_5483_;
}
else
{
lean_object* v_reuseFailAlloc_5485_; 
v_reuseFailAlloc_5485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5485_, 0, v_a_5479_);
v___x_5484_ = v_reuseFailAlloc_5485_;
goto v_reusejp_5483_;
}
v_reusejp_5483_:
{
return v___x_5484_;
}
}
}
}
}
else
{
lean_object* v_a_5489_; lean_object* v___x_5491_; uint8_t v_isShared_5492_; uint8_t v_isSharedCheck_5496_; 
lean_dec(v_structId_5416_);
lean_dec(v_id_5415_);
lean_dec_ref(v_b_5398_);
lean_dec_ref(v_a_5397_);
v_a_5489_ = lean_ctor_get(v___x_5417_, 0);
v_isSharedCheck_5496_ = !lean_is_exclusive(v___x_5417_);
if (v_isSharedCheck_5496_ == 0)
{
v___x_5491_ = v___x_5417_;
v_isShared_5492_ = v_isSharedCheck_5496_;
goto v_resetjp_5490_;
}
else
{
lean_inc(v_a_5489_);
lean_dec(v___x_5417_);
v___x_5491_ = lean_box(0);
v_isShared_5492_ = v_isSharedCheck_5496_;
goto v_resetjp_5490_;
}
v_resetjp_5490_:
{
lean_object* v___x_5494_; 
if (v_isShared_5492_ == 0)
{
v___x_5494_ = v___x_5491_;
goto v_reusejp_5493_;
}
else
{
lean_object* v_reuseFailAlloc_5495_; 
v_reuseFailAlloc_5495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5495_, 0, v_a_5489_);
v___x_5494_ = v_reuseFailAlloc_5495_;
goto v_reusejp_5493_;
}
v_reusejp_5493_:
{
return v___x_5494_;
}
}
}
}
}
else
{
lean_object* v_a_5497_; lean_object* v___x_5499_; uint8_t v_isShared_5500_; uint8_t v_isSharedCheck_5504_; 
lean_dec_ref(v_b_5398_);
lean_dec_ref(v_a_5397_);
v_a_5497_ = lean_ctor_get(v___x_5411_, 0);
v_isSharedCheck_5504_ = !lean_is_exclusive(v___x_5411_);
if (v_isSharedCheck_5504_ == 0)
{
v___x_5499_ = v___x_5411_;
v_isShared_5500_ = v_isSharedCheck_5504_;
goto v_resetjp_5498_;
}
else
{
lean_inc(v_a_5497_);
lean_dec(v___x_5411_);
v___x_5499_ = lean_box(0);
v_isShared_5500_ = v_isSharedCheck_5504_;
goto v_resetjp_5498_;
}
v_resetjp_5498_:
{
lean_object* v___x_5502_; 
if (v_isShared_5500_ == 0)
{
v___x_5502_ = v___x_5499_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5503_; 
v_reuseFailAlloc_5503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5503_, 0, v_a_5497_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq___boxed(lean_object* v_a_5505_, lean_object* v_b_5506_, lean_object* v_a_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_, lean_object* v_a_5516_, lean_object* v_a_5517_, lean_object* v_a_5518_){
_start:
{
lean_object* v_res_5519_; 
v_res_5519_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5505_, v_b_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_);
lean_dec(v_a_5517_);
lean_dec_ref(v_a_5516_);
lean_dec(v_a_5515_);
lean_dec_ref(v_a_5514_);
lean_dec(v_a_5513_);
lean_dec_ref(v_a_5512_);
lean_dec(v_a_5511_);
lean_dec_ref(v_a_5510_);
lean_dec(v_a_5509_);
lean_dec(v_a_5508_);
lean_dec(v_a_5507_);
return v_res_5519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(lean_object* v_a_5520_, lean_object* v_b_5521_, lean_object* v_a_5522_, lean_object* v_a_5523_, lean_object* v_a_5524_, lean_object* v_a_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_, lean_object* v_a_5530_, lean_object* v_a_5531_){
_start:
{
lean_object* v___x_5533_; 
v___x_5533_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5520_, v_b_5521_, v_a_5522_, v_a_5530_);
if (lean_obj_tag(v___x_5533_) == 0)
{
lean_object* v_a_5534_; 
v_a_5534_ = lean_ctor_get(v___x_5533_, 0);
lean_inc(v_a_5534_);
lean_dec_ref_known(v___x_5533_, 1);
if (lean_obj_tag(v_a_5534_) == 1)
{
lean_object* v_val_5535_; lean_object* v___x_5536_; 
v_val_5535_ = lean_ctor_get(v_a_5534_, 0);
lean_inc(v_val_5535_);
lean_dec_ref_known(v_a_5534_, 1);
v___x_5536_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5535_, v_a_5522_, v_a_5523_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_);
if (lean_obj_tag(v___x_5536_) == 0)
{
lean_object* v_a_5537_; uint8_t v___x_5538_; 
v_a_5537_ = lean_ctor_get(v___x_5536_, 0);
lean_inc(v_a_5537_);
lean_dec_ref_known(v___x_5536_, 1);
v___x_5538_ = lean_unbox(v_a_5537_);
lean_dec(v_a_5537_);
if (v___x_5538_ == 0)
{
lean_object* v___x_5539_; 
v___x_5539_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5520_, v_b_5521_, v_val_5535_, v_a_5522_, v_a_5523_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_);
lean_dec(v_val_5535_);
return v___x_5539_;
}
else
{
lean_object* v___x_5540_; 
v___x_5540_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5520_, v_b_5521_, v_val_5535_, v_a_5522_, v_a_5523_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_);
lean_dec(v_val_5535_);
return v___x_5540_;
}
}
else
{
lean_object* v_a_5541_; lean_object* v___x_5543_; uint8_t v_isShared_5544_; uint8_t v_isSharedCheck_5548_; 
lean_dec(v_val_5535_);
lean_dec_ref(v_b_5521_);
lean_dec_ref(v_a_5520_);
v_a_5541_ = lean_ctor_get(v___x_5536_, 0);
v_isSharedCheck_5548_ = !lean_is_exclusive(v___x_5536_);
if (v_isSharedCheck_5548_ == 0)
{
v___x_5543_ = v___x_5536_;
v_isShared_5544_ = v_isSharedCheck_5548_;
goto v_resetjp_5542_;
}
else
{
lean_inc(v_a_5541_);
lean_dec(v___x_5536_);
v___x_5543_ = lean_box(0);
v_isShared_5544_ = v_isSharedCheck_5548_;
goto v_resetjp_5542_;
}
v_resetjp_5542_:
{
lean_object* v___x_5546_; 
if (v_isShared_5544_ == 0)
{
v___x_5546_ = v___x_5543_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_a_5541_);
v___x_5546_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
return v___x_5546_;
}
}
}
}
else
{
lean_object* v___x_5549_; 
lean_dec(v_a_5534_);
v___x_5549_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5520_, v_b_5521_, v_a_5522_, v_a_5530_);
if (lean_obj_tag(v___x_5549_) == 0)
{
lean_object* v_a_5550_; lean_object* v___x_5552_; uint8_t v_isShared_5553_; uint8_t v_isSharedCheck_5560_; 
v_a_5550_ = lean_ctor_get(v___x_5549_, 0);
v_isSharedCheck_5560_ = !lean_is_exclusive(v___x_5549_);
if (v_isSharedCheck_5560_ == 0)
{
v___x_5552_ = v___x_5549_;
v_isShared_5553_ = v_isSharedCheck_5560_;
goto v_resetjp_5551_;
}
else
{
lean_inc(v_a_5550_);
lean_dec(v___x_5549_);
v___x_5552_ = lean_box(0);
v_isShared_5553_ = v_isSharedCheck_5560_;
goto v_resetjp_5551_;
}
v_resetjp_5551_:
{
if (lean_obj_tag(v_a_5550_) == 1)
{
lean_object* v_val_5554_; lean_object* v___x_5555_; 
lean_del_object(v___x_5552_);
v_val_5554_ = lean_ctor_get(v_a_5550_, 0);
lean_inc(v_val_5554_);
lean_dec_ref_known(v_a_5550_, 1);
v___x_5555_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5520_, v_b_5521_, v_val_5554_, v_a_5522_, v_a_5523_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_);
lean_dec(v_val_5554_);
return v___x_5555_;
}
else
{
lean_object* v___x_5556_; lean_object* v___x_5558_; 
lean_dec(v_a_5550_);
lean_dec_ref(v_b_5521_);
lean_dec_ref(v_a_5520_);
v___x_5556_ = lean_box(0);
if (v_isShared_5553_ == 0)
{
lean_ctor_set(v___x_5552_, 0, v___x_5556_);
v___x_5558_ = v___x_5552_;
goto v_reusejp_5557_;
}
else
{
lean_object* v_reuseFailAlloc_5559_; 
v_reuseFailAlloc_5559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5559_, 0, v___x_5556_);
v___x_5558_ = v_reuseFailAlloc_5559_;
goto v_reusejp_5557_;
}
v_reusejp_5557_:
{
return v___x_5558_;
}
}
}
}
else
{
lean_object* v_a_5561_; lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5568_; 
lean_dec_ref(v_b_5521_);
lean_dec_ref(v_a_5520_);
v_a_5561_ = lean_ctor_get(v___x_5549_, 0);
v_isSharedCheck_5568_ = !lean_is_exclusive(v___x_5549_);
if (v_isSharedCheck_5568_ == 0)
{
v___x_5563_ = v___x_5549_;
v_isShared_5564_ = v_isSharedCheck_5568_;
goto v_resetjp_5562_;
}
else
{
lean_inc(v_a_5561_);
lean_dec(v___x_5549_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5568_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
lean_object* v___x_5566_; 
if (v_isShared_5564_ == 0)
{
v___x_5566_ = v___x_5563_;
goto v_reusejp_5565_;
}
else
{
lean_object* v_reuseFailAlloc_5567_; 
v_reuseFailAlloc_5567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5567_, 0, v_a_5561_);
v___x_5566_ = v_reuseFailAlloc_5567_;
goto v_reusejp_5565_;
}
v_reusejp_5565_:
{
return v___x_5566_;
}
}
}
}
}
else
{
lean_object* v_a_5569_; lean_object* v___x_5571_; uint8_t v_isShared_5572_; uint8_t v_isSharedCheck_5576_; 
lean_dec_ref(v_b_5521_);
lean_dec_ref(v_a_5520_);
v_a_5569_ = lean_ctor_get(v___x_5533_, 0);
v_isSharedCheck_5576_ = !lean_is_exclusive(v___x_5533_);
if (v_isSharedCheck_5576_ == 0)
{
v___x_5571_ = v___x_5533_;
v_isShared_5572_ = v_isSharedCheck_5576_;
goto v_resetjp_5570_;
}
else
{
lean_inc(v_a_5569_);
lean_dec(v___x_5533_);
v___x_5571_ = lean_box(0);
v_isShared_5572_ = v_isSharedCheck_5576_;
goto v_resetjp_5570_;
}
v_resetjp_5570_:
{
lean_object* v___x_5574_; 
if (v_isShared_5572_ == 0)
{
v___x_5574_ = v___x_5571_;
goto v_reusejp_5573_;
}
else
{
lean_object* v_reuseFailAlloc_5575_; 
v_reuseFailAlloc_5575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5575_, 0, v_a_5569_);
v___x_5574_ = v_reuseFailAlloc_5575_;
goto v_reusejp_5573_;
}
v_reusejp_5573_:
{
return v___x_5574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed(lean_object* v_a_5577_, lean_object* v_b_5578_, lean_object* v_a_5579_, lean_object* v_a_5580_, lean_object* v_a_5581_, lean_object* v_a_5582_, lean_object* v_a_5583_, lean_object* v_a_5584_, lean_object* v_a_5585_, lean_object* v_a_5586_, lean_object* v_a_5587_, lean_object* v_a_5588_, lean_object* v_a_5589_){
_start:
{
lean_object* v_res_5590_; 
v_res_5590_ = l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(v_a_5577_, v_b_5578_, v_a_5579_, v_a_5580_, v_a_5581_, v_a_5582_, v_a_5583_, v_a_5584_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_);
lean_dec(v_a_5588_);
lean_dec_ref(v_a_5587_);
lean_dec(v_a_5586_);
lean_dec_ref(v_a_5585_);
lean_dec(v_a_5584_);
lean_dec_ref(v_a_5583_);
lean_dec(v_a_5582_);
lean_dec_ref(v_a_5581_);
lean_dec(v_a_5580_);
lean_dec(v_a_5579_);
return v_res_5590_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
