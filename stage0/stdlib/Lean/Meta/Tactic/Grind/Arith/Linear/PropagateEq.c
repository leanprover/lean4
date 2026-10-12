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
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0(lean_object* v_k_3_, lean_object* v_x_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_3_ = stack[0].m_obj;
lean_object* v_x_4_ = stack[1].m_obj;
lean_object* v___y_5_ = stack[2].m_obj;
lean_object* v___y_6_ = stack[3].m_obj;
lean_object* v___y_7_ = stack[4].m_obj;
lean_object* v___y_8_ = stack[5].m_obj;
lean_object* v___y_9_ = stack[6].m_obj;
lean_object* v___y_10_ = stack[7].m_obj;
lean_object* v___y_11_ = stack[8].m_obj;
lean_object* v___y_12_ = stack[9].m_obj;
lean_object* v___y_13_ = stack[10].m_obj;
lean_object* v___y_14_ = stack[11].m_obj;
lean_object* v___y_15_ = stack[12].m_obj;
lean_object* v_res_82_;
v_res_82_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0(v_k_3_, v_x_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_);
stack->m_obj
 = v_res_82_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___boxed(lean_object* v_k_83_, lean_object* v_x_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0(v_k_83_, v_x_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec(v___y_87_);
lean_dec(v___y_86_);
lean_dec(v___y_85_);
lean_dec(v_x_84_);
lean_dec(v_k_83_);
return v_res_97_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__1(lean_object* v_p_98_, lean_object* v_acc_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
if (lean_obj_tag(v_p_98_) == 0)
{
lean_object* v___x_112_; 
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v_acc_99_);
return v___x_112_;
}
else
{
lean_object* v_k_113_; lean_object* v_v_114_; lean_object* v_p_115_; lean_object* v___x_116_; 
v_k_113_ = lean_ctor_get(v_p_98_, 0);
v_v_114_ = lean_ctor_get(v_p_98_, 1);
v_p_115_ = lean_ctor_get(v_p_98_, 2);
v___x_116_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_118_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref_known(v___x_116_, 1);
v___x_118_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0(v_k_113_, v_v_114_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v_a_119_; lean_object* v_addFn_120_; lean_object* v___x_121_; 
v_a_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_a_119_);
lean_dec_ref_known(v___x_118_, 1);
v_addFn_120_ = lean_ctor_get(v_a_117_, 22);
lean_inc_ref(v_addFn_120_);
lean_dec(v_a_117_);
v___x_121_ = l_Lean_mkAppB(v_addFn_120_, v_acc_99_, v_a_119_);
v_p_98_ = v_p_115_;
v_acc_99_ = v___x_121_;
goto _start;
}
else
{
lean_dec(v_a_117_);
lean_dec_ref(v_acc_99_);
return v___x_118_;
}
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec_ref(v_acc_99_);
v_a_123_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_116_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_116_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_98_ = stack[0].m_obj;
lean_object* v_acc_99_ = stack[1].m_obj;
lean_object* v___y_100_ = stack[2].m_obj;
lean_object* v___y_101_ = stack[3].m_obj;
lean_object* v___y_102_ = stack[4].m_obj;
lean_object* v___y_103_ = stack[5].m_obj;
lean_object* v___y_104_ = stack[6].m_obj;
lean_object* v___y_105_ = stack[7].m_obj;
lean_object* v___y_106_ = stack[8].m_obj;
lean_object* v___y_107_ = stack[9].m_obj;
lean_object* v___y_108_ = stack[10].m_obj;
lean_object* v___y_109_ = stack[11].m_obj;
lean_object* v___y_110_ = stack[12].m_obj;
lean_object* v_res_131_;
v_res_131_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__1(v_p_98_, v_acc_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
stack->m_obj
 = v_res_131_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__1___boxed(lean_object* v_p_132_, lean_object* v_acc_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__1(v_p_132_, v_acc_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec(v___y_135_);
lean_dec(v___y_134_);
lean_dec(v_p_132_);
return v_res_146_;
}
}
lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(lean_object* v_p_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
if (lean_obj_tag(v_p_147_) == 0)
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_169_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_169_ == 0)
{
v___x_163_ = v___x_160_;
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v_zero_165_; lean_object* v___x_167_; 
v_zero_165_ = lean_ctor_get(v_a_161_, 17);
lean_inc_ref(v_zero_165_);
lean_dec(v_a_161_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v_zero_165_);
v___x_167_ = v___x_163_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_zero_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
v_a_170_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_160_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_160_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
else
{
lean_object* v_k_178_; lean_object* v_v_179_; lean_object* v_p_180_; lean_object* v___x_181_; 
v_k_178_ = lean_ctor_get(v_p_147_, 0);
v_v_179_ = lean_ctor_get(v_p_147_, 1);
v_p_180_ = lean_ctor_get(v_p_147_, 2);
v___x_181_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0(v_k_178_, v_v_179_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_183_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref_known(v___x_181_, 1);
v___x_183_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__1(v_p_180_, v_a_182_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
return v___x_183_;
}
else
{
return v___x_181_;
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_147_ = stack[0].m_obj;
lean_object* v___y_148_ = stack[1].m_obj;
lean_object* v___y_149_ = stack[2].m_obj;
lean_object* v___y_150_ = stack[3].m_obj;
lean_object* v___y_151_ = stack[4].m_obj;
lean_object* v___y_152_ = stack[5].m_obj;
lean_object* v___y_153_ = stack[6].m_obj;
lean_object* v___y_154_ = stack[7].m_obj;
lean_object* v___y_155_ = stack[8].m_obj;
lean_object* v___y_156_ = stack[9].m_obj;
lean_object* v___y_157_ = stack[10].m_obj;
lean_object* v___y_158_ = stack[11].m_obj;
lean_object* v_res_184_;
v_res_184_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
stack->m_obj
 = v_res_184_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___boxed(lean_object* v_p_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec(v___y_187_);
lean_dec(v___y_186_);
lean_dec(v_p_185_);
return v_res_198_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3(lean_object* v_a_202_, lean_object* v_b_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_232_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_232_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_232_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_232_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_type_221_; lean_object* v_u_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
v_type_221_ = lean_ctor_get(v_a_217_, 2);
lean_inc_ref(v_type_221_);
v_u_222_ = lean_ctor_get(v_a_217_, 3);
lean_inc(v_u_222_);
lean_dec(v_a_217_);
v___x_223_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3___closed__1));
v___x_224_ = l_Lean_Level_succ___override(v_u_222_);
v___x_225_ = lean_box(0);
v___x_226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_224_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = l_Lean_mkConst(v___x_223_, v___x_226_);
v___x_228_ = l_Lean_mkApp3(v___x_227_, v_type_221_, v_a_202_, v_b_203_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_228_);
v___x_230_ = v___x_219_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec_ref(v_b_203_);
lean_dec_ref(v_a_202_);
v_a_233_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_216_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_216_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_202_ = stack[0].m_obj;
lean_object* v_b_203_ = stack[1].m_obj;
lean_object* v___y_204_ = stack[2].m_obj;
lean_object* v___y_205_ = stack[3].m_obj;
lean_object* v___y_206_ = stack[4].m_obj;
lean_object* v___y_207_ = stack[5].m_obj;
lean_object* v___y_208_ = stack[6].m_obj;
lean_object* v___y_209_ = stack[7].m_obj;
lean_object* v___y_210_ = stack[8].m_obj;
lean_object* v___y_211_ = stack[9].m_obj;
lean_object* v___y_212_ = stack[10].m_obj;
lean_object* v___y_213_ = stack[11].m_obj;
lean_object* v___y_214_ = stack[12].m_obj;
lean_object* v_res_241_;
v_res_241_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3(v_a_202_, v_b_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
stack->m_obj
 = v_res_241_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3___boxed(lean_object* v_a_242_, lean_object* v_b_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3(v_a_242_, v_b_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec(v___y_245_);
lean_dec(v___y_244_);
return v_res_256_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(lean_object* v_c_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v_p_270_; lean_object* v___x_271_; 
v_p_270_ = lean_ctor_get(v_c_257_, 0);
v___x_271_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_270_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v___x_273_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v___x_271_, 1);
v___x_273_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v_ofNatZero_275_; lean_object* v___x_276_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_274_);
lean_dec_ref_known(v___x_273_, 1);
v_ofNatZero_275_ = lean_ctor_get(v_a_274_, 18);
lean_inc_ref(v_ofNatZero_275_);
lean_dec(v_a_274_);
v___x_276_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3(v_a_272_, v_ofNatZero_275_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
return v___x_276_;
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_dec(v_a_272_);
v_a_277_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_273_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_273_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
else
{
return v___x_271_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_257_ = stack[0].m_obj;
lean_object* v___y_258_ = stack[1].m_obj;
lean_object* v___y_259_ = stack[2].m_obj;
lean_object* v___y_260_ = stack[3].m_obj;
lean_object* v___y_261_ = stack[4].m_obj;
lean_object* v___y_262_ = stack[5].m_obj;
lean_object* v___y_263_ = stack[6].m_obj;
lean_object* v___y_264_ = stack[7].m_obj;
lean_object* v___y_265_ = stack[8].m_obj;
lean_object* v___y_266_ = stack[9].m_obj;
lean_object* v___y_267_ = stack[10].m_obj;
lean_object* v___y_268_ = stack[11].m_obj;
lean_object* v_res_285_;
v_res_285_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
stack->m_obj
 = v_res_285_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1___boxed(lean_object* v_c_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v_c_286_);
return v_res_299_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(lean_object* v_msgData_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; lean_object* v_env_307_; uint8_t v___x_308_; lean_object* v_env_309_; lean_object* v___x_310_; lean_object* v_toCold_311_; lean_object* v_mctx_312_; lean_object* v_lctx_313_; lean_object* v_options_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_306_ = lean_st_ref_get(v___y_304_);
v_env_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc_ref(v_env_307_);
lean_dec(v___x_306_);
v___x_308_ = 0;
v_env_309_ = l_Lean_Environment_setRecordingDeps(v_env_307_, v___x_308_);
v___x_310_ = lean_st_ref_get(v___y_302_);
v_toCold_311_ = lean_ctor_get(v___y_303_, 0);
v_mctx_312_ = lean_ctor_get(v___x_310_, 0);
lean_inc_ref(v_mctx_312_);
lean_dec(v___x_310_);
v_lctx_313_ = lean_ctor_get(v___y_301_, 2);
v_options_314_ = lean_ctor_get(v_toCold_311_, 2);
lean_inc_ref(v_options_314_);
lean_inc_ref(v_lctx_313_);
v___x_315_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_315_, 0, v_env_309_);
lean_ctor_set(v___x_315_, 1, v_mctx_312_);
lean_ctor_set(v___x_315_, 2, v_lctx_313_);
lean_ctor_set(v___x_315_, 3, v_options_314_);
v___x_316_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v_msgData_300_);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_300_ = stack[0].m_obj;
lean_object* v___y_301_ = stack[1].m_obj;
lean_object* v___y_302_ = stack[2].m_obj;
lean_object* v___y_303_ = stack[3].m_obj;
lean_object* v___y_304_ = stack[4].m_obj;
lean_object* v_res_318_;
v_res_318_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msgData_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
stack->m_obj
 = v_res_318_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5___boxed(lean_object* v_msgData_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msgData_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
return v_res_325_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_326_; double v___x_327_; 
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = lean_float_of_nat(v___x_326_);
return v___x_327_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(lean_object* v_cls_331_, lean_object* v_msg_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_ref_338_; lean_object* v___x_339_; lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_385_; 
v_ref_338_ = lean_ctor_get(v___y_335_, 2);
v___x_339_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msg_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
v_a_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_385_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_385_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_385_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v_traceState_345_; lean_object* v_env_346_; lean_object* v_nextMacroScope_347_; lean_object* v_ngen_348_; lean_object* v_auxDeclNGen_349_; lean_object* v_cache_350_; lean_object* v_recordedDeps_351_; lean_object* v_messages_352_; lean_object* v_infoState_353_; lean_object* v_snapshotTasks_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_384_; 
v___x_344_ = lean_st_ref_take(v___y_336_);
v_traceState_345_ = lean_ctor_get(v___x_344_, 4);
v_env_346_ = lean_ctor_get(v___x_344_, 0);
v_nextMacroScope_347_ = lean_ctor_get(v___x_344_, 1);
v_ngen_348_ = lean_ctor_get(v___x_344_, 2);
v_auxDeclNGen_349_ = lean_ctor_get(v___x_344_, 3);
v_cache_350_ = lean_ctor_get(v___x_344_, 5);
v_recordedDeps_351_ = lean_ctor_get(v___x_344_, 6);
v_messages_352_ = lean_ctor_get(v___x_344_, 7);
v_infoState_353_ = lean_ctor_get(v___x_344_, 8);
v_snapshotTasks_354_ = lean_ctor_get(v___x_344_, 9);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_384_ == 0)
{
v___x_356_ = v___x_344_;
v_isShared_357_ = v_isSharedCheck_384_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_snapshotTasks_354_);
lean_inc(v_infoState_353_);
lean_inc(v_messages_352_);
lean_inc(v_recordedDeps_351_);
lean_inc(v_cache_350_);
lean_inc(v_traceState_345_);
lean_inc(v_auxDeclNGen_349_);
lean_inc(v_ngen_348_);
lean_inc(v_nextMacroScope_347_);
lean_inc(v_env_346_);
lean_dec(v___x_344_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_384_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
uint64_t v_tid_358_; lean_object* v_traces_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_383_; 
v_tid_358_ = lean_ctor_get_uint64(v_traceState_345_, sizeof(void*)*1);
v_traces_359_ = lean_ctor_get(v_traceState_345_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v_traceState_345_);
if (v_isSharedCheck_383_ == 0)
{
v___x_361_ = v_traceState_345_;
v_isShared_362_ = v_isSharedCheck_383_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_traces_359_);
lean_dec(v_traceState_345_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_383_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_364_; double v___x_365_; uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_363_ = lean_box(0);
v___x_364_ = lean_box(0);
v___x_365_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0);
v___x_366_ = 0;
v___x_367_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__1));
v___x_368_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_368_, 0, v_cls_331_);
lean_ctor_set(v___x_368_, 1, v___x_364_);
lean_ctor_set(v___x_368_, 2, v___x_367_);
lean_ctor_set_float(v___x_368_, sizeof(void*)*3, v___x_365_);
lean_ctor_set_float(v___x_368_, sizeof(void*)*3 + 8, v___x_365_);
lean_ctor_set_uint8(v___x_368_, sizeof(void*)*3 + 16, v___x_366_);
v___x_369_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__2));
v___x_370_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_370_, 0, v___x_368_);
lean_ctor_set(v___x_370_, 1, v_a_340_);
lean_ctor_set(v___x_370_, 2, v___x_369_);
lean_inc(v_ref_338_);
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v_ref_338_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v___x_372_ = l_Lean_PersistentArray_push___redArg(v_traces_359_, v___x_371_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_372_);
v___x_374_ = v___x_361_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_372_);
lean_ctor_set_uint64(v_reuseFailAlloc_382_, sizeof(void*)*1, v_tid_358_);
v___x_374_ = v_reuseFailAlloc_382_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_376_; 
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 4, v___x_374_);
v___x_376_ = v___x_356_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_env_346_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_nextMacroScope_347_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_ngen_348_);
lean_ctor_set(v_reuseFailAlloc_381_, 3, v_auxDeclNGen_349_);
lean_ctor_set(v_reuseFailAlloc_381_, 4, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_381_, 5, v_cache_350_);
lean_ctor_set(v_reuseFailAlloc_381_, 6, v_recordedDeps_351_);
lean_ctor_set(v_reuseFailAlloc_381_, 7, v_messages_352_);
lean_ctor_set(v_reuseFailAlloc_381_, 8, v_infoState_353_);
lean_ctor_set(v_reuseFailAlloc_381_, 9, v_snapshotTasks_354_);
v___x_376_ = v_reuseFailAlloc_381_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_377_ = lean_st_ref_put(v___y_336_, v___x_376_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___x_363_);
v___x_379_ = v___x_342_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_363_);
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
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_331_ = stack[0].m_obj;
lean_object* v_msg_332_ = stack[1].m_obj;
lean_object* v___y_333_ = stack[2].m_obj;
lean_object* v___y_334_ = stack[3].m_obj;
lean_object* v___y_335_ = stack[4].m_obj;
lean_object* v___y_336_ = stack[5].m_obj;
lean_object* v_res_386_;
v_res_386_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_331_, v_msg_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
stack->m_obj
 = v_res_386_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___boxed(lean_object* v_cls_387_, lean_object* v_msg_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_387_, v_msg_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
return v_res_394_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_407_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_409_ = l_Lean_Name_append(v___x_408_, v___x_407_);
return v___x_409_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8));
v___x_412_ = l_Lean_stringToMessageData(v___x_411_);
return v___x_412_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(lean_object* v_p_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_550_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_550_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_550_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_550_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
if (lean_obj_tag(v_a_427_) == 1)
{
lean_object* v_val_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_545_; 
v_val_431_ = lean_ctor_get(v_a_427_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v_a_427_);
if (v_isSharedCheck_545_ == 0)
{
v___x_433_ = v_a_427_;
v_isShared_434_ = v_isSharedCheck_545_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_val_431_);
lean_dec(v_a_427_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_545_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v_snd_435_; lean_object* v_snd_436_; lean_object* v_toCold_437_; lean_object* v_options_438_; lean_object* v_fst_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_543_; 
v_snd_435_ = lean_ctor_get(v_val_431_, 1);
lean_inc(v_snd_435_);
v_snd_436_ = lean_ctor_get(v_snd_435_, 1);
lean_inc(v_snd_436_);
v_toCold_437_ = lean_ctor_get(v_a_423_, 0);
v_options_438_ = lean_ctor_get(v_toCold_437_, 2);
v_fst_439_ = lean_ctor_get(v_val_431_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v_val_431_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; 
v_unused_544_ = lean_ctor_get(v_val_431_, 1);
lean_dec(v_unused_544_);
v___x_441_ = v_val_431_;
v_isShared_442_ = v_isSharedCheck_543_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_fst_439_);
lean_dec(v_val_431_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_543_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v_fst_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_541_; 
v_fst_443_ = lean_ctor_get(v_snd_435_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v_snd_435_);
if (v_isSharedCheck_541_ == 0)
{
lean_object* v_unused_542_; 
v_unused_542_ = lean_ctor_get(v_snd_435_, 1);
lean_dec(v_unused_542_);
v___x_445_ = v_snd_435_;
v_isShared_446_ = v_isSharedCheck_541_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_fst_443_);
lean_dec(v_snd_435_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_541_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v_p_447_; lean_object* v_inheritedTraceOptions_448_; uint8_t v_hasTrace_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v_p_447_ = lean_ctor_get(v_snd_436_, 0);
v_inheritedTraceOptions_448_ = lean_ctor_get(v_toCold_437_, 11);
v_hasTrace_449_ = lean_ctor_get_uint8(v_options_438_, sizeof(void*)*1);
v___x_450_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_447_, v_fst_443_);
lean_inc(v_p_413_);
v___x_451_ = l_Lean_Grind_Linarith_Poly_mul(v_p_413_, v___x_450_);
v___x_452_ = lean_int_neg(v_fst_439_);
lean_inc(v_p_447_);
v___x_453_ = l_Lean_Grind_Linarith_Poly_mul(v_p_447_, v___x_452_);
lean_dec(v___x_452_);
v___x_454_ = l_Lean_Grind_Linarith_Poly_combine(v___x_451_, v___x_453_);
if (v_hasTrace_449_ == 0)
{
lean_dec(v___x_450_);
lean_dec(v_fst_439_);
lean_dec(v_p_413_);
goto v___jp_455_;
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_468_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_469_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_470_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_448_, v_options_438_, v___x_469_);
if (v___x_470_ == 0)
{
lean_dec(v___x_450_);
lean_dec(v_fst_439_);
lean_dec(v_p_413_);
goto v___jp_455_;
}
else
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
lean_dec(v_p_413_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_473_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref_known(v___x_471_, 1);
v___x_473_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_443_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_475_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref_known(v___x_473_, 1);
v___x_475_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_436_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_477_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v___x_475_, 1);
v___x_477_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v___x_454_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_478_);
lean_dec_ref_known(v___x_477_, 1);
v___x_479_ = l_Lean_MessageData_ofExpr(v_a_472_);
v___x_480_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_479_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = l_Int_repr(v_fst_439_);
lean_dec(v_fst_439_);
v___x_483_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
v___x_484_ = l_Lean_MessageData_ofFormat(v___x_483_);
v___x_485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_481_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___x_480_);
v___x_487_ = l_Lean_MessageData_ofExpr(v_a_474_);
v___x_488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v___x_480_);
v___x_490_ = l_Lean_MessageData_ofExpr(v_a_476_);
v___x_491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_489_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v___x_480_);
v___x_493_ = l_Int_repr(v___x_450_);
lean_dec(v___x_450_);
v___x_494_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
v___x_495_ = l_Lean_MessageData_ofFormat(v___x_494_);
v___x_496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_492_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v___x_480_);
v___x_498_ = l_Lean_MessageData_ofExpr(v_a_478_);
v___x_499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_468_, v___x_499_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_dec_ref_known(v___x_500_, 1);
goto v___jp_455_;
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec(v___x_454_);
lean_del_object(v___x_445_);
lean_dec(v_fst_443_);
lean_del_object(v___x_441_);
lean_dec(v_snd_436_);
lean_del_object(v___x_433_);
lean_del_object(v___x_429_);
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec(v_a_476_);
lean_dec(v_a_474_);
lean_dec(v_a_472_);
lean_dec(v___x_454_);
lean_dec(v___x_450_);
lean_del_object(v___x_445_);
lean_dec(v_fst_443_);
lean_del_object(v___x_441_);
lean_dec(v_fst_439_);
lean_dec(v_snd_436_);
lean_del_object(v___x_433_);
lean_del_object(v___x_429_);
v_a_509_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_477_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_477_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec(v_a_474_);
lean_dec(v_a_472_);
lean_dec(v___x_454_);
lean_dec(v___x_450_);
lean_del_object(v___x_445_);
lean_dec(v_fst_443_);
lean_del_object(v___x_441_);
lean_dec(v_fst_439_);
lean_dec(v_snd_436_);
lean_del_object(v___x_433_);
lean_del_object(v___x_429_);
v_a_517_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_475_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_475_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_a_472_);
lean_dec(v___x_454_);
lean_dec(v___x_450_);
lean_del_object(v___x_445_);
lean_dec(v_fst_443_);
lean_del_object(v___x_441_);
lean_dec(v_fst_439_);
lean_dec(v_snd_436_);
lean_del_object(v___x_433_);
lean_del_object(v___x_429_);
v_a_525_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_473_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_473_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec(v___x_454_);
lean_dec(v___x_450_);
lean_del_object(v___x_445_);
lean_dec(v_fst_443_);
lean_del_object(v___x_441_);
lean_dec(v_fst_439_);
lean_dec(v_snd_436_);
lean_del_object(v___x_433_);
lean_del_object(v___x_429_);
v_a_533_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_471_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_471_);
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
}
v___jp_455_:
{
lean_object* v___x_457_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v___x_454_);
lean_ctor_set(v___x_445_, 0, v_snd_436_);
v___x_457_ = v___x_445_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_snd_436_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v___x_454_);
v___x_457_ = v_reuseFailAlloc_467_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v___x_457_);
lean_ctor_set(v___x_441_, 0, v_fst_443_);
v___x_459_ = v___x_441_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_fst_443_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_457_);
v___x_459_ = v_reuseFailAlloc_466_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_461_; 
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_459_);
v___x_461_ = v___x_433_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_465_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_463_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_461_);
v___x_463_ = v___x_429_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
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
lean_object* v___x_546_; lean_object* v___x_548_; 
lean_dec(v_a_427_);
lean_dec(v_p_413_);
v___x_546_ = lean_box(0);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_546_);
v___x_548_ = v___x_429_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_546_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
lean_dec(v_p_413_);
v_a_551_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_426_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_426_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_413_ = stack[0].m_obj;
lean_object* v_a_414_ = stack[1].m_obj;
lean_object* v_a_415_ = stack[2].m_obj;
lean_object* v_a_416_ = stack[3].m_obj;
lean_object* v_a_417_ = stack[4].m_obj;
lean_object* v_a_418_ = stack[5].m_obj;
lean_object* v_a_419_ = stack[6].m_obj;
lean_object* v_a_420_ = stack[7].m_obj;
lean_object* v_a_421_ = stack[8].m_obj;
lean_object* v_a_422_ = stack[9].m_obj;
lean_object* v_a_423_ = stack[10].m_obj;
lean_object* v_a_424_ = stack[11].m_obj;
lean_object* v_res_559_;
v_res_559_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
stack->m_obj
 = v_res_559_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___boxed(lean_object* v_p_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec(v_a_562_);
lean_dec(v_a_561_);
return v_res_573_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(lean_object* v_cls_574_, lean_object* v_msg_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_574_, v_msg_575_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
return v___x_588_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_574_ = stack[0].m_obj;
lean_object* v_msg_575_ = stack[1].m_obj;
lean_object* v___y_576_ = stack[2].m_obj;
lean_object* v___y_577_ = stack[3].m_obj;
lean_object* v___y_578_ = stack[4].m_obj;
lean_object* v___y_579_ = stack[5].m_obj;
lean_object* v___y_580_ = stack[6].m_obj;
lean_object* v___y_581_ = stack[7].m_obj;
lean_object* v___y_582_ = stack[8].m_obj;
lean_object* v___y_583_ = stack[9].m_obj;
lean_object* v___y_584_ = stack[10].m_obj;
lean_object* v___y_585_ = stack[11].m_obj;
lean_object* v___y_586_ = stack[12].m_obj;
lean_object* v_res_589_;
v_res_589_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_cls_574_, v_msg_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
stack->m_obj
 = v_res_589_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___boxed(lean_object* v_cls_590_, lean_object* v_msg_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_cls_590_, v_msg_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec(v___y_593_);
lean_dec(v___y_592_);
return v_res_604_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(lean_object* v_c_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_p_618_; lean_object* v___x_619_; 
v_p_618_ = lean_ctor_get(v_c_605_, 0);
v___x_619_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_618_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v___x_621_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_620_);
lean_dec_ref_known(v___x_619_, 1);
v___x_621_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v_ofNatZero_623_; lean_object* v___x_624_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v___x_621_, 1);
v_ofNatZero_623_ = lean_ctor_get(v_a_622_, 18);
lean_inc_ref(v_ofNatZero_623_);
lean_dec(v_a_622_);
v___x_624_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3(v_a_620_, v_ofNatZero_623_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_633_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_633_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_633_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_633_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_629_ = l_Lean_mkNot(v_a_625_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_629_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
else
{
return v___x_624_;
}
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_dec(v_a_620_);
v_a_634_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_621_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_621_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
else
{
return v___x_619_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_605_ = stack[0].m_obj;
lean_object* v___y_606_ = stack[1].m_obj;
lean_object* v___y_607_ = stack[2].m_obj;
lean_object* v___y_608_ = stack[3].m_obj;
lean_object* v___y_609_ = stack[4].m_obj;
lean_object* v___y_610_ = stack[5].m_obj;
lean_object* v___y_611_ = stack[6].m_obj;
lean_object* v___y_612_ = stack[7].m_obj;
lean_object* v___y_613_ = stack[8].m_obj;
lean_object* v___y_614_ = stack[9].m_obj;
lean_object* v___y_615_ = stack[10].m_obj;
lean_object* v___y_616_ = stack[11].m_obj;
lean_object* v_res_642_;
v_res_642_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
stack->m_obj
 = v_res_642_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0___boxed(lean_object* v_c_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v_c_643_);
return v_res_656_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_nat_to_int(v___x_657_);
return v___x_658_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2(void){
_start:
{
lean_object* v_cls_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_cls_663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_664_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_665_ = l_Lean_Name_append(v___x_664_, v_cls_663_);
return v___x_665_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(lean_object* v_a_666_, lean_object* v_x_667_, lean_object* v_c_u2081_668_, lean_object* v_b_669_, lean_object* v_c_u2082_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v_toCold_737_; lean_object* v_options_738_; uint8_t v_hasTrace_739_; 
v_toCold_737_ = lean_ctor_get(v_a_680_, 0);
v_options_738_ = lean_ctor_get(v_toCold_737_, 2);
v_hasTrace_739_ = lean_ctor_get_uint8(v_options_738_, sizeof(void*)*1);
if (v_hasTrace_739_ == 0)
{
v___y_684_ = v_a_671_;
v___y_685_ = v_a_672_;
v___y_686_ = v_a_673_;
v___y_687_ = v_a_674_;
v___y_688_ = v_a_675_;
v___y_689_ = v_a_676_;
v___y_690_ = v_a_677_;
v___y_691_ = v_a_678_;
v___y_692_ = v_a_679_;
v___y_693_ = v_a_680_;
v___y_694_ = v_a_681_;
goto v___jp_683_;
}
else
{
lean_object* v_inheritedTraceOptions_740_; lean_object* v_cls_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v_inheritedTraceOptions_740_ = lean_ctor_get(v_toCold_737_, 11);
v_cls_741_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_742_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2);
v___x_743_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_740_, v_options_738_, v___x_742_);
if (v___x_743_ == 0)
{
v___y_684_ = v_a_671_;
v___y_685_ = v_a_672_;
v___y_686_ = v_a_673_;
v___y_687_ = v_a_674_;
v___y_688_ = v_a_675_;
v___y_689_ = v_a_676_;
v___y_690_ = v_a_677_;
v___y_691_ = v_a_678_;
v___y_692_ = v_a_679_;
v___y_693_ = v_a_680_;
v___y_694_ = v_a_681_;
goto v___jp_683_;
}
else
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_667_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_746_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_744_, 1);
v___x_746_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_668_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_748_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v___x_748_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_u2082_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_748_, 1);
v___x_750_ = l_Lean_MessageData_ofExpr(v_a_745_);
v___x_751_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_750_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = l_Lean_MessageData_ofExpr(v_a_747_);
v___x_754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v___x_751_);
v___x_756_ = l_Lean_MessageData_ofExpr(v_a_749_);
v___x_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_755_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_741_, v___x_757_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_dec_ref_known(v___x_758_, 1);
v___y_684_ = v_a_671_;
v___y_685_ = v_a_672_;
v___y_686_ = v_a_673_;
v___y_687_ = v_a_674_;
v___y_688_ = v_a_675_;
v___y_689_ = v_a_676_;
v___y_690_ = v_a_677_;
v___y_691_ = v_a_678_;
v___y_692_ = v_a_679_;
v___y_693_ = v_a_680_;
v___y_694_ = v_a_681_;
goto v___jp_683_;
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec_ref(v_c_u2082_670_);
lean_dec(v_b_669_);
lean_dec_ref(v_c_u2081_668_);
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
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
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec(v_a_747_);
lean_dec(v_a_745_);
lean_dec_ref(v_c_u2082_670_);
lean_dec(v_b_669_);
lean_dec_ref(v_c_u2081_668_);
v_a_767_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_748_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_748_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec(v_a_745_);
lean_dec_ref(v_c_u2082_670_);
lean_dec(v_b_669_);
lean_dec_ref(v_c_u2081_668_);
v_a_775_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_746_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_746_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec_ref(v_c_u2082_670_);
lean_dec(v_b_669_);
lean_dec_ref(v_c_u2081_668_);
v_a_783_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_744_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_744_);
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
}
v___jp_683_:
{
lean_object* v_p_695_; lean_object* v_p_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_p_695_ = lean_ctor_get(v_c_u2081_668_, 0);
v_p_696_ = lean_ctor_get(v_c_u2082_670_, 0);
v___x_697_ = lean_int_emod(v_b_669_, v_a_666_);
v___x_698_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_699_ = lean_int_dec_eq(v___x_697_, v___x_698_);
lean_dec(v___x_697_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
v___x_700_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_720_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_720_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_720_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_720_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
uint8_t v___x_705_; 
v___x_705_ = lean_unbox(v_a_701_);
lean_dec(v_a_701_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_708_; 
lean_dec_ref(v_c_u2082_670_);
lean_dec(v_b_669_);
lean_dec_ref(v_c_u2081_668_);
v___x_706_ = lean_box(0);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_706_);
v___x_708_ = v___x_703_;
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
else
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_718_; 
lean_inc(v_p_695_);
v___x_710_ = l_Lean_Grind_Linarith_Poly_mul(v_p_695_, v_b_669_);
v___x_711_ = lean_int_neg(v_a_666_);
lean_inc(v_p_696_);
v___x_712_ = l_Lean_Grind_Linarith_Poly_mul(v_p_696_, v___x_711_);
v___x_713_ = l_Lean_Grind_Linarith_Poly_combine(v___x_710_, v___x_712_);
v___x_714_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_714_, 0, v___x_711_);
lean_ctor_set(v___x_714_, 1, v_b_669_);
lean_ctor_set(v___x_714_, 2, v_c_u2081_668_);
lean_ctor_set(v___x_714_, 3, v_c_u2082_670_);
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v___x_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_716_);
v___x_718_ = v___x_703_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec_ref(v_c_u2082_670_);
lean_dec(v_b_669_);
lean_dec_ref(v_c_u2081_668_);
v_a_721_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_700_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_700_);
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
else
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_729_ = lean_int_neg(v_b_669_);
lean_dec(v_b_669_);
v___x_730_ = lean_int_ediv(v___x_729_, v_a_666_);
lean_dec(v___x_729_);
lean_inc(v_p_695_);
v___x_731_ = l_Lean_Grind_Linarith_Poly_mul(v_p_695_, v___x_730_);
lean_inc(v_p_696_);
v___x_732_ = l_Lean_Grind_Linarith_Poly_combine(v___x_731_, v_p_696_);
v___x_733_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_733_, 0, v___x_730_);
lean_ctor_set(v___x_733_, 1, v_c_u2081_668_);
lean_ctor_set(v___x_733_, 2, v_c_u2082_670_);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_666_ = stack[0].m_obj;
lean_object* v_x_667_ = stack[1].m_obj;
lean_object* v_c_u2081_668_ = stack[2].m_obj;
lean_object* v_b_669_ = stack[3].m_obj;
lean_object* v_c_u2082_670_ = stack[4].m_obj;
lean_object* v_a_671_ = stack[5].m_obj;
lean_object* v_a_672_ = stack[6].m_obj;
lean_object* v_a_673_ = stack[7].m_obj;
lean_object* v_a_674_ = stack[8].m_obj;
lean_object* v_a_675_ = stack[9].m_obj;
lean_object* v_a_676_ = stack[10].m_obj;
lean_object* v_a_677_ = stack[11].m_obj;
lean_object* v_a_678_ = stack[12].m_obj;
lean_object* v_a_679_ = stack[13].m_obj;
lean_object* v_a_680_ = stack[14].m_obj;
lean_object* v_a_681_ = stack[15].m_obj;
lean_object* v_res_791_;
v_res_791_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_666_, v_x_667_, v_c_u2081_668_, v_b_669_, v_c_u2082_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
stack->m_obj
 = v_res_791_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___boxed(lean_object** _args){
lean_object* v_a_792_ = _args[0];
lean_object* v_x_793_ = _args[1];
lean_object* v_c_u2081_794_ = _args[2];
lean_object* v_b_795_ = _args[3];
lean_object* v_c_u2082_796_ = _args[4];
lean_object* v_a_797_ = _args[5];
lean_object* v_a_798_ = _args[6];
lean_object* v_a_799_ = _args[7];
lean_object* v_a_800_ = _args[8];
lean_object* v_a_801_ = _args[9];
lean_object* v_a_802_ = _args[10];
lean_object* v_a_803_ = _args[11];
lean_object* v_a_804_ = _args[12];
lean_object* v_a_805_ = _args[13];
lean_object* v_a_806_ = _args[14];
lean_object* v_a_807_ = _args[15];
lean_object* v_a_808_ = _args[16];
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_792_, v_x_793_, v_c_u2081_794_, v_b_795_, v_c_u2082_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec(v_a_798_);
lean_dec(v_a_797_);
lean_dec(v_x_793_);
lean_dec(v_a_792_);
return v_res_809_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(lean_object* v_a_810_, lean_object* v_b_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_a_810_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_844_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_844_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_844_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_844_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
if (lean_obj_tag(v_a_816_) == 1)
{
lean_object* v_val_820_; lean_object* v___x_821_; 
lean_del_object(v___x_818_);
v_val_820_ = lean_ctor_get(v_a_816_, 0);
v___x_821_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_b_811_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_839_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_839_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_839_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_839_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
if (lean_obj_tag(v_a_822_) == 1)
{
lean_object* v_val_826_; uint8_t v___x_827_; 
v_val_826_ = lean_ctor_get(v_a_822_, 0);
lean_inc(v_val_826_);
lean_dec_ref_known(v_a_822_, 1);
v___x_827_ = lean_nat_dec_eq(v_val_820_, v_val_826_);
lean_dec(v_val_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_830_; 
lean_dec_ref_known(v_a_816_, 1);
v___x_828_ = lean_box(0);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_828_);
v___x_830_ = v___x_824_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
else
{
lean_object* v___x_833_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v_a_816_);
v___x_833_ = v___x_824_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_816_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
else
{
lean_object* v___x_835_; lean_object* v___x_837_; 
lean_dec(v_a_822_);
lean_dec_ref_known(v_a_816_, 1);
v___x_835_ = lean_box(0);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_835_);
v___x_837_ = v___x_824_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_816_, 1);
return v___x_821_;
}
}
else
{
lean_object* v___x_840_; lean_object* v___x_842_; 
lean_dec(v_a_816_);
v___x_840_ = lean_box(0);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_840_);
v___x_842_ = v___x_818_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
return v___x_815_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_810_ = stack[0].m_obj;
lean_object* v_b_811_ = stack[1].m_obj;
lean_object* v_a_812_ = stack[2].m_obj;
lean_object* v_a_813_ = stack[3].m_obj;
lean_object* v_res_845_;
v_res_845_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_810_, v_b_811_, v_a_812_, v_a_813_);
stack->m_obj
 = v_res_845_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg___boxed(lean_object* v_a_846_, lean_object* v_b_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_846_, v_b_847_, v_a_848_, v_a_849_);
lean_dec_ref(v_a_849_);
lean_dec(v_a_848_);
lean_dec_ref(v_b_847_);
lean_dec_ref(v_a_846_);
return v_res_851_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(lean_object* v_a_852_, lean_object* v_b_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_852_, v_b_853_, v_a_854_, v_a_862_);
return v___x_865_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_852_ = stack[0].m_obj;
lean_object* v_b_853_ = stack[1].m_obj;
lean_object* v_a_854_ = stack[2].m_obj;
lean_object* v_a_855_ = stack[3].m_obj;
lean_object* v_a_856_ = stack[4].m_obj;
lean_object* v_a_857_ = stack[5].m_obj;
lean_object* v_a_858_ = stack[6].m_obj;
lean_object* v_a_859_ = stack[7].m_obj;
lean_object* v_a_860_ = stack[8].m_obj;
lean_object* v_a_861_ = stack[9].m_obj;
lean_object* v_a_862_ = stack[10].m_obj;
lean_object* v_a_863_ = stack[11].m_obj;
lean_object* v_res_866_;
v_res_866_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(v_a_852_, v_b_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_);
stack->m_obj
 = v_res_866_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___boxed(lean_object* v_a_867_, lean_object* v_b_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(v_a_867_, v_b_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
lean_dec(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_b_868_);
lean_dec_ref(v_a_867_);
return v_res_880_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_882_ = lean_int_neg(v___x_881_);
return v___x_882_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(lean_object* v_a_883_, lean_object* v_b_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
uint8_t v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_897_ = 0;
v___x_898_ = lean_box(v___x_897_);
lean_inc_ref(v_a_883_);
v___x_899_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 2);
lean_closure_set(v___x_899_, 0, v_a_883_);
lean_closure_set(v___x_899_, 1, v___x_898_);
v___x_900_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_899_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_1052_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_903_ = v___x_900_;
v_isShared_904_ = v_isSharedCheck_1052_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_1052_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
if (lean_obj_tag(v_a_901_) == 1)
{
lean_object* v_val_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
lean_del_object(v___x_903_);
v_val_905_ = lean_ctor_get(v_a_901_, 0);
lean_inc(v_val_905_);
lean_dec_ref_known(v_a_901_, 1);
v___x_906_ = lean_box(v___x_897_);
lean_inc_ref(v_b_884_);
v___x_907_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 2);
lean_closure_set(v___x_907_, 0, v_b_884_);
lean_closure_set(v___x_907_, 1, v___x_906_);
v___x_908_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_907_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_1039_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_1039_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_1039_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
if (lean_obj_tag(v_a_909_) == 1)
{
lean_object* v_val_913_; lean_object* v___x_914_; 
lean_del_object(v___x_911_);
v_val_913_ = lean_ctor_get(v_a_909_, 0);
lean_inc(v_val_913_);
lean_dec_ref_known(v_a_909_, 1);
v___x_914_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_883_, v_a_886_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_916_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_914_, 1);
v___x_916_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_884_, v_a_886_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___y_919_; uint8_t v___x_1018_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
v___x_1018_ = lean_nat_dec_le(v_a_915_, v_a_917_);
if (v___x_1018_ == 0)
{
lean_dec(v_a_917_);
v___y_919_ = v_a_915_;
goto v___jp_918_;
}
else
{
lean_dec(v_a_915_);
v___y_919_ = v_a_917_;
goto v___jp_918_;
}
v___jp_918_:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
lean_inc(v_val_913_);
lean_inc(v_val_905_);
v___x_920_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_920_, 0, v_val_905_);
lean_ctor_set(v___x_920_, 1, v_val_913_);
v___x_921_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_920_);
v___x_922_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_922_, 0, v_a_883_);
lean_ctor_set(v___x_922_, 1, v_b_884_);
lean_ctor_set(v___x_922_, 2, v_val_905_);
lean_ctor_set(v___x_922_, 3, v_val_913_);
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_921_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(v___x_923_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v_p_926_; lean_object* v___x_927_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref_known(v___x_924_, 1);
v_p_926_ = lean_ctor_get(v_a_925_, 0);
lean_inc(v___y_919_);
lean_inc_ref(v_p_926_);
v___x_927_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_926_, v___y_919_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_929_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v___x_927_, 1);
v___x_929_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_928_, v___x_897_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_993_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_993_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_993_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_993_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
if (lean_obj_tag(v_a_930_) == 1)
{
lean_object* v_val_934_; lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v_val_934_ = lean_ctor_get(v_a_930_, 0);
lean_inc_n(v_val_934_, 2);
lean_dec_ref_known(v_a_930_, 1);
v___x_935_ = l_Lean_Grind_Linarith_Expr_norm(v_val_934_);
v___x_936_ = lean_box(0);
v___x_937_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_935_, v___x_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
lean_del_object(v___x_932_);
lean_inc(v_a_925_);
v___x_938_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_938_, 0, v_a_925_);
lean_ctor_set(v___x_938_, 1, v_val_934_);
lean_inc(v___x_935_);
v___x_939_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_939_, 0, v___x_935_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
lean_ctor_set_uint8(v___x_939_, sizeof(void*)*2, v___x_897_);
v___x_940_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_939_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_983_; 
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; 
v_unused_984_ = lean_ctor_get(v___x_940_, 0);
lean_dec(v_unused_984_);
v___x_942_ = v___x_940_;
v_isShared_943_ = v_isSharedCheck_983_;
goto v_resetjp_941_;
}
else
{
lean_dec(v___x_940_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_983_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_944_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_926_);
v___x_945_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_944_, v_p_926_);
if (v_isShared_943_ == 0)
{
lean_ctor_set_tag(v___x_942_, 1);
lean_ctor_set(v___x_942_, 0, v_a_925_);
v___x_947_ = v___x_942_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_925_);
v___x_947_ = v_reuseFailAlloc_982_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
lean_inc_ref(v___x_945_);
v___x_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_945_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = l_Lean_Grind_Linarith_Poly_mul(v___x_935_, v___x_944_);
v___x_950_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v___x_945_, v___y_919_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_952_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
v___x_952_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_951_, v___x_897_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_965_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_965_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_965_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_965_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
if (lean_obj_tag(v_a_953_) == 1)
{
lean_object* v_val_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
lean_del_object(v___x_955_);
v_val_957_ = lean_ctor_get(v_a_953_, 0);
lean_inc(v_val_957_);
lean_dec_ref_known(v_a_953_, 1);
v___x_958_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_948_);
lean_ctor_set(v___x_958_, 1, v_val_957_);
v___x_959_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_959_, 0, v___x_949_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
lean_ctor_set_uint8(v___x_959_, sizeof(void*)*2, v___x_897_);
v___x_960_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_959_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
return v___x_960_;
}
else
{
lean_object* v___x_961_; lean_object* v___x_963_; 
lean_dec(v_a_953_);
lean_dec(v___x_949_);
lean_dec_ref_known(v___x_948_, 2);
v___x_961_ = lean_box(0);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_961_);
v___x_963_ = v___x_955_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec(v___x_949_);
lean_dec_ref_known(v___x_948_, 2);
v_a_966_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_952_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_952_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec(v___x_949_);
lean_dec_ref_known(v___x_948_, 2);
v_a_974_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_950_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_950_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
}
else
{
lean_dec(v___x_935_);
lean_dec(v_a_925_);
lean_dec(v___y_919_);
return v___x_940_;
}
}
else
{
lean_object* v___x_985_; lean_object* v___x_987_; 
lean_dec(v___x_935_);
lean_dec(v_val_934_);
lean_dec(v_a_925_);
lean_dec(v___y_919_);
v___x_985_ = lean_box(0);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_985_);
v___x_987_ = v___x_932_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
else
{
lean_object* v___x_989_; lean_object* v___x_991_; 
lean_dec(v_a_930_);
lean_dec(v_a_925_);
lean_dec(v___y_919_);
v___x_989_ = lean_box(0);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_989_);
v___x_991_ = v___x_932_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec(v_a_925_);
lean_dec(v___y_919_);
v_a_994_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_929_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_929_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec(v_a_925_);
lean_dec(v___y_919_);
v_a_1002_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_927_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_927_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v___y_919_);
v_a_1010_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_924_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_924_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v_a_915_);
lean_dec(v_val_913_);
lean_dec(v_val_905_);
lean_dec_ref(v_b_884_);
lean_dec_ref(v_a_883_);
v_a_1019_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_916_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_916_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
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
lean_dec(v_val_913_);
lean_dec(v_val_905_);
lean_dec_ref(v_b_884_);
lean_dec_ref(v_a_883_);
v_a_1027_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_914_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_914_);
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
lean_dec(v_a_909_);
lean_dec(v_val_905_);
lean_dec_ref(v_b_884_);
lean_dec_ref(v_a_883_);
v___x_1035_ = lean_box(0);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_1035_);
v___x_1037_ = v___x_911_;
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
lean_dec(v_val_905_);
lean_dec_ref(v_b_884_);
lean_dec_ref(v_a_883_);
v_a_1040_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_908_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_908_);
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
else
{
lean_object* v___x_1048_; lean_object* v___x_1050_; 
lean_dec(v_a_901_);
lean_dec_ref(v_b_884_);
lean_dec_ref(v_a_883_);
v___x_1048_ = lean_box(0);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_1048_);
v___x_1050_ = v___x_903_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
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
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec_ref(v_b_884_);
lean_dec_ref(v_a_883_);
v_a_1053_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_900_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_900_);
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_883_ = stack[0].m_obj;
lean_object* v_b_884_ = stack[1].m_obj;
lean_object* v_a_885_ = stack[2].m_obj;
lean_object* v_a_886_ = stack[3].m_obj;
lean_object* v_a_887_ = stack[4].m_obj;
lean_object* v_a_888_ = stack[5].m_obj;
lean_object* v_a_889_ = stack[6].m_obj;
lean_object* v_a_890_ = stack[7].m_obj;
lean_object* v_a_891_ = stack[8].m_obj;
lean_object* v_a_892_ = stack[9].m_obj;
lean_object* v_a_893_ = stack[10].m_obj;
lean_object* v_a_894_ = stack[11].m_obj;
lean_object* v_a_895_ = stack[12].m_obj;
lean_object* v_res_1061_;
v_res_1061_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_883_, v_b_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
stack->m_obj
 = v_res_1061_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___boxed(lean_object* v_a_1062_, lean_object* v_b_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_1062_, v_b_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec(v_a_1064_);
return v_res_1076_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(lean_object* v_a_1077_, lean_object* v_b_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
uint8_t v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = 0;
lean_inc_ref(v_a_1077_);
v___x_1092_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1077_, v___x_1091_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1137_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1137_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1137_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
if (lean_obj_tag(v_a_1093_) == 1)
{
lean_object* v_val_1097_; lean_object* v___x_1098_; 
lean_del_object(v___x_1095_);
v_val_1097_ = lean_ctor_get(v_a_1093_, 0);
lean_inc(v_val_1097_);
lean_dec_ref_known(v_a_1093_, 1);
lean_inc_ref(v_b_1078_);
v___x_1098_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_1078_, v___x_1091_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1124_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1124_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1124_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
if (lean_obj_tag(v_a_1099_) == 1)
{
lean_object* v_val_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v_val_1103_ = lean_ctor_get(v_a_1099_, 0);
lean_inc_n(v_val_1103_, 2);
lean_dec_ref_known(v_a_1099_, 1);
lean_inc(v_val_1097_);
v___x_1104_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1104_, 0, v_val_1097_);
lean_ctor_set(v___x_1104_, 1, v_val_1103_);
v___x_1105_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1104_);
v___x_1106_ = lean_box(0);
v___x_1107_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_1105_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
lean_del_object(v___x_1101_);
lean_inc(v_val_1103_);
lean_inc(v_val_1097_);
lean_inc_ref(v_b_1078_);
lean_inc_ref(v_a_1077_);
v___x_1108_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1108_, 0, v_a_1077_);
lean_ctor_set(v___x_1108_, 1, v_b_1078_);
lean_ctor_set(v___x_1108_, 2, v_val_1097_);
lean_ctor_set(v___x_1108_, 3, v_val_1103_);
lean_inc(v___x_1105_);
v___x_1109_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1109_, 0, v___x_1105_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
lean_ctor_set_uint8(v___x_1109_, sizeof(void*)*2, v___x_1091_);
v___x_1110_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1109_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec_ref_known(v___x_1110_, 1);
v___x_1111_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_1112_ = l_Lean_Grind_Linarith_Poly_mul(v___x_1105_, v___x_1111_);
v___x_1113_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1113_, 0, v_b_1078_);
lean_ctor_set(v___x_1113_, 1, v_a_1077_);
lean_ctor_set(v___x_1113_, 2, v_val_1103_);
lean_ctor_set(v___x_1113_, 3, v_val_1097_);
v___x_1114_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
lean_ctor_set_uint8(v___x_1114_, sizeof(void*)*2, v___x_1091_);
v___x_1115_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1114_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
return v___x_1115_;
}
else
{
lean_dec(v___x_1105_);
lean_dec(v_val_1103_);
lean_dec(v_val_1097_);
lean_dec_ref(v_b_1078_);
lean_dec_ref(v_a_1077_);
return v___x_1110_;
}
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1118_; 
lean_dec(v___x_1105_);
lean_dec(v_val_1103_);
lean_dec(v_val_1097_);
lean_dec_ref(v_b_1078_);
lean_dec_ref(v_a_1077_);
v___x_1116_ = lean_box(0);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1116_);
v___x_1118_ = v___x_1101_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1122_; 
lean_dec(v_a_1099_);
lean_dec(v_val_1097_);
lean_dec_ref(v_b_1078_);
lean_dec_ref(v_a_1077_);
v___x_1120_ = lean_box(0);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1120_);
v___x_1122_ = v___x_1101_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec(v_val_1097_);
lean_dec_ref(v_b_1078_);
lean_dec_ref(v_a_1077_);
v_a_1125_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1098_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1098_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
lean_dec(v_a_1093_);
lean_dec_ref(v_b_1078_);
lean_dec_ref(v_a_1077_);
v___x_1133_ = lean_box(0);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1133_);
v___x_1135_ = v___x_1095_;
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
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec_ref(v_b_1078_);
lean_dec_ref(v_a_1077_);
v_a_1138_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1092_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1092_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1077_ = stack[0].m_obj;
lean_object* v_b_1078_ = stack[1].m_obj;
lean_object* v_a_1079_ = stack[2].m_obj;
lean_object* v_a_1080_ = stack[3].m_obj;
lean_object* v_a_1081_ = stack[4].m_obj;
lean_object* v_a_1082_ = stack[5].m_obj;
lean_object* v_a_1083_ = stack[6].m_obj;
lean_object* v_a_1084_ = stack[7].m_obj;
lean_object* v_a_1085_ = stack[8].m_obj;
lean_object* v_a_1086_ = stack[9].m_obj;
lean_object* v_a_1087_ = stack[10].m_obj;
lean_object* v_a_1088_ = stack[11].m_obj;
lean_object* v_a_1089_ = stack[12].m_obj;
lean_object* v_res_1146_;
v_res_1146_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_1077_, v_b_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
stack->m_obj
 = v_res_1146_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27___boxed(lean_object* v_a_1147_, lean_object* v_b_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_1147_, v_b_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec(v_a_1149_);
return v_res_1161_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_1162_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(lean_object* v_msg_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v___x_1176_; lean_object* v___f_1177_; lean_object* v___x_2795__overap_1178_; lean_object* v___x_1179_; 
v___x_1176_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0);
v___f_1177_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1177_, 0, v___x_1176_);
v___x_2795__overap_1178_ = lean_panic_fn_borrowed(v___f_1177_, v_msg_1163_);
lean_dec_ref(v___f_1177_);
lean_inc(v___y_1174_);
lean_inc_ref(v___y_1173_);
lean_inc(v___y_1172_);
lean_inc_ref(v___y_1171_);
lean_inc(v___y_1170_);
lean_inc_ref(v___y_1169_);
lean_inc(v___y_1168_);
lean_inc_ref(v___y_1167_);
lean_inc(v___y_1166_);
lean_inc(v___y_1165_);
lean_inc(v___y_1164_);
v___x_1179_ = lean_apply_12(v___x_2795__overap_1178_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, lean_box(0));
return v___x_1179_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1163_ = stack[0].m_obj;
lean_object* v___y_1164_ = stack[1].m_obj;
lean_object* v___y_1165_ = stack[2].m_obj;
lean_object* v___y_1166_ = stack[3].m_obj;
lean_object* v___y_1167_ = stack[4].m_obj;
lean_object* v___y_1168_ = stack[5].m_obj;
lean_object* v___y_1169_ = stack[6].m_obj;
lean_object* v___y_1170_ = stack[7].m_obj;
lean_object* v___y_1171_ = stack[8].m_obj;
lean_object* v___y_1172_ = stack[9].m_obj;
lean_object* v___y_1173_ = stack[10].m_obj;
lean_object* v___y_1174_ = stack[11].m_obj;
lean_object* v_res_1180_;
v_res_1180_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v_msg_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
stack->m_obj
 = v_res_1180_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___boxed(lean_object* v_msg_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v_msg_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec(v___y_1182_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__1(lean_object* v_a_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_nat_to_int(v_a_1195_);
return v___x_1196_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2));
v___x_1201_ = lean_unsigned_to_nat(42u);
v___x_1202_ = lean_unsigned_to_nat(87u);
v___x_1203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1));
v___x_1204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0));
v___x_1205_ = l_mkPanicMessageWithDecl(v___x_1204_, v___x_1203_, v___x_1202_, v___x_1201_, v___x_1200_);
return v___x_1205_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(lean_object* v_c_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v_c_1222_; lean_object* v_c_1228_; lean_object* v_p_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; uint8_t v___x_1267_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1265_, 1);
v___x_1267_ = lean_unbox(v_a_1266_);
lean_dec(v_a_1266_);
if (v___x_1267_ == 0)
{
lean_object* v_p_1268_; 
v_p_1268_ = lean_ctor_get(v_c_1206_, 0);
lean_inc(v_p_1268_);
v_c_1228_ = v_c_1206_;
v_p_1229_ = v_p_1268_;
v___y_1230_ = v_a_1207_;
v___y_1231_ = v_a_1208_;
v___y_1232_ = v_a_1209_;
v___y_1233_ = v_a_1210_;
v___y_1234_ = v_a_1211_;
v___y_1235_ = v_a_1212_;
v___y_1236_ = v_a_1213_;
v___y_1237_ = v_a_1214_;
v___y_1238_ = v_a_1215_;
v___y_1239_ = v_a_1216_;
v___y_1240_ = v_a_1217_;
goto v___jp_1227_;
}
else
{
lean_object* v_p_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v_p_1269_ = lean_ctor_get(v_c_1206_, 0);
v___x_1270_ = l_Lean_Grind_Linarith_Poly_gcdCoeffs(v_p_1269_);
v___x_1271_ = lean_unsigned_to_nat(1u);
v___x_1272_ = lean_nat_dec_eq(v___x_1270_, v___x_1271_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_inc(v___x_1270_);
v___x_1273_ = lean_nat_to_int(v___x_1270_);
lean_inc(v_p_1269_);
v___x_1274_ = l_Lean_Grind_Linarith_Poly_div(v_p_1269_, v___x_1273_);
lean_dec(v___x_1273_);
v___x_1275_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1270_);
lean_ctor_set(v___x_1275_, 1, v_c_1206_);
lean_inc(v___x_1274_);
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1274_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v_c_1228_ = v___x_1276_;
v_p_1229_ = v___x_1274_;
v___y_1230_ = v_a_1207_;
v___y_1231_ = v_a_1208_;
v___y_1232_ = v_a_1209_;
v___y_1233_ = v_a_1210_;
v___y_1234_ = v_a_1211_;
v___y_1235_ = v_a_1212_;
v___y_1236_ = v_a_1213_;
v___y_1237_ = v_a_1214_;
v___y_1238_ = v_a_1215_;
v___y_1239_ = v_a_1216_;
v___y_1240_ = v_a_1217_;
goto v___jp_1227_;
}
else
{
lean_inc(v_p_1269_);
lean_dec(v___x_1270_);
v_c_1228_ = v_c_1206_;
v_p_1229_ = v_p_1269_;
v___y_1230_ = v_a_1207_;
v___y_1231_ = v_a_1208_;
v___y_1232_ = v_a_1209_;
v___y_1233_ = v_a_1210_;
v___y_1234_ = v_a_1211_;
v___y_1235_ = v_a_1212_;
v___y_1236_ = v_a_1213_;
v___y_1237_ = v_a_1214_;
v___y_1238_ = v_a_1215_;
v___y_1239_ = v_a_1216_;
v___y_1240_ = v_a_1217_;
goto v___jp_1227_;
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec_ref(v_c_1206_);
v_a_1277_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1265_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1265_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
v___jp_1219_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1223_ = lean_nat_abs(v___y_1220_);
lean_dec(v___y_1220_);
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___y_1221_);
lean_ctor_set(v___x_1224_, 1, v_c_1222_);
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1223_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
v___jp_1227_:
{
lean_object* v___x_1241_; 
lean_inc(v_p_1229_);
v___x_1241_ = l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(v_p_1229_);
if (lean_obj_tag(v___x_1241_) == 1)
{
lean_object* v_val_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1262_; 
v_val_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1262_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_val_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1262_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v_fst_1246_; lean_object* v_snd_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1261_; 
v_fst_1246_ = lean_ctor_get(v_val_1242_, 0);
v_snd_1247_ = lean_ctor_get(v_val_1242_, 1);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_val_1242_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1249_ = v_val_1242_;
v_isShared_1250_ = v_isSharedCheck_1261_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_snd_1247_);
lean_inc(v_fst_1246_);
lean_dec(v_val_1242_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1261_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_1252_ = lean_int_dec_lt(v_fst_1246_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_del_object(v___x_1249_);
lean_del_object(v___x_1244_);
lean_dec(v_p_1229_);
v___y_1220_ = v_fst_1246_;
v___y_1221_ = v_snd_1247_;
v_c_1222_ = v_c_1228_;
goto v___jp_1219_;
}
else
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1253_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_1254_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1229_, v___x_1253_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set_tag(v___x_1244_, 3);
lean_ctor_set(v___x_1244_, 0, v_c_1228_);
v___x_1256_ = v___x_1244_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_c_1228_);
v___x_1256_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1258_; 
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 1, v___x_1256_);
lean_ctor_set(v___x_1249_, 0, v___x_1254_);
v___x_1258_ = v___x_1249_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
v___y_1220_ = v_fst_1246_;
v___y_1221_ = v_snd_1247_;
v_c_1222_ = v___x_1258_;
goto v___jp_1219_;
}
}
}
}
}
}
else
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec(v___x_1241_);
lean_dec(v_p_1229_);
lean_dec_ref(v_c_1228_);
v___x_1263_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3);
v___x_1264_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v___x_1263_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
return v___x_1264_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1206_ = stack[0].m_obj;
lean_object* v_a_1207_ = stack[1].m_obj;
lean_object* v_a_1208_ = stack[2].m_obj;
lean_object* v_a_1209_ = stack[3].m_obj;
lean_object* v_a_1210_ = stack[4].m_obj;
lean_object* v_a_1211_ = stack[5].m_obj;
lean_object* v_a_1212_ = stack[6].m_obj;
lean_object* v_a_1213_ = stack[7].m_obj;
lean_object* v_a_1214_ = stack[8].m_obj;
lean_object* v_a_1215_ = stack[9].m_obj;
lean_object* v_a_1216_ = stack[10].m_obj;
lean_object* v_a_1217_ = stack[11].m_obj;
lean_object* v_res_1285_;
v_res_1285_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_c_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
stack->m_obj
 = v_res_1285_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___boxed(lean_object* v_c_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_c_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
lean_dec(v_a_1289_);
lean_dec(v_a_1288_);
lean_dec(v_a_1287_);
return v_res_1299_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = l_Lean_maxRecDepthErrorMessage;
v___x_1306_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
return v___x_1306_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_1308_ = l_Lean_MessageData_ofFormat(v___x_1307_);
return v___x_1308_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_1310_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_1311_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v___x_1309_);
return v___x_1311_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_1312_){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1314_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1315_, 0, v_ref_1312_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1312_ = stack[0].m_obj;
lean_object* v_res_1317_;
v_res_1317_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1312_);
stack->m_obj
 = v_res_1317_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1318_);
return v_res_1320_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_1321_, lean_object* v_ref_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1322_);
return v___x_1335_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1322_ = stack[1].m_obj;
lean_object* v___y_1323_ = stack[2].m_obj;
lean_object* v___y_1324_ = stack[3].m_obj;
lean_object* v___y_1325_ = stack[4].m_obj;
lean_object* v___y_1326_ = stack[5].m_obj;
lean_object* v___y_1327_ = stack[6].m_obj;
lean_object* v___y_1328_ = stack[7].m_obj;
lean_object* v___y_1329_ = stack[8].m_obj;
lean_object* v___y_1330_ = stack[9].m_obj;
lean_object* v___y_1331_ = stack[10].m_obj;
lean_object* v___y_1332_ = stack[11].m_obj;
lean_object* v___y_1333_ = stack[12].m_obj;
lean_object* v_res_1336_;
v_res_1336_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(lean_box(0), v_ref_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
stack->m_obj
 = v_res_1336_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_1337_, lean_object* v_ref_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(v_00_u03b1_1337_, v_ref_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec(v___y_1339_);
return v_res_1351_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(lean_object* v_c_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v_toCold_1383_; lean_object* v_p_1384_; lean_object* v_currRecDepth_1385_; lean_object* v_ref_1386_; uint16_t v_optionFlags_1387_; uint8_t v_suppressElabErrors_1388_; uint8_t v_isRecordingDeps_1389_; lean_object* v_options_1390_; lean_object* v_maxRecDepth_1391_; lean_object* v_inheritedTraceOptions_1392_; lean_object* v___x_1486_; uint8_t v___x_1487_; 
v_toCold_1383_ = lean_ctor_get(v_a_1362_, 0);
lean_inc_ref(v_toCold_1383_);
v_p_1384_ = lean_ctor_get(v_c_1352_, 0);
v_currRecDepth_1385_ = lean_ctor_get(v_a_1362_, 1);
lean_inc(v_currRecDepth_1385_);
v_ref_1386_ = lean_ctor_get(v_a_1362_, 2);
lean_inc(v_ref_1386_);
v_optionFlags_1387_ = lean_ctor_get_uint16(v_a_1362_, sizeof(void*)*3);
v_suppressElabErrors_1388_ = lean_ctor_get_uint8(v_a_1362_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1389_ = lean_ctor_get_uint8(v_a_1362_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_1362_);
v_options_1390_ = lean_ctor_get(v_toCold_1383_, 2);
lean_inc_ref(v_options_1390_);
v_maxRecDepth_1391_ = lean_ctor_get(v_toCold_1383_, 3);
v_inheritedTraceOptions_1392_ = lean_ctor_get(v_toCold_1383_, 11);
lean_inc_ref(v_inheritedTraceOptions_1392_);
v___x_1486_ = lean_unsigned_to_nat(0u);
v___x_1487_ = lean_nat_dec_eq(v_maxRecDepth_1391_, v___x_1486_);
if (v___x_1487_ == 0)
{
uint8_t v___x_1488_; 
v___x_1488_ = lean_nat_dec_eq(v_currRecDepth_1385_, v_maxRecDepth_1391_);
if (v___x_1488_ == 0)
{
goto v___jp_1393_;
}
else
{
lean_object* v___x_1489_; 
lean_dec_ref(v_inheritedTraceOptions_1392_);
lean_dec_ref(v_options_1390_);
lean_dec(v_currRecDepth_1385_);
lean_dec_ref(v_toCold_1383_);
lean_dec_ref(v_c_1352_);
v___x_1489_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1386_);
return v___x_1489_;
}
}
else
{
goto v___jp_1393_;
}
v___jp_1365_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_1380_, 0, v___y_1368_);
lean_ctor_set(v___x_1380_, 1, v___y_1366_);
lean_ctor_set(v___x_1380_, 2, v_c_1352_);
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___y_1367_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v_c_1352_ = v___x_1381_;
v_a_1353_ = v___y_1369_;
v_a_1354_ = v___y_1370_;
v_a_1355_ = v___y_1371_;
v_a_1356_ = v___y_1372_;
v_a_1357_ = v___y_1373_;
v_a_1358_ = v___y_1374_;
v_a_1359_ = v___y_1375_;
v_a_1360_ = v___y_1376_;
v_a_1361_ = v___y_1377_;
v_a_1362_ = v___y_1378_;
v_a_1363_ = v___y_1379_;
goto _start;
}
v___jp_1393_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1394_ = lean_unsigned_to_nat(1u);
v___x_1395_ = lean_nat_add(v_currRecDepth_1385_, v___x_1394_);
lean_dec(v_currRecDepth_1385_);
v___x_1396_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1396_, 0, v_toCold_1383_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
lean_ctor_set(v___x_1396_, 2, v_ref_1386_);
lean_ctor_set_uint16(v___x_1396_, sizeof(void*)*3, v_optionFlags_1387_);
lean_ctor_set_uint8(v___x_1396_, sizeof(void*)*3 + 2, v_suppressElabErrors_1388_);
lean_ctor_set_uint8(v___x_1396_, sizeof(void*)*3 + 3, v_isRecordingDeps_1389_);
lean_inc(v_p_1384_);
v___x_1397_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_1384_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v___x_1396_, v_a_1363_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1477_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1477_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1477_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
if (lean_obj_tag(v_a_1398_) == 1)
{
lean_object* v_val_1402_; lean_object* v_snd_1403_; uint8_t v_hasTrace_1404_; 
lean_del_object(v___x_1400_);
v_val_1402_ = lean_ctor_get(v_a_1398_, 0);
lean_inc(v_val_1402_);
lean_dec_ref_known(v_a_1398_, 1);
v_snd_1403_ = lean_ctor_get(v_val_1402_, 1);
lean_inc(v_snd_1403_);
v_hasTrace_1404_ = lean_ctor_get_uint8(v_options_1390_, sizeof(void*)*1);
if (v_hasTrace_1404_ == 0)
{
lean_object* v_fst_1405_; lean_object* v_fst_1406_; lean_object* v_snd_1407_; 
lean_dec_ref(v_inheritedTraceOptions_1392_);
lean_dec_ref(v_options_1390_);
v_fst_1405_ = lean_ctor_get(v_val_1402_, 0);
lean_inc(v_fst_1405_);
lean_dec(v_val_1402_);
v_fst_1406_ = lean_ctor_get(v_snd_1403_, 0);
lean_inc(v_fst_1406_);
v_snd_1407_ = lean_ctor_get(v_snd_1403_, 1);
lean_inc(v_snd_1407_);
lean_dec(v_snd_1403_);
v___y_1366_ = v_fst_1406_;
v___y_1367_ = v_snd_1407_;
v___y_1368_ = v_fst_1405_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v_a_1359_;
v___y_1376_ = v_a_1360_;
v___y_1377_ = v_a_1361_;
v___y_1378_ = v___x_1396_;
v___y_1379_ = v_a_1363_;
goto v___jp_1365_;
}
else
{
lean_object* v_fst_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1472_; 
v_fst_1408_ = lean_ctor_get(v_val_1402_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_val_1402_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; 
v_unused_1473_ = lean_ctor_get(v_val_1402_, 1);
lean_dec(v_unused_1473_);
v___x_1410_ = v_val_1402_;
v_isShared_1411_ = v_isSharedCheck_1472_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_fst_1408_);
lean_dec(v_val_1402_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1472_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v_fst_1412_; lean_object* v_snd_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1471_; 
v_fst_1412_ = lean_ctor_get(v_snd_1403_, 0);
v_snd_1413_ = lean_ctor_get(v_snd_1403_, 1);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_snd_1403_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1415_ = v_snd_1403_;
v_isShared_1416_ = v_isSharedCheck_1471_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_snd_1413_);
lean_inc(v_fst_1412_);
lean_dec(v_snd_1403_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1471_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_1418_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_1419_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1392_, v_options_1390_, v___x_1418_);
lean_dec_ref(v_options_1390_);
lean_dec_ref(v_inheritedTraceOptions_1392_);
if (v___x_1419_ == 0)
{
lean_del_object(v___x_1415_);
lean_del_object(v___x_1410_);
v___y_1366_ = v_fst_1412_;
v___y_1367_ = v_snd_1413_;
v___y_1368_ = v_fst_1408_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v_a_1359_;
v___y_1376_ = v_a_1360_;
v___y_1377_ = v_a_1361_;
v___y_1378_ = v___x_1396_;
v___y_1379_ = v_a_1363_;
goto v___jp_1365_;
}
else
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_1408_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v___x_1396_, v_a_1363_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1422_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v___x_1396_, v_a_1363_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1424_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
v___x_1424_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_fst_1412_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v___x_1396_, v_a_1363_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v___x_1426_ = l_Lean_MessageData_ofExpr(v_a_1421_);
v___x_1427_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_1416_ == 0)
{
lean_ctor_set_tag(v___x_1415_, 7);
lean_ctor_set(v___x_1415_, 1, v___x_1427_);
lean_ctor_set(v___x_1415_, 0, v___x_1426_);
v___x_1429_ = v___x_1415_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1430_ = l_Lean_MessageData_ofExpr(v_a_1423_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set_tag(v___x_1410_, 7);
lean_ctor_set(v___x_1410_, 1, v___x_1430_);
lean_ctor_set(v___x_1410_, 0, v___x_1429_);
v___x_1432_ = v___x_1410_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
lean_ctor_set(v___x_1433_, 1, v___x_1427_);
v___x_1434_ = l_Lean_MessageData_ofExpr(v_a_1425_);
v___x_1435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_1417_, v___x_1435_, v_a_1360_, v_a_1361_, v___x_1396_, v_a_1363_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_dec_ref_known(v___x_1436_, 1);
v___y_1366_ = v_fst_1412_;
v___y_1367_ = v_snd_1413_;
v___y_1368_ = v_fst_1408_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v_a_1359_;
v___y_1376_ = v_a_1360_;
v___y_1377_ = v_a_1361_;
v___y_1378_ = v___x_1396_;
v___y_1379_ = v_a_1363_;
goto v___jp_1365_;
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec(v_snd_1413_);
lean_dec(v_fst_1412_);
lean_dec(v_fst_1408_);
lean_dec_ref_known(v___x_1396_, 3);
lean_dec_ref(v_c_1352_);
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v_a_1423_);
lean_dec(v_a_1421_);
lean_del_object(v___x_1415_);
lean_dec(v_snd_1413_);
lean_dec(v_fst_1412_);
lean_del_object(v___x_1410_);
lean_dec(v_fst_1408_);
lean_dec_ref_known(v___x_1396_, 3);
lean_dec_ref(v_c_1352_);
v_a_1447_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1424_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1424_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec(v_a_1421_);
lean_del_object(v___x_1415_);
lean_dec(v_snd_1413_);
lean_dec(v_fst_1412_);
lean_del_object(v___x_1410_);
lean_dec(v_fst_1408_);
lean_dec_ref_known(v___x_1396_, 3);
lean_dec_ref(v_c_1352_);
v_a_1455_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1422_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1422_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_del_object(v___x_1415_);
lean_dec(v_snd_1413_);
lean_dec(v_fst_1412_);
lean_del_object(v___x_1410_);
lean_dec(v_fst_1408_);
lean_dec_ref_known(v___x_1396_, 3);
lean_dec_ref(v_c_1352_);
v_a_1463_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1420_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1420_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
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
lean_object* v___x_1475_; 
lean_dec(v_a_1398_);
lean_dec_ref_known(v___x_1396_, 3);
lean_dec_ref(v_inheritedTraceOptions_1392_);
lean_dec_ref(v_options_1390_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v_c_1352_);
v___x_1475_ = v___x_1400_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_c_1352_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec_ref_known(v___x_1396_, 3);
lean_dec_ref(v_inheritedTraceOptions_1392_);
lean_dec_ref(v_options_1390_);
lean_dec_ref(v_c_1352_);
v_a_1478_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1397_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1397_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1352_ = stack[0].m_obj;
lean_object* v_a_1353_ = stack[1].m_obj;
lean_object* v_a_1354_ = stack[2].m_obj;
lean_object* v_a_1355_ = stack[3].m_obj;
lean_object* v_a_1356_ = stack[4].m_obj;
lean_object* v_a_1357_ = stack[5].m_obj;
lean_object* v_a_1358_ = stack[6].m_obj;
lean_object* v_a_1359_ = stack[7].m_obj;
lean_object* v_a_1360_ = stack[8].m_obj;
lean_object* v_a_1361_ = stack[9].m_obj;
lean_object* v_a_1362_ = stack[10].m_obj;
lean_object* v_a_1363_ = stack[11].m_obj;
lean_object* v_res_1490_;
v_res_1490_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
stack->m_obj
 = v_res_1490_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object* v_c_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
lean_dec(v_a_1502_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec(v_a_1492_);
return v_res_1504_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_ref_1511_; lean_object* v___x_1512_; lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1521_; 
v_ref_1511_ = lean_ctor_get(v___y_1508_, 2);
v___x_1512_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msg_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1515_ = v___x_1512_;
v_isShared_1516_ = v_isSharedCheck_1521_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1512_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1521_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1517_; lean_object* v___x_1519_; 
lean_inc(v_ref_1511_);
v___x_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1517_, 0, v_ref_1511_);
lean_ctor_set(v___x_1517_, 1, v_a_1513_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set_tag(v___x_1515_, 1);
lean_ctor_set(v___x_1515_, 0, v___x_1517_);
v___x_1519_ = v___x_1515_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1517_);
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
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1505_ = stack[0].m_obj;
lean_object* v___y_1506_ = stack[1].m_obj;
lean_object* v___y_1507_ = stack[2].m_obj;
lean_object* v___y_1508_ = stack[3].m_obj;
lean_object* v___y_1509_ = stack[4].m_obj;
lean_object* v_res_1522_;
v_res_1522_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
stack->m_obj
 = v_res_1522_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
return v_res_1529_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0));
v___x_1532_ = l_Lean_stringToMessageData(v___x_1531_);
return v___x_1532_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1557_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1557_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1557_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v_leFn_x3f_1550_; 
v_leFn_x3f_1550_ = lean_ctor_get(v_a_1546_, 20);
lean_inc(v_leFn_x3f_1550_);
lean_dec(v_a_1546_);
if (lean_obj_tag(v_leFn_x3f_1550_) == 1)
{
lean_object* v_val_1551_; lean_object* v___x_1553_; 
v_val_1551_ = lean_ctor_get(v_leFn_x3f_1550_, 0);
lean_inc(v_val_1551_);
lean_dec_ref_known(v_leFn_x3f_1550_, 1);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v_val_1551_);
v___x_1553_ = v___x_1548_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_val_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
lean_dec(v_leFn_x3f_1550_);
lean_del_object(v___x_1548_);
v___x_1555_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1);
v___x_1556_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1555_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
return v___x_1556_;
}
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
v_a_1558_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1545_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1545_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1533_ = stack[0].m_obj;
lean_object* v___y_1534_ = stack[1].m_obj;
lean_object* v___y_1535_ = stack[2].m_obj;
lean_object* v___y_1536_ = stack[3].m_obj;
lean_object* v___y_1537_ = stack[4].m_obj;
lean_object* v___y_1538_ = stack[5].m_obj;
lean_object* v___y_1539_ = stack[6].m_obj;
lean_object* v___y_1540_ = stack[7].m_obj;
lean_object* v___y_1541_ = stack[8].m_obj;
lean_object* v___y_1542_ = stack[9].m_obj;
lean_object* v___y_1543_ = stack[10].m_obj;
lean_object* v_res_1566_;
v_res_1566_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
stack->m_obj
 = v_res_1566_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___boxed(lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec(v___y_1567_);
return v_res_1579_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0));
v___x_1582_ = l_Lean_stringToMessageData(v___x_1581_);
return v___x_1582_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1607_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1607_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1607_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v_ltFn_x3f_1600_; 
v_ltFn_x3f_1600_ = lean_ctor_get(v_a_1596_, 21);
lean_inc(v_ltFn_x3f_1600_);
lean_dec(v_a_1596_);
if (lean_obj_tag(v_ltFn_x3f_1600_) == 1)
{
lean_object* v_val_1601_; lean_object* v___x_1603_; 
v_val_1601_ = lean_ctor_get(v_ltFn_x3f_1600_, 0);
lean_inc(v_val_1601_);
lean_dec_ref_known(v_ltFn_x3f_1600_, 1);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v_val_1601_);
v___x_1603_ = v___x_1598_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_val_1601_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
lean_dec(v_ltFn_x3f_1600_);
lean_del_object(v___x_1598_);
v___x_1605_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1);
v___x_1606_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1605_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
return v___x_1606_;
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
v_a_1608_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1595_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1595_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1583_ = stack[0].m_obj;
lean_object* v___y_1584_ = stack[1].m_obj;
lean_object* v___y_1585_ = stack[2].m_obj;
lean_object* v___y_1586_ = stack[3].m_obj;
lean_object* v___y_1587_ = stack[4].m_obj;
lean_object* v___y_1588_ = stack[5].m_obj;
lean_object* v___y_1589_ = stack[6].m_obj;
lean_object* v___y_1590_ = stack[7].m_obj;
lean_object* v___y_1591_ = stack[8].m_obj;
lean_object* v___y_1592_ = stack[9].m_obj;
lean_object* v___y_1593_ = stack[10].m_obj;
lean_object* v_res_1616_;
v_res_1616_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
stack->m_obj
 = v_res_1616_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___boxed(lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec(v___y_1617_);
return v_res_1629_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(lean_object* v_p_1630_, uint8_t v_strict_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
if (v_strict_1631_ == 0)
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1646_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v___x_1644_, 1);
v___x_1646_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1630_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1648_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1647_);
lean_dec_ref_known(v___x_1646_, 1);
v___x_1648_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
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
else
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1669_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1667_, 1);
v___x_1669_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1630_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1671_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1670_);
lean_dec_ref_known(v___x_1669_, 1);
v___x_1671_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1681_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1674_ = v___x_1671_;
v_isShared_1675_ = v_isSharedCheck_1681_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1671_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1681_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v_ofNatZero_1676_; lean_object* v___x_1677_; lean_object* v___x_1679_; 
v_ofNatZero_1676_ = lean_ctor_get(v_a_1672_, 18);
lean_inc_ref(v_ofNatZero_1676_);
lean_dec(v_a_1672_);
v___x_1677_ = l_Lean_mkAppB(v_a_1668_, v_a_1670_, v_ofNatZero_1676_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1677_);
v___x_1679_ = v___x_1674_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec(v_a_1670_);
lean_dec(v_a_1668_);
v_a_1682_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1671_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1671_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
else
{
lean_dec(v_a_1668_);
return v___x_1669_;
}
}
else
{
return v___x_1667_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1630_ = stack[0].m_obj;
uint8_t v_strict_1631_ = stack[1].m_num;
lean_object* v___y_1632_ = stack[2].m_obj;
lean_object* v___y_1633_ = stack[3].m_obj;
lean_object* v___y_1634_ = stack[4].m_obj;
lean_object* v___y_1635_ = stack[5].m_obj;
lean_object* v___y_1636_ = stack[6].m_obj;
lean_object* v___y_1637_ = stack[7].m_obj;
lean_object* v___y_1638_ = stack[8].m_obj;
lean_object* v___y_1639_ = stack[9].m_obj;
lean_object* v___y_1640_ = stack[10].m_obj;
lean_object* v___y_1641_ = stack[11].m_obj;
lean_object* v___y_1642_ = stack[12].m_obj;
lean_object* v_res_1690_;
v_res_1690_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1630_, v_strict_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
stack->m_obj
 = v_res_1690_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_p_1691_, lean_object* v_strict_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
uint8_t v_strict_boxed_1705_; lean_object* v_res_1706_; 
v_strict_boxed_1705_ = lean_unbox(v_strict_1692_);
v_res_1706_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1691_, v_strict_boxed_1705_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec(v_p_1691_);
return v_res_1706_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(lean_object* v_c_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v_p_1720_; uint8_t v_strict_1721_; lean_object* v___x_1722_; 
v_p_1720_ = lean_ctor_get(v_c_1707_, 0);
v_strict_1721_ = lean_ctor_get_uint8(v_c_1707_, sizeof(void*)*2);
v___x_1722_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1720_, v_strict_1721_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
return v___x_1722_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1707_ = stack[0].m_obj;
lean_object* v___y_1708_ = stack[1].m_obj;
lean_object* v___y_1709_ = stack[2].m_obj;
lean_object* v___y_1710_ = stack[3].m_obj;
lean_object* v___y_1711_ = stack[4].m_obj;
lean_object* v___y_1712_ = stack[5].m_obj;
lean_object* v___y_1713_ = stack[6].m_obj;
lean_object* v___y_1714_ = stack[7].m_obj;
lean_object* v___y_1715_ = stack[8].m_obj;
lean_object* v___y_1716_ = stack[9].m_obj;
lean_object* v___y_1717_ = stack[10].m_obj;
lean_object* v___y_1718_ = stack[11].m_obj;
lean_object* v_res_1723_;
v_res_1723_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
stack->m_obj
 = v_res_1723_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0___boxed(lean_object* v_c_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v_c_1724_);
return v_res_1737_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object* v_a_1738_, lean_object* v_x_1739_, lean_object* v_c_u2081_1740_, lean_object* v_b_1741_, lean_object* v_c_u2082_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v_toCold_1755_; lean_object* v_options_1756_; lean_object* v_p_1757_; lean_object* v_p_1758_; uint8_t v_strict_1759_; lean_object* v_inheritedTraceOptions_1760_; uint8_t v_hasTrace_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v_p_1766_; 
v_toCold_1755_ = lean_ctor_get(v_a_1752_, 0);
v_options_1756_ = lean_ctor_get(v_toCold_1755_, 2);
v_p_1757_ = lean_ctor_get(v_c_u2081_1740_, 0);
v_p_1758_ = lean_ctor_get(v_c_u2082_1742_, 0);
v_strict_1759_ = lean_ctor_get_uint8(v_c_u2082_1742_, sizeof(void*)*2);
v_inheritedTraceOptions_1760_ = lean_ctor_get(v_toCold_1755_, 11);
v_hasTrace_1761_ = lean_ctor_get_uint8(v_options_1756_, sizeof(void*)*1);
v___x_1762_ = lean_nat_to_int(v_a_1738_);
lean_inc(v_p_1758_);
v___x_1763_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1758_, v___x_1762_);
lean_dec(v___x_1762_);
v___x_1764_ = lean_int_neg(v_b_1741_);
lean_inc(v_p_1757_);
v___x_1765_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1757_, v___x_1764_);
lean_dec(v___x_1764_);
v_p_1766_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1763_, v___x_1765_);
if (v_hasTrace_1761_ == 0)
{
goto v___jp_1767_;
}
else
{
lean_object* v_cls_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v_cls_1771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_1772_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2);
v___x_1773_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1760_, v_options_1756_, v___x_1772_);
if (v___x_1773_ == 0)
{
goto v___jp_1767_;
}
else
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1739_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1776_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref_known(v___x_1774_, 1);
v___x_1776_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_1740_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1778_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref_known(v___x_1776_, 1);
v___x_1778_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_u2082_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref_known(v___x_1778_, 1);
v___x_1780_ = l_Lean_MessageData_ofExpr(v_a_1775_);
v___x_1781_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_1782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1780_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = l_Lean_MessageData_ofExpr(v_a_1777_);
v___x_1784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
lean_ctor_set(v___x_1785_, 1, v___x_1781_);
v___x_1786_ = l_Lean_MessageData_ofExpr(v_a_1779_);
v___x_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1785_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_1771_, v___x_1787_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_dec_ref_known(v___x_1788_, 1);
goto v___jp_1767_;
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec(v_p_1766_);
lean_dec_ref(v_c_u2082_1742_);
lean_dec_ref(v_c_u2081_1740_);
lean_dec(v_x_1739_);
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec(v_a_1777_);
lean_dec(v_a_1775_);
lean_dec(v_p_1766_);
lean_dec_ref(v_c_u2082_1742_);
lean_dec_ref(v_c_u2081_1740_);
lean_dec(v_x_1739_);
v_a_1797_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1778_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1778_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_dec(v_a_1775_);
lean_dec(v_p_1766_);
lean_dec_ref(v_c_u2082_1742_);
lean_dec_ref(v_c_u2081_1740_);
lean_dec(v_x_1739_);
v_a_1805_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1776_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1776_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec(v_p_1766_);
lean_dec_ref(v_c_u2082_1742_);
lean_dec_ref(v_c_u2081_1740_);
lean_dec(v_x_1739_);
v_a_1813_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1774_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1774_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
v___jp_1767_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1768_ = lean_alloc_ctor(13, 3, 0);
lean_ctor_set(v___x_1768_, 0, v_x_1739_);
lean_ctor_set(v___x_1768_, 1, v_c_u2081_1740_);
lean_ctor_set(v___x_1768_, 2, v_c_u2082_1742_);
v___x_1769_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1769_, 0, v_p_1766_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
lean_ctor_set_uint8(v___x_1769_, sizeof(void*)*2, v_strict_1759_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
return v___x_1770_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1738_ = stack[0].m_obj;
lean_object* v_x_1739_ = stack[1].m_obj;
lean_object* v_c_u2081_1740_ = stack[2].m_obj;
lean_object* v_b_1741_ = stack[3].m_obj;
lean_object* v_c_u2082_1742_ = stack[4].m_obj;
lean_object* v_a_1743_ = stack[5].m_obj;
lean_object* v_a_1744_ = stack[6].m_obj;
lean_object* v_a_1745_ = stack[7].m_obj;
lean_object* v_a_1746_ = stack[8].m_obj;
lean_object* v_a_1747_ = stack[9].m_obj;
lean_object* v_a_1748_ = stack[10].m_obj;
lean_object* v_a_1749_ = stack[11].m_obj;
lean_object* v_a_1750_ = stack[12].m_obj;
lean_object* v_a_1751_ = stack[13].m_obj;
lean_object* v_a_1752_ = stack[14].m_obj;
lean_object* v_a_1753_ = stack[15].m_obj;
lean_object* v_res_1821_;
v_res_1821_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1738_, v_x_1739_, v_c_u2081_1740_, v_b_1741_, v_c_u2082_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
stack->m_obj
 = v_res_1821_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object** _args){
lean_object* v_a_1822_ = _args[0];
lean_object* v_x_1823_ = _args[1];
lean_object* v_c_u2081_1824_ = _args[2];
lean_object* v_b_1825_ = _args[3];
lean_object* v_c_u2082_1826_ = _args[4];
lean_object* v_a_1827_ = _args[5];
lean_object* v_a_1828_ = _args[6];
lean_object* v_a_1829_ = _args[7];
lean_object* v_a_1830_ = _args[8];
lean_object* v_a_1831_ = _args[9];
lean_object* v_a_1832_ = _args[10];
lean_object* v_a_1833_ = _args[11];
lean_object* v_a_1834_ = _args[12];
lean_object* v_a_1835_ = _args[13];
lean_object* v_a_1836_ = _args[14];
lean_object* v_a_1837_ = _args[15];
lean_object* v_a_1838_ = _args[16];
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1822_, v_x_1823_, v_c_u2081_1824_, v_b_1825_, v_c_u2082_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
lean_dec(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec(v_a_1827_);
lean_dec(v_b_1825_);
return v_res_1839_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1840_, lean_object* v_msg_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1841_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
return v___x_1854_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1841_ = stack[1].m_obj;
lean_object* v___y_1842_ = stack[2].m_obj;
lean_object* v___y_1843_ = stack[3].m_obj;
lean_object* v___y_1844_ = stack[4].m_obj;
lean_object* v___y_1845_ = stack[5].m_obj;
lean_object* v___y_1846_ = stack[6].m_obj;
lean_object* v___y_1847_ = stack[7].m_obj;
lean_object* v___y_1848_ = stack[8].m_obj;
lean_object* v___y_1849_ = stack[9].m_obj;
lean_object* v___y_1850_ = stack[10].m_obj;
lean_object* v___y_1851_ = stack[11].m_obj;
lean_object* v___y_1852_ = stack[12].m_obj;
lean_object* v_res_1855_;
v_res_1855_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(lean_box(0), v_msg_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
stack->m_obj
 = v_res_1855_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1856_, lean_object* v_msg_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1856_, v_msg_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec(v___y_1858_);
return v_res_1870_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(lean_object* v_a_1879_, lean_object* v_x_1880_, lean_object* v_c_u2081_1881_, lean_object* v_as_1882_, size_t v_sz_1883_, size_t v_i_1884_, lean_object* v_b_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
uint8_t v___x_1898_; 
v___x_1898_ = lean_usize_dec_lt(v_i_1884_, v_sz_1883_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; 
lean_dec_ref(v_c_u2081_1881_);
lean_dec(v_x_1880_);
lean_dec(v_a_1879_);
v___x_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1899_, 0, v_b_1885_);
return v___x_1899_;
}
else
{
lean_object* v_a_1900_; lean_object* v_fst_1901_; lean_object* v_snd_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
lean_dec_ref(v_b_1885_);
v_a_1900_ = lean_array_uget_borrowed(v_as_1882_, v_i_1884_);
v_fst_1901_ = lean_ctor_get(v_a_1900_, 0);
v_snd_1902_ = lean_ctor_get(v_a_1900_, 1);
v___x_1903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
lean_inc(v_snd_1902_);
lean_inc_ref(v_c_u2081_1881_);
lean_inc(v_x_1880_);
lean_inc(v_a_1879_);
v___x_1904_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1879_, v_x_1880_, v_c_u2081_1881_, v_fst_1901_, v_snd_1902_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1906_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
v___x_1906_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_a_1905_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v___x_1907_; 
lean_dec_ref_known(v___x_1906_, 1);
v___x_1907_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1920_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_1920_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1920_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
uint8_t v___x_1912_; 
v___x_1912_ = lean_unbox(v_a_1908_);
lean_dec(v_a_1908_);
if (v___x_1912_ == 0)
{
size_t v___x_1913_; size_t v___x_1914_; 
lean_del_object(v___x_1910_);
v___x_1913_ = ((size_t)1ULL);
v___x_1914_ = lean_usize_add(v_i_1884_, v___x_1913_);
v_i_1884_ = v___x_1914_;
v_b_1885_ = v___x_1903_;
goto _start;
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1918_; 
lean_dec_ref(v_c_u2081_1881_);
lean_dec(v_x_1880_);
lean_dec(v_a_1879_);
v___x_1916_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v___x_1916_);
v___x_1918_ = v___x_1910_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec_ref(v_c_u2081_1881_);
lean_dec(v_x_1880_);
lean_dec(v_a_1879_);
v_a_1921_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1907_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1907_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec_ref(v_c_u2081_1881_);
lean_dec(v_x_1880_);
lean_dec(v_a_1879_);
v_a_1929_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1906_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1906_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec_ref(v_c_u2081_1881_);
lean_dec(v_x_1880_);
lean_dec(v_a_1879_);
v_a_1937_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1904_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1904_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1879_ = stack[0].m_obj;
lean_object* v_x_1880_ = stack[1].m_obj;
lean_object* v_c_u2081_1881_ = stack[2].m_obj;
lean_object* v_as_1882_ = stack[3].m_obj;
size_t v_sz_1883_ = stack[4].m_num;
size_t v_i_1884_ = stack[5].m_num;
lean_object* v_b_1885_ = stack[6].m_obj;
lean_object* v___y_1886_ = stack[7].m_obj;
lean_object* v___y_1887_ = stack[8].m_obj;
lean_object* v___y_1888_ = stack[9].m_obj;
lean_object* v___y_1889_ = stack[10].m_obj;
lean_object* v___y_1890_ = stack[11].m_obj;
lean_object* v___y_1891_ = stack[12].m_obj;
lean_object* v___y_1892_ = stack[13].m_obj;
lean_object* v___y_1893_ = stack[14].m_obj;
lean_object* v___y_1894_ = stack[15].m_obj;
lean_object* v___y_1895_ = stack[16].m_obj;
lean_object* v___y_1896_ = stack[17].m_obj;
lean_object* v_res_1945_;
v_res_1945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1879_, v_x_1880_, v_c_u2081_1881_, v_as_1882_, v_sz_1883_, v_i_1884_, v_b_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
stack->m_obj
 = v_res_1945_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___boxed(lean_object** _args){
lean_object* v_a_1946_ = _args[0];
lean_object* v_x_1947_ = _args[1];
lean_object* v_c_u2081_1948_ = _args[2];
lean_object* v_as_1949_ = _args[3];
lean_object* v_sz_1950_ = _args[4];
lean_object* v_i_1951_ = _args[5];
lean_object* v_b_1952_ = _args[6];
lean_object* v___y_1953_ = _args[7];
lean_object* v___y_1954_ = _args[8];
lean_object* v___y_1955_ = _args[9];
lean_object* v___y_1956_ = _args[10];
lean_object* v___y_1957_ = _args[11];
lean_object* v___y_1958_ = _args[12];
lean_object* v___y_1959_ = _args[13];
lean_object* v___y_1960_ = _args[14];
lean_object* v___y_1961_ = _args[15];
lean_object* v___y_1962_ = _args[16];
lean_object* v___y_1963_ = _args[17];
lean_object* v___y_1964_ = _args[18];
_start:
{
size_t v_sz_boxed_1965_; size_t v_i_boxed_1966_; lean_object* v_res_1967_; 
v_sz_boxed_1965_ = lean_unbox_usize(v_sz_1950_);
lean_dec(v_sz_1950_);
v_i_boxed_1966_ = lean_unbox_usize(v_i_1951_);
lean_dec(v_i_1951_);
v_res_1967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1946_, v_x_1947_, v_c_u2081_1948_, v_as_1949_, v_sz_boxed_1965_, v_i_boxed_1966_, v_b_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v_as_1949_);
return v_res_1967_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(lean_object* v_a_1968_, lean_object* v_x_1969_, lean_object* v_c_u2081_1970_, lean_object* v_todo_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; size_t v_sz_1986_; size_t v___x_1987_; lean_object* v___x_1988_; 
v___x_1984_ = lean_box(0);
v___x_1985_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_1986_ = lean_array_size(v_todo_1971_);
v___x_1987_ = ((size_t)0ULL);
v___x_1988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1968_, v_x_1969_, v_c_u2081_1970_, v_todo_1971_, v_sz_1986_, v___x_1987_, v___x_1985_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2001_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_2001_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2001_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v_fst_1993_; 
v_fst_1993_ = lean_ctor_get(v_a_1989_, 0);
lean_inc(v_fst_1993_);
lean_dec(v_a_1989_);
if (lean_obj_tag(v_fst_1993_) == 0)
{
lean_object* v___x_1995_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_1984_);
v___x_1995_ = v___x_1991_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1984_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
else
{
lean_object* v_val_1997_; lean_object* v___x_1999_; 
v_val_1997_ = lean_ctor_get(v_fst_1993_, 0);
lean_inc(v_val_1997_);
lean_dec_ref_known(v_fst_1993_, 1);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v_val_1997_);
v___x_1999_ = v___x_1991_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_val_1997_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
v_a_2002_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1988_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1988_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1968_ = stack[0].m_obj;
lean_object* v_x_1969_ = stack[1].m_obj;
lean_object* v_c_u2081_1970_ = stack[2].m_obj;
lean_object* v_todo_1971_ = stack[3].m_obj;
lean_object* v_a_1972_ = stack[4].m_obj;
lean_object* v_a_1973_ = stack[5].m_obj;
lean_object* v_a_1974_ = stack[6].m_obj;
lean_object* v_a_1975_ = stack[7].m_obj;
lean_object* v_a_1976_ = stack[8].m_obj;
lean_object* v_a_1977_ = stack[9].m_obj;
lean_object* v_a_1978_ = stack[10].m_obj;
lean_object* v_a_1979_ = stack[11].m_obj;
lean_object* v_a_1980_ = stack[12].m_obj;
lean_object* v_a_1981_ = stack[13].m_obj;
lean_object* v_a_1982_ = stack[14].m_obj;
lean_object* v_res_2010_;
v_res_2010_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_1968_, v_x_1969_, v_c_u2081_1970_, v_todo_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
stack->m_obj
 = v_res_2010_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object* v_a_2011_, lean_object* v_x_2012_, lean_object* v_c_u2081_2013_, lean_object* v_todo_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2011_, v_x_2012_, v_c_u2081_2013_, v_todo_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_);
lean_dec(v_a_2025_);
lean_dec_ref(v_a_2024_);
lean_dec(v_a_2023_);
lean_dec_ref(v_a_2022_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_todo_2014_);
return v_res_2027_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_2028_, lean_object* v_as_2029_, size_t v_sz_2030_, size_t v_i_2031_, lean_object* v_b_2032_){
_start:
{
uint8_t v___x_2033_; 
v___x_2033_ = lean_usize_dec_lt(v_i_2031_, v_sz_2030_);
if (v___x_2033_ == 0)
{
return v_b_2032_;
}
else
{
lean_object* v_snd_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2067_; 
v_snd_2034_ = lean_ctor_get(v_b_2032_, 1);
v_isSharedCheck_2067_ = !lean_is_exclusive(v_b_2032_);
if (v_isSharedCheck_2067_ == 0)
{
lean_object* v_unused_2068_; 
v_unused_2068_ = lean_ctor_get(v_b_2032_, 0);
lean_dec(v_unused_2068_);
v___x_2036_ = v_b_2032_;
v_isShared_2037_ = v_isSharedCheck_2067_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_snd_2034_);
lean_dec(v_b_2032_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2067_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v_fst_2038_; lean_object* v_snd_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2066_; 
v_fst_2038_ = lean_ctor_get(v_snd_2034_, 0);
v_snd_2039_ = lean_ctor_get(v_snd_2034_, 1);
v_isSharedCheck_2066_ = !lean_is_exclusive(v_snd_2034_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2041_ = v_snd_2034_;
v_isShared_2042_ = v_isSharedCheck_2066_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_snd_2039_);
lean_inc(v_fst_2038_);
lean_dec(v_snd_2034_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2066_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v_a_2043_; lean_object* v_p_2044_; lean_object* v___x_2045_; lean_object* v_a_2047_; lean_object* v_b_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; 
v_a_2043_ = lean_array_uget_borrowed(v_as_2029_, v_i_2031_);
v_p_2044_ = lean_ctor_get(v_a_2043_, 0);
v___x_2045_ = lean_box(0);
v_b_2054_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2044_, v_x_2028_);
v___x_2055_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2056_ = lean_int_dec_eq(v_b_2054_, v___x_2055_);
if (v___x_2056_ == 0)
{
lean_object* v___x_2058_; 
lean_inc(v_a_2043_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 1, v_a_2043_);
lean_ctor_set(v___x_2036_, 0, v_b_2054_);
v___x_2058_ = v___x_2036_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_b_2054_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_a_2043_);
v___x_2058_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v_todo_2059_; lean_object* v___x_2060_; 
v_todo_2059_ = lean_array_push(v_snd_2039_, v___x_2058_);
v___x_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2060_, 0, v_fst_2038_);
lean_ctor_set(v___x_2060_, 1, v_todo_2059_);
v_a_2047_ = v___x_2060_;
goto v___jp_2046_;
}
}
else
{
lean_object* v_cs_x27_2062_; lean_object* v___x_2064_; 
lean_dec(v_b_2054_);
lean_inc(v_a_2043_);
v_cs_x27_2062_ = l_Lean_PersistentArray_push___redArg(v_fst_2038_, v_a_2043_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 1, v_snd_2039_);
lean_ctor_set(v___x_2036_, 0, v_cs_x27_2062_);
v___x_2064_ = v___x_2036_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_cs_x27_2062_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_snd_2039_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
v_a_2047_ = v___x_2064_;
goto v___jp_2046_;
}
}
v___jp_2046_:
{
lean_object* v___x_2049_; 
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 1, v_a_2047_);
lean_ctor_set(v___x_2041_, 0, v___x_2045_);
v___x_2049_ = v___x_2041_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_a_2047_);
v___x_2049_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
size_t v___x_2050_; size_t v___x_2051_; 
v___x_2050_ = ((size_t)1ULL);
v___x_2051_ = lean_usize_add(v_i_2031_, v___x_2050_);
v_i_2031_ = v___x_2051_;
v_b_2032_ = v___x_2049_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2028_ = stack[0].m_obj;
lean_object* v_as_2029_ = stack[1].m_obj;
size_t v_sz_2030_ = stack[2].m_num;
size_t v_i_2031_ = stack[3].m_num;
lean_object* v_b_2032_ = stack[4].m_obj;
lean_object* v_res_2069_;
v_res_2069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2028_, v_as_2029_, v_sz_2030_, v_i_2031_, v_b_2032_);
stack->m_obj
 = v_res_2069_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_2070_, lean_object* v_as_2071_, lean_object* v_sz_2072_, lean_object* v_i_2073_, lean_object* v_b_2074_){
_start:
{
size_t v_sz_boxed_2075_; size_t v_i_boxed_2076_; lean_object* v_res_2077_; 
v_sz_boxed_2075_ = lean_unbox_usize(v_sz_2072_);
lean_dec(v_sz_2072_);
v_i_boxed_2076_ = lean_unbox_usize(v_i_2073_);
lean_dec(v_i_2073_);
v_res_2077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2070_, v_as_2071_, v_sz_boxed_2075_, v_i_boxed_2076_, v_b_2074_);
lean_dec_ref(v_as_2071_);
lean_dec(v_x_2070_);
return v_res_2077_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(lean_object* v_x_2078_, lean_object* v_as_2079_, size_t v_sz_2080_, size_t v_i_2081_, lean_object* v_b_2082_){
_start:
{
uint8_t v___x_2083_; 
v___x_2083_ = lean_usize_dec_lt(v_i_2081_, v_sz_2080_);
if (v___x_2083_ == 0)
{
return v_b_2082_;
}
else
{
lean_object* v_snd_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2117_; 
v_snd_2084_ = lean_ctor_get(v_b_2082_, 1);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_b_2082_);
if (v_isSharedCheck_2117_ == 0)
{
lean_object* v_unused_2118_; 
v_unused_2118_ = lean_ctor_get(v_b_2082_, 0);
lean_dec(v_unused_2118_);
v___x_2086_ = v_b_2082_;
v_isShared_2087_ = v_isSharedCheck_2117_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_snd_2084_);
lean_dec(v_b_2082_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2117_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v_fst_2088_; lean_object* v_snd_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2116_; 
v_fst_2088_ = lean_ctor_get(v_snd_2084_, 0);
v_snd_2089_ = lean_ctor_get(v_snd_2084_, 1);
v_isSharedCheck_2116_ = !lean_is_exclusive(v_snd_2084_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2091_ = v_snd_2084_;
v_isShared_2092_ = v_isSharedCheck_2116_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_snd_2089_);
lean_inc(v_fst_2088_);
lean_dec(v_snd_2084_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2116_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v_a_2093_; lean_object* v_p_2094_; lean_object* v___x_2095_; lean_object* v_a_2097_; lean_object* v_b_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v_a_2093_ = lean_array_uget_borrowed(v_as_2079_, v_i_2081_);
v_p_2094_ = lean_ctor_get(v_a_2093_, 0);
v___x_2095_ = lean_box(0);
v_b_2104_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2094_, v_x_2078_);
v___x_2105_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2106_ = lean_int_dec_eq(v_b_2104_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2108_; 
lean_inc(v_a_2093_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 1, v_a_2093_);
lean_ctor_set(v___x_2086_, 0, v_b_2104_);
v___x_2108_ = v___x_2086_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_b_2104_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_a_2093_);
v___x_2108_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v_todo_2109_; lean_object* v___x_2110_; 
v_todo_2109_ = lean_array_push(v_snd_2089_, v___x_2108_);
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v_fst_2088_);
lean_ctor_set(v___x_2110_, 1, v_todo_2109_);
v_a_2097_ = v___x_2110_;
goto v___jp_2096_;
}
}
else
{
lean_object* v_cs_x27_2112_; lean_object* v___x_2114_; 
lean_dec(v_b_2104_);
lean_inc(v_a_2093_);
v_cs_x27_2112_ = l_Lean_PersistentArray_push___redArg(v_fst_2088_, v_a_2093_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 1, v_snd_2089_);
lean_ctor_set(v___x_2086_, 0, v_cs_x27_2112_);
v___x_2114_ = v___x_2086_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_cs_x27_2112_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_snd_2089_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
v_a_2097_ = v___x_2114_;
goto v___jp_2096_;
}
}
v___jp_2096_:
{
lean_object* v___x_2099_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 1, v_a_2097_);
lean_ctor_set(v___x_2091_, 0, v___x_2095_);
v___x_2099_ = v___x_2091_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_a_2097_);
v___x_2099_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
size_t v___x_2100_; size_t v___x_2101_; lean_object* v___x_2102_; 
v___x_2100_ = ((size_t)1ULL);
v___x_2101_ = lean_usize_add(v_i_2081_, v___x_2100_);
v___x_2102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2078_, v_as_2079_, v_sz_2080_, v___x_2101_, v___x_2099_);
return v___x_2102_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2078_ = stack[0].m_obj;
lean_object* v_as_2079_ = stack[1].m_obj;
size_t v_sz_2080_ = stack[2].m_num;
size_t v_i_2081_ = stack[3].m_num;
lean_object* v_b_2082_ = stack[4].m_obj;
lean_object* v_res_2119_;
v_res_2119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2078_, v_as_2079_, v_sz_2080_, v_i_2081_, v_b_2082_);
stack->m_obj
 = v_res_2119_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2120_, lean_object* v_as_2121_, lean_object* v_sz_2122_, lean_object* v_i_2123_, lean_object* v_b_2124_){
_start:
{
size_t v_sz_boxed_2125_; size_t v_i_boxed_2126_; lean_object* v_res_2127_; 
v_sz_boxed_2125_ = lean_unbox_usize(v_sz_2122_);
lean_dec(v_sz_2122_);
v_i_boxed_2126_ = lean_unbox_usize(v_i_2123_);
lean_dec(v_i_2123_);
v_res_2127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2120_, v_as_2121_, v_sz_boxed_2125_, v_i_boxed_2126_, v_b_2124_);
lean_dec_ref(v_as_2121_);
lean_dec(v_x_2120_);
return v_res_2127_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_2128_, lean_object* v_as_2129_, size_t v_sz_2130_, size_t v_i_2131_, lean_object* v_b_2132_){
_start:
{
uint8_t v___x_2133_; 
v___x_2133_ = lean_usize_dec_lt(v_i_2131_, v_sz_2130_);
if (v___x_2133_ == 0)
{
return v_b_2132_;
}
else
{
lean_object* v_snd_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2167_; 
v_snd_2134_ = lean_ctor_get(v_b_2132_, 1);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_b_2132_);
if (v_isSharedCheck_2167_ == 0)
{
lean_object* v_unused_2168_; 
v_unused_2168_ = lean_ctor_get(v_b_2132_, 0);
lean_dec(v_unused_2168_);
v___x_2136_ = v_b_2132_;
v_isShared_2137_ = v_isSharedCheck_2167_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_snd_2134_);
lean_dec(v_b_2132_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2167_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v_fst_2138_; lean_object* v_snd_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2166_; 
v_fst_2138_ = lean_ctor_get(v_snd_2134_, 0);
v_snd_2139_ = lean_ctor_get(v_snd_2134_, 1);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_snd_2134_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2141_ = v_snd_2134_;
v_isShared_2142_ = v_isSharedCheck_2166_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_snd_2139_);
lean_inc(v_fst_2138_);
lean_dec(v_snd_2134_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2166_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v_a_2143_; lean_object* v_p_2144_; lean_object* v___x_2145_; lean_object* v_a_2147_; lean_object* v_b_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v_a_2143_ = lean_array_uget_borrowed(v_as_2129_, v_i_2131_);
v_p_2144_ = lean_ctor_get(v_a_2143_, 0);
v___x_2145_ = lean_box(0);
v_b_2154_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2144_, v_x_2128_);
v___x_2155_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2156_ = lean_int_dec_eq(v_b_2154_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2158_; 
lean_inc(v_a_2143_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 1, v_a_2143_);
lean_ctor_set(v___x_2136_, 0, v_b_2154_);
v___x_2158_ = v___x_2136_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_b_2154_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_a_2143_);
v___x_2158_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v_todo_2159_; lean_object* v___x_2160_; 
v_todo_2159_ = lean_array_push(v_snd_2139_, v___x_2158_);
v___x_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2160_, 0, v_fst_2138_);
lean_ctor_set(v___x_2160_, 1, v_todo_2159_);
v_a_2147_ = v___x_2160_;
goto v___jp_2146_;
}
}
else
{
lean_object* v_cs_x27_2162_; lean_object* v___x_2164_; 
lean_dec(v_b_2154_);
lean_inc(v_a_2143_);
v_cs_x27_2162_ = l_Lean_PersistentArray_push___redArg(v_fst_2138_, v_a_2143_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 1, v_snd_2139_);
lean_ctor_set(v___x_2136_, 0, v_cs_x27_2162_);
v___x_2164_ = v___x_2136_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_cs_x27_2162_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_snd_2139_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
v_a_2147_ = v___x_2164_;
goto v___jp_2146_;
}
}
v___jp_2146_:
{
lean_object* v___x_2149_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 1, v_a_2147_);
lean_ctor_set(v___x_2141_, 0, v___x_2145_);
v___x_2149_ = v___x_2141_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2145_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_a_2147_);
v___x_2149_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
size_t v___x_2150_; size_t v___x_2151_; 
v___x_2150_ = ((size_t)1ULL);
v___x_2151_ = lean_usize_add(v_i_2131_, v___x_2150_);
v_i_2131_ = v___x_2151_;
v_b_2132_ = v___x_2149_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2128_ = stack[0].m_obj;
lean_object* v_as_2129_ = stack[1].m_obj;
size_t v_sz_2130_ = stack[2].m_num;
size_t v_i_2131_ = stack[3].m_num;
lean_object* v_b_2132_ = stack[4].m_obj;
lean_object* v_res_2169_;
v_res_2169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2128_, v_as_2129_, v_sz_2130_, v_i_2131_, v_b_2132_);
stack->m_obj
 = v_res_2169_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_2170_, lean_object* v_as_2171_, lean_object* v_sz_2172_, lean_object* v_i_2173_, lean_object* v_b_2174_){
_start:
{
size_t v_sz_boxed_2175_; size_t v_i_boxed_2176_; lean_object* v_res_2177_; 
v_sz_boxed_2175_ = lean_unbox_usize(v_sz_2172_);
lean_dec(v_sz_2172_);
v_i_boxed_2176_ = lean_unbox_usize(v_i_2173_);
lean_dec(v_i_2173_);
v_res_2177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2170_, v_as_2171_, v_sz_boxed_2175_, v_i_boxed_2176_, v_b_2174_);
lean_dec_ref(v_as_2171_);
lean_dec(v_x_2170_);
return v_res_2177_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2178_, lean_object* v_as_2179_, size_t v_sz_2180_, size_t v_i_2181_, lean_object* v_b_2182_){
_start:
{
uint8_t v___x_2183_; 
v___x_2183_ = lean_usize_dec_lt(v_i_2181_, v_sz_2180_);
if (v___x_2183_ == 0)
{
return v_b_2182_;
}
else
{
lean_object* v_snd_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2217_; 
v_snd_2184_ = lean_ctor_get(v_b_2182_, 1);
v_isSharedCheck_2217_ = !lean_is_exclusive(v_b_2182_);
if (v_isSharedCheck_2217_ == 0)
{
lean_object* v_unused_2218_; 
v_unused_2218_ = lean_ctor_get(v_b_2182_, 0);
lean_dec(v_unused_2218_);
v___x_2186_ = v_b_2182_;
v_isShared_2187_ = v_isSharedCheck_2217_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_snd_2184_);
lean_dec(v_b_2182_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2217_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v_fst_2188_; lean_object* v_snd_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2216_; 
v_fst_2188_ = lean_ctor_get(v_snd_2184_, 0);
v_snd_2189_ = lean_ctor_get(v_snd_2184_, 1);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_snd_2184_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2191_ = v_snd_2184_;
v_isShared_2192_ = v_isSharedCheck_2216_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_snd_2189_);
lean_inc(v_fst_2188_);
lean_dec(v_snd_2184_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2216_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v_a_2193_; lean_object* v_p_2194_; lean_object* v___x_2195_; lean_object* v_a_2197_; lean_object* v_b_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
v_a_2193_ = lean_array_uget_borrowed(v_as_2179_, v_i_2181_);
v_p_2194_ = lean_ctor_get(v_a_2193_, 0);
v___x_2195_ = lean_box(0);
v_b_2204_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2194_, v_x_2178_);
v___x_2205_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2206_ = lean_int_dec_eq(v_b_2204_, v___x_2205_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2208_; 
lean_inc(v_a_2193_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 1, v_a_2193_);
lean_ctor_set(v___x_2186_, 0, v_b_2204_);
v___x_2208_ = v___x_2186_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_b_2204_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_a_2193_);
v___x_2208_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
lean_object* v_todo_2209_; lean_object* v___x_2210_; 
v_todo_2209_ = lean_array_push(v_snd_2189_, v___x_2208_);
v___x_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2210_, 0, v_fst_2188_);
lean_ctor_set(v___x_2210_, 1, v_todo_2209_);
v_a_2197_ = v___x_2210_;
goto v___jp_2196_;
}
}
else
{
lean_object* v_cs_x27_2212_; lean_object* v___x_2214_; 
lean_dec(v_b_2204_);
lean_inc(v_a_2193_);
v_cs_x27_2212_ = l_Lean_PersistentArray_push___redArg(v_fst_2188_, v_a_2193_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 1, v_snd_2189_);
lean_ctor_set(v___x_2186_, 0, v_cs_x27_2212_);
v___x_2214_ = v___x_2186_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_cs_x27_2212_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_snd_2189_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
v_a_2197_ = v___x_2214_;
goto v___jp_2196_;
}
}
v___jp_2196_:
{
lean_object* v___x_2199_; 
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 1, v_a_2197_);
lean_ctor_set(v___x_2191_, 0, v___x_2195_);
v___x_2199_ = v___x_2191_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_a_2197_);
v___x_2199_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
size_t v___x_2200_; size_t v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = ((size_t)1ULL);
v___x_2201_ = lean_usize_add(v_i_2181_, v___x_2200_);
v___x_2202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2178_, v_as_2179_, v_sz_2180_, v___x_2201_, v___x_2199_);
return v___x_2202_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2178_ = stack[0].m_obj;
lean_object* v_as_2179_ = stack[1].m_obj;
size_t v_sz_2180_ = stack[2].m_num;
size_t v_i_2181_ = stack[3].m_num;
lean_object* v_b_2182_ = stack[4].m_obj;
lean_object* v_res_2219_;
v_res_2219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2178_, v_as_2179_, v_sz_2180_, v_i_2181_, v_b_2182_);
stack->m_obj
 = v_res_2219_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_2220_, lean_object* v_as_2221_, lean_object* v_sz_2222_, lean_object* v_i_2223_, lean_object* v_b_2224_){
_start:
{
size_t v_sz_boxed_2225_; size_t v_i_boxed_2226_; lean_object* v_res_2227_; 
v_sz_boxed_2225_ = lean_unbox_usize(v_sz_2222_);
lean_dec(v_sz_2222_);
v_i_boxed_2226_ = lean_unbox_usize(v_i_2223_);
lean_dec(v_i_2223_);
v_res_2227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2220_, v_as_2221_, v_sz_boxed_2225_, v_i_boxed_2226_, v_b_2224_);
lean_dec_ref(v_as_2221_);
lean_dec(v_x_2220_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(lean_object* v_init_2228_, lean_object* v_x_2229_, lean_object* v_n_2230_, lean_object* v_b_2231_){
_start:
{
if (lean_obj_tag(v_n_2230_) == 0)
{
lean_object* v_cs_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; size_t v_sz_2235_; size_t v___x_2236_; lean_object* v___x_2237_; lean_object* v_fst_2238_; 
v_cs_2232_ = lean_ctor_get(v_n_2230_, 0);
v___x_2233_ = lean_box(0);
v___x_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
lean_ctor_set(v___x_2234_, 1, v_b_2231_);
v_sz_2235_ = lean_array_size(v_cs_2232_);
v___x_2236_ = ((size_t)0ULL);
v___x_2237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2228_, v_x_2229_, v_cs_2232_, v_sz_2235_, v___x_2236_, v___x_2234_);
v_fst_2238_ = lean_ctor_get(v___x_2237_, 0);
if (lean_obj_tag(v_fst_2238_) == 0)
{
lean_object* v_snd_2239_; lean_object* v___x_2240_; 
v_snd_2239_ = lean_ctor_get(v___x_2237_, 1);
lean_inc(v_snd_2239_);
lean_dec_ref(v___x_2237_);
v___x_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2240_, 0, v_snd_2239_);
return v___x_2240_;
}
else
{
lean_object* v_val_2241_; 
lean_inc_ref(v_fst_2238_);
lean_dec_ref(v___x_2237_);
v_val_2241_ = lean_ctor_get(v_fst_2238_, 0);
lean_inc(v_val_2241_);
lean_dec_ref_known(v_fst_2238_, 1);
return v_val_2241_;
}
}
else
{
lean_object* v_vs_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; size_t v_sz_2245_; size_t v___x_2246_; lean_object* v___x_2247_; lean_object* v_fst_2248_; 
v_vs_2242_ = lean_ctor_get(v_n_2230_, 0);
v___x_2243_ = lean_box(0);
v___x_2244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
lean_ctor_set(v___x_2244_, 1, v_b_2231_);
v_sz_2245_ = lean_array_size(v_vs_2242_);
v___x_2246_ = ((size_t)0ULL);
v___x_2247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2229_, v_vs_2242_, v_sz_2245_, v___x_2246_, v___x_2244_);
v_fst_2248_ = lean_ctor_get(v___x_2247_, 0);
if (lean_obj_tag(v_fst_2248_) == 0)
{
lean_object* v_snd_2249_; lean_object* v___x_2250_; 
v_snd_2249_ = lean_ctor_get(v___x_2247_, 1);
lean_inc(v_snd_2249_);
lean_dec_ref(v___x_2247_);
v___x_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2250_, 0, v_snd_2249_);
return v___x_2250_;
}
else
{
lean_object* v_val_2251_; 
lean_inc_ref(v_fst_2248_);
lean_dec_ref(v___x_2247_);
v_val_2251_ = lean_ctor_get(v_fst_2248_, 0);
lean_inc(v_val_2251_);
lean_dec_ref_known(v_fst_2248_, 1);
return v_val_2251_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_2252_, lean_object* v_x_2253_, lean_object* v_as_2254_, size_t v_sz_2255_, size_t v_i_2256_, lean_object* v_b_2257_){
_start:
{
uint8_t v___x_2258_; 
v___x_2258_ = lean_usize_dec_lt(v_i_2256_, v_sz_2255_);
if (v___x_2258_ == 0)
{
return v_b_2257_;
}
else
{
lean_object* v_snd_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2277_; 
v_snd_2259_ = lean_ctor_get(v_b_2257_, 1);
v_isSharedCheck_2277_ = !lean_is_exclusive(v_b_2257_);
if (v_isSharedCheck_2277_ == 0)
{
lean_object* v_unused_2278_; 
v_unused_2278_ = lean_ctor_get(v_b_2257_, 0);
lean_dec(v_unused_2278_);
v___x_2261_ = v_b_2257_;
v_isShared_2262_ = v_isSharedCheck_2277_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_snd_2259_);
lean_dec(v_b_2257_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2277_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v_a_2263_; lean_object* v___x_2264_; 
v_a_2263_ = lean_array_uget_borrowed(v_as_2254_, v_i_2256_);
lean_inc(v_snd_2259_);
v___x_2264_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2252_, v_x_2253_, v_a_2263_, v_snd_2259_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v___x_2265_; lean_object* v___x_2267_; 
v___x_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 0, v___x_2265_);
v___x_2267_ = v___x_2261_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2265_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v_snd_2259_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2270_; lean_object* v___x_2272_; 
lean_dec(v_snd_2259_);
v_a_2269_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___x_2264_, 1);
v___x_2270_ = lean_box(0);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 1, v_a_2269_);
lean_ctor_set(v___x_2261_, 0, v___x_2270_);
v___x_2272_ = v___x_2261_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2270_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_a_2269_);
v___x_2272_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
size_t v___x_2273_; size_t v___x_2274_; 
v___x_2273_ = ((size_t)1ULL);
v___x_2274_ = lean_usize_add(v_i_2256_, v___x_2273_);
v_i_2256_ = v___x_2274_;
v_b_2257_ = v___x_2272_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2252_ = stack[0].m_obj;
lean_object* v_x_2253_ = stack[1].m_obj;
lean_object* v_as_2254_ = stack[2].m_obj;
size_t v_sz_2255_ = stack[3].m_num;
size_t v_i_2256_ = stack[4].m_num;
lean_object* v_b_2257_ = stack[5].m_obj;
lean_object* v_res_2279_;
v_res_2279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2252_, v_x_2253_, v_as_2254_, v_sz_2255_, v_i_2256_, v_b_2257_);
stack->m_obj
 = v_res_2279_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_2280_, lean_object* v_x_2281_, lean_object* v_as_2282_, lean_object* v_sz_2283_, lean_object* v_i_2284_, lean_object* v_b_2285_){
_start:
{
size_t v_sz_boxed_2286_; size_t v_i_boxed_2287_; lean_object* v_res_2288_; 
v_sz_boxed_2286_ = lean_unbox_usize(v_sz_2283_);
lean_dec(v_sz_2283_);
v_i_boxed_2287_ = lean_unbox_usize(v_i_2284_);
lean_dec(v_i_2284_);
v_res_2288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2280_, v_x_2281_, v_as_2282_, v_sz_boxed_2286_, v_i_boxed_2287_, v_b_2285_);
lean_dec_ref(v_as_2282_);
lean_dec(v_x_2281_);
lean_dec_ref(v_init_2280_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_2289_, lean_object* v_x_2290_, lean_object* v_n_2291_, lean_object* v_b_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2289_, v_x_2290_, v_n_2291_, v_b_2292_);
lean_dec_ref(v_n_2291_);
lean_dec(v_x_2290_);
lean_dec_ref(v_init_2289_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(lean_object* v_x_2294_, lean_object* v_t_2295_, lean_object* v_init_2296_){
_start:
{
lean_object* v_root_2297_; lean_object* v_tail_2298_; lean_object* v___x_2299_; 
v_root_2297_ = lean_ctor_get(v_t_2295_, 0);
v_tail_2298_ = lean_ctor_get(v_t_2295_, 1);
lean_inc_ref(v_init_2296_);
v___x_2299_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2296_, v_x_2294_, v_root_2297_, v_init_2296_);
lean_dec_ref(v_init_2296_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
return v_a_2300_;
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; size_t v_sz_2304_; size_t v___x_2305_; lean_object* v___x_2306_; lean_object* v_fst_2307_; 
v_a_2301_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2301_);
lean_dec_ref_known(v___x_2299_, 1);
v___x_2302_ = lean_box(0);
v___x_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
lean_ctor_set(v___x_2303_, 1, v_a_2301_);
v_sz_2304_ = lean_array_size(v_tail_2298_);
v___x_2305_ = ((size_t)0ULL);
v___x_2306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2294_, v_tail_2298_, v_sz_2304_, v___x_2305_, v___x_2303_);
v_fst_2307_ = lean_ctor_get(v___x_2306_, 0);
if (lean_obj_tag(v_fst_2307_) == 0)
{
lean_object* v_snd_2308_; 
v_snd_2308_ = lean_ctor_get(v___x_2306_, 1);
lean_inc(v_snd_2308_);
lean_dec_ref(v___x_2306_);
return v_snd_2308_;
}
else
{
lean_object* v_val_2309_; 
lean_inc_ref(v_fst_2307_);
lean_dec_ref(v___x_2306_);
v_val_2309_ = lean_ctor_get(v_fst_2307_, 0);
lean_inc(v_val_2309_);
lean_dec_ref_known(v_fst_2307_, 1);
return v_val_2309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0___boxed(lean_object* v_x_2310_, lean_object* v_t_2311_, lean_object* v_init_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2310_, v_t_2311_, v_init_2312_);
lean_dec_ref(v_t_2311_);
lean_dec(v_x_2310_);
return v_res_2313_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2314_ = lean_unsigned_to_nat(32u);
v___x_2315_ = lean_mk_empty_array_with_capacity(v___x_2314_);
v___x_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
return v___x_2316_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1(void){
_start:
{
size_t v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v_cs_x27_2322_; 
v___x_2317_ = ((size_t)5ULL);
v___x_2318_ = lean_unsigned_to_nat(0u);
v___x_2319_ = lean_unsigned_to_nat(32u);
v___x_2320_ = lean_mk_empty_array_with_capacity(v___x_2319_);
v___x_2321_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0);
v_cs_x27_2322_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_2322_, 0, v___x_2321_);
lean_ctor_set(v_cs_x27_2322_, 1, v___x_2320_);
lean_ctor_set(v_cs_x27_2322_, 2, v___x_2318_);
lean_ctor_set(v_cs_x27_2322_, 3, v___x_2318_);
lean_ctor_set_usize(v_cs_x27_2322_, 4, v___x_2317_);
return v_cs_x27_2322_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_2325_; lean_object* v_cs_x27_2326_; lean_object* v___x_2327_; 
v_todo_2325_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2));
v_cs_x27_2326_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v_cs_x27_2326_);
lean_ctor_set(v___x_2327_, 1, v_todo_2325_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(lean_object* v_x_2328_, lean_object* v_cs_2329_){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v_fst_2332_; lean_object* v_snd_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
v___x_2330_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3);
v___x_2331_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2328_, v_cs_2329_, v___x_2330_);
v_fst_2332_ = lean_ctor_get(v___x_2331_, 0);
v_snd_2333_ = lean_ctor_get(v___x_2331_, 1);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2331_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_snd_2333_);
lean_inc(v_fst_2332_);
lean_dec(v___x_2331_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_fst_2332_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v_snd_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___boxed(lean_object* v_x_2341_, lean_object* v_cs_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2341_, v_cs_2342_);
lean_dec_ref(v_cs_2342_);
lean_dec(v_x_2341_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object* v_x_2344_, lean_object* v_cs_2345_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2344_, v_cs_2345_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___boxed(lean_object* v_x_2347_, lean_object* v_cs_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(v_x_2347_, v_cs_2348_);
lean_dec_ref(v_cs_2348_);
lean_dec(v_x_2347_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(lean_object* v_a_2350_, lean_object* v_y_2351_, lean_object* v_fst_2352_, lean_object* v_s_2353_){
_start:
{
lean_object* v_structs_2354_; lean_object* v_typeIdOf_2355_; lean_object* v_exprToStructId_2356_; lean_object* v_exprToStructIdEntries_2357_; lean_object* v_forbiddenNatModules_2358_; lean_object* v_natStructs_2359_; lean_object* v_natTypeIdOf_2360_; lean_object* v_exprToNatStructId_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v_structs_2354_ = lean_ctor_get(v_s_2353_, 0);
v_typeIdOf_2355_ = lean_ctor_get(v_s_2353_, 1);
v_exprToStructId_2356_ = lean_ctor_get(v_s_2353_, 2);
v_exprToStructIdEntries_2357_ = lean_ctor_get(v_s_2353_, 3);
v_forbiddenNatModules_2358_ = lean_ctor_get(v_s_2353_, 4);
v_natStructs_2359_ = lean_ctor_get(v_s_2353_, 5);
v_natTypeIdOf_2360_ = lean_ctor_get(v_s_2353_, 6);
v_exprToNatStructId_2361_ = lean_ctor_get(v_s_2353_, 7);
v___x_2362_ = lean_array_get_size(v_structs_2354_);
v___x_2363_ = lean_nat_dec_lt(v_a_2350_, v___x_2362_);
if (v___x_2363_ == 0)
{
lean_dec_ref(v_fst_2352_);
return v_s_2353_;
}
else
{
lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2425_; 
lean_inc_ref(v_exprToNatStructId_2361_);
lean_inc_ref(v_natTypeIdOf_2360_);
lean_inc_ref(v_natStructs_2359_);
lean_inc_ref(v_forbiddenNatModules_2358_);
lean_inc_ref(v_exprToStructIdEntries_2357_);
lean_inc_ref(v_exprToStructId_2356_);
lean_inc_ref(v_typeIdOf_2355_);
lean_inc_ref(v_structs_2354_);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_s_2353_);
if (v_isSharedCheck_2425_ == 0)
{
lean_object* v_unused_2426_; lean_object* v_unused_2427_; lean_object* v_unused_2428_; lean_object* v_unused_2429_; lean_object* v_unused_2430_; lean_object* v_unused_2431_; lean_object* v_unused_2432_; lean_object* v_unused_2433_; 
v_unused_2426_ = lean_ctor_get(v_s_2353_, 7);
lean_dec(v_unused_2426_);
v_unused_2427_ = lean_ctor_get(v_s_2353_, 6);
lean_dec(v_unused_2427_);
v_unused_2428_ = lean_ctor_get(v_s_2353_, 5);
lean_dec(v_unused_2428_);
v_unused_2429_ = lean_ctor_get(v_s_2353_, 4);
lean_dec(v_unused_2429_);
v_unused_2430_ = lean_ctor_get(v_s_2353_, 3);
lean_dec(v_unused_2430_);
v_unused_2431_ = lean_ctor_get(v_s_2353_, 2);
lean_dec(v_unused_2431_);
v_unused_2432_ = lean_ctor_get(v_s_2353_, 1);
lean_dec(v_unused_2432_);
v_unused_2433_ = lean_ctor_get(v_s_2353_, 0);
lean_dec(v_unused_2433_);
v___x_2365_ = v_s_2353_;
v_isShared_2366_ = v_isSharedCheck_2425_;
goto v_resetjp_2364_;
}
else
{
lean_dec(v_s_2353_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2425_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v_v_2367_; lean_object* v_id_2368_; lean_object* v_ringId_x3f_2369_; lean_object* v_type_2370_; lean_object* v_u_2371_; lean_object* v_intModuleInst_2372_; lean_object* v_leInst_x3f_2373_; lean_object* v_ltInst_x3f_2374_; lean_object* v_lawfulOrderLTInst_x3f_2375_; lean_object* v_isPreorderInst_x3f_2376_; lean_object* v_orderedAddInst_x3f_2377_; lean_object* v_isLinearInst_x3f_2378_; lean_object* v_noNatDivInst_x3f_2379_; lean_object* v_ringInst_x3f_2380_; lean_object* v_commRingInst_x3f_2381_; lean_object* v_orderedRingInst_x3f_2382_; lean_object* v_fieldInst_x3f_2383_; lean_object* v_charInst_x3f_2384_; lean_object* v_zero_2385_; lean_object* v_ofNatZero_2386_; lean_object* v_one_x3f_2387_; lean_object* v_leFn_x3f_2388_; lean_object* v_ltFn_x3f_2389_; lean_object* v_addFn_2390_; lean_object* v_zsmulFn_2391_; lean_object* v_nsmulFn_2392_; lean_object* v_zsmulFn_x3f_2393_; lean_object* v_nsmulFn_x3f_2394_; lean_object* v_homomulFn_x3f_2395_; lean_object* v_subFn_2396_; lean_object* v_negFn_2397_; lean_object* v_vars_2398_; lean_object* v_varMap_2399_; lean_object* v_lowers_2400_; lean_object* v_uppers_2401_; lean_object* v_diseqs_2402_; lean_object* v_assignment_2403_; uint8_t v_caseSplits_2404_; lean_object* v_conflict_x3f_2405_; lean_object* v_diseqSplits_2406_; lean_object* v_elimEqs_2407_; lean_object* v_elimStack_2408_; lean_object* v_occurs_2409_; lean_object* v_ignored_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2424_; 
v_v_2367_ = lean_array_fget(v_structs_2354_, v_a_2350_);
v_id_2368_ = lean_ctor_get(v_v_2367_, 0);
v_ringId_x3f_2369_ = lean_ctor_get(v_v_2367_, 1);
v_type_2370_ = lean_ctor_get(v_v_2367_, 2);
v_u_2371_ = lean_ctor_get(v_v_2367_, 3);
v_intModuleInst_2372_ = lean_ctor_get(v_v_2367_, 4);
v_leInst_x3f_2373_ = lean_ctor_get(v_v_2367_, 5);
v_ltInst_x3f_2374_ = lean_ctor_get(v_v_2367_, 6);
v_lawfulOrderLTInst_x3f_2375_ = lean_ctor_get(v_v_2367_, 7);
v_isPreorderInst_x3f_2376_ = lean_ctor_get(v_v_2367_, 8);
v_orderedAddInst_x3f_2377_ = lean_ctor_get(v_v_2367_, 9);
v_isLinearInst_x3f_2378_ = lean_ctor_get(v_v_2367_, 10);
v_noNatDivInst_x3f_2379_ = lean_ctor_get(v_v_2367_, 11);
v_ringInst_x3f_2380_ = lean_ctor_get(v_v_2367_, 12);
v_commRingInst_x3f_2381_ = lean_ctor_get(v_v_2367_, 13);
v_orderedRingInst_x3f_2382_ = lean_ctor_get(v_v_2367_, 14);
v_fieldInst_x3f_2383_ = lean_ctor_get(v_v_2367_, 15);
v_charInst_x3f_2384_ = lean_ctor_get(v_v_2367_, 16);
v_zero_2385_ = lean_ctor_get(v_v_2367_, 17);
v_ofNatZero_2386_ = lean_ctor_get(v_v_2367_, 18);
v_one_x3f_2387_ = lean_ctor_get(v_v_2367_, 19);
v_leFn_x3f_2388_ = lean_ctor_get(v_v_2367_, 20);
v_ltFn_x3f_2389_ = lean_ctor_get(v_v_2367_, 21);
v_addFn_2390_ = lean_ctor_get(v_v_2367_, 22);
v_zsmulFn_2391_ = lean_ctor_get(v_v_2367_, 23);
v_nsmulFn_2392_ = lean_ctor_get(v_v_2367_, 24);
v_zsmulFn_x3f_2393_ = lean_ctor_get(v_v_2367_, 25);
v_nsmulFn_x3f_2394_ = lean_ctor_get(v_v_2367_, 26);
v_homomulFn_x3f_2395_ = lean_ctor_get(v_v_2367_, 27);
v_subFn_2396_ = lean_ctor_get(v_v_2367_, 28);
v_negFn_2397_ = lean_ctor_get(v_v_2367_, 29);
v_vars_2398_ = lean_ctor_get(v_v_2367_, 30);
v_varMap_2399_ = lean_ctor_get(v_v_2367_, 31);
v_lowers_2400_ = lean_ctor_get(v_v_2367_, 32);
v_uppers_2401_ = lean_ctor_get(v_v_2367_, 33);
v_diseqs_2402_ = lean_ctor_get(v_v_2367_, 34);
v_assignment_2403_ = lean_ctor_get(v_v_2367_, 35);
v_caseSplits_2404_ = lean_ctor_get_uint8(v_v_2367_, sizeof(void*)*42);
v_conflict_x3f_2405_ = lean_ctor_get(v_v_2367_, 36);
v_diseqSplits_2406_ = lean_ctor_get(v_v_2367_, 37);
v_elimEqs_2407_ = lean_ctor_get(v_v_2367_, 38);
v_elimStack_2408_ = lean_ctor_get(v_v_2367_, 39);
v_occurs_2409_ = lean_ctor_get(v_v_2367_, 40);
v_ignored_2410_ = lean_ctor_get(v_v_2367_, 41);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_v_2367_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2412_ = v_v_2367_;
v_isShared_2413_ = v_isSharedCheck_2424_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_ignored_2410_);
lean_inc(v_occurs_2409_);
lean_inc(v_elimStack_2408_);
lean_inc(v_elimEqs_2407_);
lean_inc(v_diseqSplits_2406_);
lean_inc(v_conflict_x3f_2405_);
lean_inc(v_assignment_2403_);
lean_inc(v_diseqs_2402_);
lean_inc(v_uppers_2401_);
lean_inc(v_lowers_2400_);
lean_inc(v_varMap_2399_);
lean_inc(v_vars_2398_);
lean_inc(v_negFn_2397_);
lean_inc(v_subFn_2396_);
lean_inc(v_homomulFn_x3f_2395_);
lean_inc(v_nsmulFn_x3f_2394_);
lean_inc(v_zsmulFn_x3f_2393_);
lean_inc(v_nsmulFn_2392_);
lean_inc(v_zsmulFn_2391_);
lean_inc(v_addFn_2390_);
lean_inc(v_ltFn_x3f_2389_);
lean_inc(v_leFn_x3f_2388_);
lean_inc(v_one_x3f_2387_);
lean_inc(v_ofNatZero_2386_);
lean_inc(v_zero_2385_);
lean_inc(v_charInst_x3f_2384_);
lean_inc(v_fieldInst_x3f_2383_);
lean_inc(v_orderedRingInst_x3f_2382_);
lean_inc(v_commRingInst_x3f_2381_);
lean_inc(v_ringInst_x3f_2380_);
lean_inc(v_noNatDivInst_x3f_2379_);
lean_inc(v_isLinearInst_x3f_2378_);
lean_inc(v_orderedAddInst_x3f_2377_);
lean_inc(v_isPreorderInst_x3f_2376_);
lean_inc(v_lawfulOrderLTInst_x3f_2375_);
lean_inc(v_ltInst_x3f_2374_);
lean_inc(v_leInst_x3f_2373_);
lean_inc(v_intModuleInst_2372_);
lean_inc(v_u_2371_);
lean_inc(v_type_2370_);
lean_inc(v_ringId_x3f_2369_);
lean_inc(v_id_2368_);
lean_dec(v_v_2367_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2424_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v_xs_x27_2415_; lean_object* v___x_2416_; lean_object* v___x_2418_; 
v___x_2414_ = lean_box(0);
v_xs_x27_2415_ = lean_array_fset(v_structs_2354_, v_a_2350_, v___x_2414_);
v___x_2416_ = l_Lean_PersistentArray_set___redArg(v_lowers_2400_, v_y_2351_, v_fst_2352_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 32, v___x_2416_);
v___x_2418_ = v___x_2412_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_id_2368_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_ringId_x3f_2369_);
lean_ctor_set(v_reuseFailAlloc_2423_, 2, v_type_2370_);
lean_ctor_set(v_reuseFailAlloc_2423_, 3, v_u_2371_);
lean_ctor_set(v_reuseFailAlloc_2423_, 4, v_intModuleInst_2372_);
lean_ctor_set(v_reuseFailAlloc_2423_, 5, v_leInst_x3f_2373_);
lean_ctor_set(v_reuseFailAlloc_2423_, 6, v_ltInst_x3f_2374_);
lean_ctor_set(v_reuseFailAlloc_2423_, 7, v_lawfulOrderLTInst_x3f_2375_);
lean_ctor_set(v_reuseFailAlloc_2423_, 8, v_isPreorderInst_x3f_2376_);
lean_ctor_set(v_reuseFailAlloc_2423_, 9, v_orderedAddInst_x3f_2377_);
lean_ctor_set(v_reuseFailAlloc_2423_, 10, v_isLinearInst_x3f_2378_);
lean_ctor_set(v_reuseFailAlloc_2423_, 11, v_noNatDivInst_x3f_2379_);
lean_ctor_set(v_reuseFailAlloc_2423_, 12, v_ringInst_x3f_2380_);
lean_ctor_set(v_reuseFailAlloc_2423_, 13, v_commRingInst_x3f_2381_);
lean_ctor_set(v_reuseFailAlloc_2423_, 14, v_orderedRingInst_x3f_2382_);
lean_ctor_set(v_reuseFailAlloc_2423_, 15, v_fieldInst_x3f_2383_);
lean_ctor_set(v_reuseFailAlloc_2423_, 16, v_charInst_x3f_2384_);
lean_ctor_set(v_reuseFailAlloc_2423_, 17, v_zero_2385_);
lean_ctor_set(v_reuseFailAlloc_2423_, 18, v_ofNatZero_2386_);
lean_ctor_set(v_reuseFailAlloc_2423_, 19, v_one_x3f_2387_);
lean_ctor_set(v_reuseFailAlloc_2423_, 20, v_leFn_x3f_2388_);
lean_ctor_set(v_reuseFailAlloc_2423_, 21, v_ltFn_x3f_2389_);
lean_ctor_set(v_reuseFailAlloc_2423_, 22, v_addFn_2390_);
lean_ctor_set(v_reuseFailAlloc_2423_, 23, v_zsmulFn_2391_);
lean_ctor_set(v_reuseFailAlloc_2423_, 24, v_nsmulFn_2392_);
lean_ctor_set(v_reuseFailAlloc_2423_, 25, v_zsmulFn_x3f_2393_);
lean_ctor_set(v_reuseFailAlloc_2423_, 26, v_nsmulFn_x3f_2394_);
lean_ctor_set(v_reuseFailAlloc_2423_, 27, v_homomulFn_x3f_2395_);
lean_ctor_set(v_reuseFailAlloc_2423_, 28, v_subFn_2396_);
lean_ctor_set(v_reuseFailAlloc_2423_, 29, v_negFn_2397_);
lean_ctor_set(v_reuseFailAlloc_2423_, 30, v_vars_2398_);
lean_ctor_set(v_reuseFailAlloc_2423_, 31, v_varMap_2399_);
lean_ctor_set(v_reuseFailAlloc_2423_, 32, v___x_2416_);
lean_ctor_set(v_reuseFailAlloc_2423_, 33, v_uppers_2401_);
lean_ctor_set(v_reuseFailAlloc_2423_, 34, v_diseqs_2402_);
lean_ctor_set(v_reuseFailAlloc_2423_, 35, v_assignment_2403_);
lean_ctor_set(v_reuseFailAlloc_2423_, 36, v_conflict_x3f_2405_);
lean_ctor_set(v_reuseFailAlloc_2423_, 37, v_diseqSplits_2406_);
lean_ctor_set(v_reuseFailAlloc_2423_, 38, v_elimEqs_2407_);
lean_ctor_set(v_reuseFailAlloc_2423_, 39, v_elimStack_2408_);
lean_ctor_set(v_reuseFailAlloc_2423_, 40, v_occurs_2409_);
lean_ctor_set(v_reuseFailAlloc_2423_, 41, v_ignored_2410_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*42, v_caseSplits_2404_);
v___x_2418_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2419_ = lean_array_fset(v_xs_x27_2415_, v_a_2350_, v___x_2418_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2419_);
v___x_2421_ = v___x_2365_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_typeIdOf_2355_);
lean_ctor_set(v_reuseFailAlloc_2422_, 2, v_exprToStructId_2356_);
lean_ctor_set(v_reuseFailAlloc_2422_, 3, v_exprToStructIdEntries_2357_);
lean_ctor_set(v_reuseFailAlloc_2422_, 4, v_forbiddenNatModules_2358_);
lean_ctor_set(v_reuseFailAlloc_2422_, 5, v_natStructs_2359_);
lean_ctor_set(v_reuseFailAlloc_2422_, 6, v_natTypeIdOf_2360_);
lean_ctor_set(v_reuseFailAlloc_2422_, 7, v_exprToNatStructId_2361_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed(lean_object* v_a_2434_, lean_object* v_y_2435_, lean_object* v_fst_2436_, lean_object* v_s_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(v_a_2434_, v_y_2435_, v_fst_2436_, v_s_2437_);
lean_dec(v_y_2435_);
lean_dec(v_a_2434_);
return v_res_2438_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0(void){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_2439_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object* v_a_2440_, lean_object* v_x_2441_, lean_object* v_c_2442_, lean_object* v_y_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2457_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2491_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2460_ = v___x_2457_;
v_isShared_2461_ = v_isSharedCheck_2491_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2457_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2491_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
uint8_t v___x_2462_; 
v___x_2462_ = lean_unbox(v_a_2458_);
lean_dec(v_a_2458_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; 
lean_del_object(v___x_2460_);
v___x_2463_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___y_2466_; lean_object* v_lowers_2474_; lean_object* v_size_2475_; uint8_t v___x_2476_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2464_);
lean_dec_ref_known(v___x_2463_, 1);
v_lowers_2474_ = lean_ctor_get(v_a_2464_, 32);
lean_inc_ref(v_lowers_2474_);
lean_dec(v_a_2464_);
v_size_2475_ = lean_ctor_get(v_lowers_2474_, 2);
v___x_2476_ = lean_nat_dec_lt(v_y_2443_, v_size_2475_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; 
lean_dec_ref(v_lowers_2474_);
v___x_2477_ = l_outOfBounds___redArg(v___x_2456_);
v___y_2466_ = v___x_2477_;
goto v___jp_2465_;
}
else
{
lean_object* v___x_2478_; 
v___x_2478_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2456_, v_lowers_2474_, v_y_2443_);
lean_dec_ref(v_lowers_2474_);
v___y_2466_ = v___x_2478_;
goto v___jp_2465_;
}
v___jp_2465_:
{
lean_object* v___x_2467_; lean_object* v_fst_2468_; lean_object* v_snd_2469_; lean_object* v___f_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2467_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2441_, v___y_2466_);
lean_dec_ref(v___y_2466_);
v_fst_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_fst_2468_);
v_snd_2469_ = lean_ctor_get(v___x_2467_, 1);
lean_inc(v_snd_2469_);
lean_dec_ref(v___x_2467_);
lean_inc(v_a_2444_);
v___f_2470_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2470_, 0, v_a_2444_);
lean_closure_set(v___f_2470_, 1, v_y_2443_);
lean_closure_set(v___f_2470_, 2, v_fst_2468_);
v___x_2471_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2472_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2471_, v___f_2470_, v_a_2445_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v___x_2473_; 
lean_dec_ref_known(v___x_2472_, 1);
v___x_2473_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2440_, v_x_2441_, v_c_2442_, v_snd_2469_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
lean_dec(v_snd_2469_);
return v___x_2473_;
}
else
{
lean_dec(v_snd_2469_);
lean_dec_ref(v_c_2442_);
lean_dec(v_x_2441_);
lean_dec(v_a_2440_);
return v___x_2472_;
}
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec(v_y_2443_);
lean_dec_ref(v_c_2442_);
lean_dec(v_x_2441_);
lean_dec(v_a_2440_);
v_a_2479_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2463_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2463_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
else
{
lean_object* v___x_2487_; lean_object* v___x_2489_; 
lean_dec(v_y_2443_);
lean_dec_ref(v_c_2442_);
lean_dec(v_x_2441_);
lean_dec(v_a_2440_);
v___x_2487_ = lean_box(0);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v___x_2487_);
v___x_2489_ = v___x_2460_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2487_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
else
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2499_; 
lean_dec(v_y_2443_);
lean_dec_ref(v_c_2442_);
lean_dec(v_x_2441_);
lean_dec(v_a_2440_);
v_a_2492_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2494_ = v___x_2457_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2457_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2497_; 
if (v_isShared_2495_ == 0)
{
v___x_2497_ = v___x_2494_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2492_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2440_ = stack[0].m_obj;
lean_object* v_x_2441_ = stack[1].m_obj;
lean_object* v_c_2442_ = stack[2].m_obj;
lean_object* v_y_2443_ = stack[3].m_obj;
lean_object* v_a_2444_ = stack[4].m_obj;
lean_object* v_a_2445_ = stack[5].m_obj;
lean_object* v_a_2446_ = stack[6].m_obj;
lean_object* v_a_2447_ = stack[7].m_obj;
lean_object* v_a_2448_ = stack[8].m_obj;
lean_object* v_a_2449_ = stack[9].m_obj;
lean_object* v_a_2450_ = stack[10].m_obj;
lean_object* v_a_2451_ = stack[11].m_obj;
lean_object* v_a_2452_ = stack[12].m_obj;
lean_object* v_a_2453_ = stack[13].m_obj;
lean_object* v_a_2454_ = stack[14].m_obj;
lean_object* v_res_2500_;
v_res_2500_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_2440_, v_x_2441_, v_c_2442_, v_y_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
stack->m_obj
 = v_res_2500_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object* v_a_2501_, lean_object* v_x_2502_, lean_object* v_c_2503_, lean_object* v_y_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_2501_, v_x_2502_, v_c_2503_, v_y_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec(v_a_2513_);
lean_dec_ref(v_a_2512_);
lean_dec(v_a_2511_);
lean_dec_ref(v_a_2510_);
lean_dec(v_a_2509_);
lean_dec_ref(v_a_2508_);
lean_dec(v_a_2507_);
lean_dec(v_a_2506_);
lean_dec(v_a_2505_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(lean_object* v_a_2518_, lean_object* v_y_2519_, lean_object* v_fst_2520_, lean_object* v_s_2521_){
_start:
{
lean_object* v_structs_2522_; lean_object* v_typeIdOf_2523_; lean_object* v_exprToStructId_2524_; lean_object* v_exprToStructIdEntries_2525_; lean_object* v_forbiddenNatModules_2526_; lean_object* v_natStructs_2527_; lean_object* v_natTypeIdOf_2528_; lean_object* v_exprToNatStructId_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v_structs_2522_ = lean_ctor_get(v_s_2521_, 0);
v_typeIdOf_2523_ = lean_ctor_get(v_s_2521_, 1);
v_exprToStructId_2524_ = lean_ctor_get(v_s_2521_, 2);
v_exprToStructIdEntries_2525_ = lean_ctor_get(v_s_2521_, 3);
v_forbiddenNatModules_2526_ = lean_ctor_get(v_s_2521_, 4);
v_natStructs_2527_ = lean_ctor_get(v_s_2521_, 5);
v_natTypeIdOf_2528_ = lean_ctor_get(v_s_2521_, 6);
v_exprToNatStructId_2529_ = lean_ctor_get(v_s_2521_, 7);
v___x_2530_ = lean_array_get_size(v_structs_2522_);
v___x_2531_ = lean_nat_dec_lt(v_a_2518_, v___x_2530_);
if (v___x_2531_ == 0)
{
lean_dec_ref(v_fst_2520_);
return v_s_2521_;
}
else
{
lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2593_; 
lean_inc_ref(v_exprToNatStructId_2529_);
lean_inc_ref(v_natTypeIdOf_2528_);
lean_inc_ref(v_natStructs_2527_);
lean_inc_ref(v_forbiddenNatModules_2526_);
lean_inc_ref(v_exprToStructIdEntries_2525_);
lean_inc_ref(v_exprToStructId_2524_);
lean_inc_ref(v_typeIdOf_2523_);
lean_inc_ref(v_structs_2522_);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_s_2521_);
if (v_isSharedCheck_2593_ == 0)
{
lean_object* v_unused_2594_; lean_object* v_unused_2595_; lean_object* v_unused_2596_; lean_object* v_unused_2597_; lean_object* v_unused_2598_; lean_object* v_unused_2599_; lean_object* v_unused_2600_; lean_object* v_unused_2601_; 
v_unused_2594_ = lean_ctor_get(v_s_2521_, 7);
lean_dec(v_unused_2594_);
v_unused_2595_ = lean_ctor_get(v_s_2521_, 6);
lean_dec(v_unused_2595_);
v_unused_2596_ = lean_ctor_get(v_s_2521_, 5);
lean_dec(v_unused_2596_);
v_unused_2597_ = lean_ctor_get(v_s_2521_, 4);
lean_dec(v_unused_2597_);
v_unused_2598_ = lean_ctor_get(v_s_2521_, 3);
lean_dec(v_unused_2598_);
v_unused_2599_ = lean_ctor_get(v_s_2521_, 2);
lean_dec(v_unused_2599_);
v_unused_2600_ = lean_ctor_get(v_s_2521_, 1);
lean_dec(v_unused_2600_);
v_unused_2601_ = lean_ctor_get(v_s_2521_, 0);
lean_dec(v_unused_2601_);
v___x_2533_ = v_s_2521_;
v_isShared_2534_ = v_isSharedCheck_2593_;
goto v_resetjp_2532_;
}
else
{
lean_dec(v_s_2521_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2593_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v_v_2535_; lean_object* v_id_2536_; lean_object* v_ringId_x3f_2537_; lean_object* v_type_2538_; lean_object* v_u_2539_; lean_object* v_intModuleInst_2540_; lean_object* v_leInst_x3f_2541_; lean_object* v_ltInst_x3f_2542_; lean_object* v_lawfulOrderLTInst_x3f_2543_; lean_object* v_isPreorderInst_x3f_2544_; lean_object* v_orderedAddInst_x3f_2545_; lean_object* v_isLinearInst_x3f_2546_; lean_object* v_noNatDivInst_x3f_2547_; lean_object* v_ringInst_x3f_2548_; lean_object* v_commRingInst_x3f_2549_; lean_object* v_orderedRingInst_x3f_2550_; lean_object* v_fieldInst_x3f_2551_; lean_object* v_charInst_x3f_2552_; lean_object* v_zero_2553_; lean_object* v_ofNatZero_2554_; lean_object* v_one_x3f_2555_; lean_object* v_leFn_x3f_2556_; lean_object* v_ltFn_x3f_2557_; lean_object* v_addFn_2558_; lean_object* v_zsmulFn_2559_; lean_object* v_nsmulFn_2560_; lean_object* v_zsmulFn_x3f_2561_; lean_object* v_nsmulFn_x3f_2562_; lean_object* v_homomulFn_x3f_2563_; lean_object* v_subFn_2564_; lean_object* v_negFn_2565_; lean_object* v_vars_2566_; lean_object* v_varMap_2567_; lean_object* v_lowers_2568_; lean_object* v_uppers_2569_; lean_object* v_diseqs_2570_; lean_object* v_assignment_2571_; uint8_t v_caseSplits_2572_; lean_object* v_conflict_x3f_2573_; lean_object* v_diseqSplits_2574_; lean_object* v_elimEqs_2575_; lean_object* v_elimStack_2576_; lean_object* v_occurs_2577_; lean_object* v_ignored_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2592_; 
v_v_2535_ = lean_array_fget(v_structs_2522_, v_a_2518_);
v_id_2536_ = lean_ctor_get(v_v_2535_, 0);
v_ringId_x3f_2537_ = lean_ctor_get(v_v_2535_, 1);
v_type_2538_ = lean_ctor_get(v_v_2535_, 2);
v_u_2539_ = lean_ctor_get(v_v_2535_, 3);
v_intModuleInst_2540_ = lean_ctor_get(v_v_2535_, 4);
v_leInst_x3f_2541_ = lean_ctor_get(v_v_2535_, 5);
v_ltInst_x3f_2542_ = lean_ctor_get(v_v_2535_, 6);
v_lawfulOrderLTInst_x3f_2543_ = lean_ctor_get(v_v_2535_, 7);
v_isPreorderInst_x3f_2544_ = lean_ctor_get(v_v_2535_, 8);
v_orderedAddInst_x3f_2545_ = lean_ctor_get(v_v_2535_, 9);
v_isLinearInst_x3f_2546_ = lean_ctor_get(v_v_2535_, 10);
v_noNatDivInst_x3f_2547_ = lean_ctor_get(v_v_2535_, 11);
v_ringInst_x3f_2548_ = lean_ctor_get(v_v_2535_, 12);
v_commRingInst_x3f_2549_ = lean_ctor_get(v_v_2535_, 13);
v_orderedRingInst_x3f_2550_ = lean_ctor_get(v_v_2535_, 14);
v_fieldInst_x3f_2551_ = lean_ctor_get(v_v_2535_, 15);
v_charInst_x3f_2552_ = lean_ctor_get(v_v_2535_, 16);
v_zero_2553_ = lean_ctor_get(v_v_2535_, 17);
v_ofNatZero_2554_ = lean_ctor_get(v_v_2535_, 18);
v_one_x3f_2555_ = lean_ctor_get(v_v_2535_, 19);
v_leFn_x3f_2556_ = lean_ctor_get(v_v_2535_, 20);
v_ltFn_x3f_2557_ = lean_ctor_get(v_v_2535_, 21);
v_addFn_2558_ = lean_ctor_get(v_v_2535_, 22);
v_zsmulFn_2559_ = lean_ctor_get(v_v_2535_, 23);
v_nsmulFn_2560_ = lean_ctor_get(v_v_2535_, 24);
v_zsmulFn_x3f_2561_ = lean_ctor_get(v_v_2535_, 25);
v_nsmulFn_x3f_2562_ = lean_ctor_get(v_v_2535_, 26);
v_homomulFn_x3f_2563_ = lean_ctor_get(v_v_2535_, 27);
v_subFn_2564_ = lean_ctor_get(v_v_2535_, 28);
v_negFn_2565_ = lean_ctor_get(v_v_2535_, 29);
v_vars_2566_ = lean_ctor_get(v_v_2535_, 30);
v_varMap_2567_ = lean_ctor_get(v_v_2535_, 31);
v_lowers_2568_ = lean_ctor_get(v_v_2535_, 32);
v_uppers_2569_ = lean_ctor_get(v_v_2535_, 33);
v_diseqs_2570_ = lean_ctor_get(v_v_2535_, 34);
v_assignment_2571_ = lean_ctor_get(v_v_2535_, 35);
v_caseSplits_2572_ = lean_ctor_get_uint8(v_v_2535_, sizeof(void*)*42);
v_conflict_x3f_2573_ = lean_ctor_get(v_v_2535_, 36);
v_diseqSplits_2574_ = lean_ctor_get(v_v_2535_, 37);
v_elimEqs_2575_ = lean_ctor_get(v_v_2535_, 38);
v_elimStack_2576_ = lean_ctor_get(v_v_2535_, 39);
v_occurs_2577_ = lean_ctor_get(v_v_2535_, 40);
v_ignored_2578_ = lean_ctor_get(v_v_2535_, 41);
v_isSharedCheck_2592_ = !lean_is_exclusive(v_v_2535_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2580_ = v_v_2535_;
v_isShared_2581_ = v_isSharedCheck_2592_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_ignored_2578_);
lean_inc(v_occurs_2577_);
lean_inc(v_elimStack_2576_);
lean_inc(v_elimEqs_2575_);
lean_inc(v_diseqSplits_2574_);
lean_inc(v_conflict_x3f_2573_);
lean_inc(v_assignment_2571_);
lean_inc(v_diseqs_2570_);
lean_inc(v_uppers_2569_);
lean_inc(v_lowers_2568_);
lean_inc(v_varMap_2567_);
lean_inc(v_vars_2566_);
lean_inc(v_negFn_2565_);
lean_inc(v_subFn_2564_);
lean_inc(v_homomulFn_x3f_2563_);
lean_inc(v_nsmulFn_x3f_2562_);
lean_inc(v_zsmulFn_x3f_2561_);
lean_inc(v_nsmulFn_2560_);
lean_inc(v_zsmulFn_2559_);
lean_inc(v_addFn_2558_);
lean_inc(v_ltFn_x3f_2557_);
lean_inc(v_leFn_x3f_2556_);
lean_inc(v_one_x3f_2555_);
lean_inc(v_ofNatZero_2554_);
lean_inc(v_zero_2553_);
lean_inc(v_charInst_x3f_2552_);
lean_inc(v_fieldInst_x3f_2551_);
lean_inc(v_orderedRingInst_x3f_2550_);
lean_inc(v_commRingInst_x3f_2549_);
lean_inc(v_ringInst_x3f_2548_);
lean_inc(v_noNatDivInst_x3f_2547_);
lean_inc(v_isLinearInst_x3f_2546_);
lean_inc(v_orderedAddInst_x3f_2545_);
lean_inc(v_isPreorderInst_x3f_2544_);
lean_inc(v_lawfulOrderLTInst_x3f_2543_);
lean_inc(v_ltInst_x3f_2542_);
lean_inc(v_leInst_x3f_2541_);
lean_inc(v_intModuleInst_2540_);
lean_inc(v_u_2539_);
lean_inc(v_type_2538_);
lean_inc(v_ringId_x3f_2537_);
lean_inc(v_id_2536_);
lean_dec(v_v_2535_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2592_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2582_; lean_object* v_xs_x27_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2582_ = lean_box(0);
v_xs_x27_2583_ = lean_array_fset(v_structs_2522_, v_a_2518_, v___x_2582_);
v___x_2584_ = l_Lean_PersistentArray_set___redArg(v_uppers_2569_, v_y_2519_, v_fst_2520_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 33, v___x_2584_);
v___x_2586_ = v___x_2580_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_id_2536_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v_ringId_x3f_2537_);
lean_ctor_set(v_reuseFailAlloc_2591_, 2, v_type_2538_);
lean_ctor_set(v_reuseFailAlloc_2591_, 3, v_u_2539_);
lean_ctor_set(v_reuseFailAlloc_2591_, 4, v_intModuleInst_2540_);
lean_ctor_set(v_reuseFailAlloc_2591_, 5, v_leInst_x3f_2541_);
lean_ctor_set(v_reuseFailAlloc_2591_, 6, v_ltInst_x3f_2542_);
lean_ctor_set(v_reuseFailAlloc_2591_, 7, v_lawfulOrderLTInst_x3f_2543_);
lean_ctor_set(v_reuseFailAlloc_2591_, 8, v_isPreorderInst_x3f_2544_);
lean_ctor_set(v_reuseFailAlloc_2591_, 9, v_orderedAddInst_x3f_2545_);
lean_ctor_set(v_reuseFailAlloc_2591_, 10, v_isLinearInst_x3f_2546_);
lean_ctor_set(v_reuseFailAlloc_2591_, 11, v_noNatDivInst_x3f_2547_);
lean_ctor_set(v_reuseFailAlloc_2591_, 12, v_ringInst_x3f_2548_);
lean_ctor_set(v_reuseFailAlloc_2591_, 13, v_commRingInst_x3f_2549_);
lean_ctor_set(v_reuseFailAlloc_2591_, 14, v_orderedRingInst_x3f_2550_);
lean_ctor_set(v_reuseFailAlloc_2591_, 15, v_fieldInst_x3f_2551_);
lean_ctor_set(v_reuseFailAlloc_2591_, 16, v_charInst_x3f_2552_);
lean_ctor_set(v_reuseFailAlloc_2591_, 17, v_zero_2553_);
lean_ctor_set(v_reuseFailAlloc_2591_, 18, v_ofNatZero_2554_);
lean_ctor_set(v_reuseFailAlloc_2591_, 19, v_one_x3f_2555_);
lean_ctor_set(v_reuseFailAlloc_2591_, 20, v_leFn_x3f_2556_);
lean_ctor_set(v_reuseFailAlloc_2591_, 21, v_ltFn_x3f_2557_);
lean_ctor_set(v_reuseFailAlloc_2591_, 22, v_addFn_2558_);
lean_ctor_set(v_reuseFailAlloc_2591_, 23, v_zsmulFn_2559_);
lean_ctor_set(v_reuseFailAlloc_2591_, 24, v_nsmulFn_2560_);
lean_ctor_set(v_reuseFailAlloc_2591_, 25, v_zsmulFn_x3f_2561_);
lean_ctor_set(v_reuseFailAlloc_2591_, 26, v_nsmulFn_x3f_2562_);
lean_ctor_set(v_reuseFailAlloc_2591_, 27, v_homomulFn_x3f_2563_);
lean_ctor_set(v_reuseFailAlloc_2591_, 28, v_subFn_2564_);
lean_ctor_set(v_reuseFailAlloc_2591_, 29, v_negFn_2565_);
lean_ctor_set(v_reuseFailAlloc_2591_, 30, v_vars_2566_);
lean_ctor_set(v_reuseFailAlloc_2591_, 31, v_varMap_2567_);
lean_ctor_set(v_reuseFailAlloc_2591_, 32, v_lowers_2568_);
lean_ctor_set(v_reuseFailAlloc_2591_, 33, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2591_, 34, v_diseqs_2570_);
lean_ctor_set(v_reuseFailAlloc_2591_, 35, v_assignment_2571_);
lean_ctor_set(v_reuseFailAlloc_2591_, 36, v_conflict_x3f_2573_);
lean_ctor_set(v_reuseFailAlloc_2591_, 37, v_diseqSplits_2574_);
lean_ctor_set(v_reuseFailAlloc_2591_, 38, v_elimEqs_2575_);
lean_ctor_set(v_reuseFailAlloc_2591_, 39, v_elimStack_2576_);
lean_ctor_set(v_reuseFailAlloc_2591_, 40, v_occurs_2577_);
lean_ctor_set(v_reuseFailAlloc_2591_, 41, v_ignored_2578_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, sizeof(void*)*42, v_caseSplits_2572_);
v___x_2586_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
lean_object* v___x_2587_; lean_object* v___x_2589_; 
v___x_2587_ = lean_array_fset(v_xs_x27_2583_, v_a_2518_, v___x_2586_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v___x_2587_);
v___x_2589_ = v___x_2533_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_typeIdOf_2523_);
lean_ctor_set(v_reuseFailAlloc_2590_, 2, v_exprToStructId_2524_);
lean_ctor_set(v_reuseFailAlloc_2590_, 3, v_exprToStructIdEntries_2525_);
lean_ctor_set(v_reuseFailAlloc_2590_, 4, v_forbiddenNatModules_2526_);
lean_ctor_set(v_reuseFailAlloc_2590_, 5, v_natStructs_2527_);
lean_ctor_set(v_reuseFailAlloc_2590_, 6, v_natTypeIdOf_2528_);
lean_ctor_set(v_reuseFailAlloc_2590_, 7, v_exprToNatStructId_2529_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed(lean_object* v_a_2602_, lean_object* v_y_2603_, lean_object* v_fst_2604_, lean_object* v_s_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(v_a_2602_, v_y_2603_, v_fst_2604_, v_s_2605_);
lean_dec(v_y_2603_);
lean_dec(v_a_2602_);
return v_res_2606_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object* v_a_2607_, lean_object* v_x_2608_, lean_object* v_c_2609_, lean_object* v_y_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2624_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2658_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2627_ = v___x_2624_;
v_isShared_2628_ = v_isSharedCheck_2658_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2624_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2658_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
uint8_t v___x_2629_; 
v___x_2629_ = lean_unbox(v_a_2625_);
lean_dec(v_a_2625_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2630_; 
lean_del_object(v___x_2627_);
v___x_2630_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v___y_2633_; lean_object* v_uppers_2641_; lean_object* v_size_2642_; uint8_t v___x_2643_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v___x_2630_, 1);
v_uppers_2641_ = lean_ctor_get(v_a_2631_, 33);
lean_inc_ref(v_uppers_2641_);
lean_dec(v_a_2631_);
v_size_2642_ = lean_ctor_get(v_uppers_2641_, 2);
v___x_2643_ = lean_nat_dec_lt(v_y_2610_, v_size_2642_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; 
lean_dec_ref(v_uppers_2641_);
v___x_2644_ = l_outOfBounds___redArg(v___x_2623_);
v___y_2633_ = v___x_2644_;
goto v___jp_2632_;
}
else
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2623_, v_uppers_2641_, v_y_2610_);
lean_dec_ref(v_uppers_2641_);
v___y_2633_ = v___x_2645_;
goto v___jp_2632_;
}
v___jp_2632_:
{
lean_object* v___x_2634_; lean_object* v_fst_2635_; lean_object* v_snd_2636_; lean_object* v___f_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2634_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2608_, v___y_2633_);
lean_dec_ref(v___y_2633_);
v_fst_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_fst_2635_);
v_snd_2636_ = lean_ctor_get(v___x_2634_, 1);
lean_inc(v_snd_2636_);
lean_dec_ref(v___x_2634_);
lean_inc(v_a_2611_);
v___f_2637_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2637_, 0, v_a_2611_);
lean_closure_set(v___f_2637_, 1, v_y_2610_);
lean_closure_set(v___f_2637_, 2, v_fst_2635_);
v___x_2638_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2639_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2638_, v___f_2637_, v_a_2612_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v___x_2640_; 
lean_dec_ref_known(v___x_2639_, 1);
v___x_2640_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2607_, v_x_2608_, v_c_2609_, v_snd_2636_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_);
lean_dec(v_snd_2636_);
return v___x_2640_;
}
else
{
lean_dec(v_snd_2636_);
lean_dec_ref(v_c_2609_);
lean_dec(v_x_2608_);
lean_dec(v_a_2607_);
return v___x_2639_;
}
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec(v_y_2610_);
lean_dec_ref(v_c_2609_);
lean_dec(v_x_2608_);
lean_dec(v_a_2607_);
v_a_2646_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2630_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2630_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2656_; 
lean_dec(v_y_2610_);
lean_dec_ref(v_c_2609_);
lean_dec(v_x_2608_);
lean_dec(v_a_2607_);
v___x_2654_ = lean_box(0);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v___x_2654_);
v___x_2656_ = v___x_2627_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2654_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
lean_dec(v_y_2610_);
lean_dec_ref(v_c_2609_);
lean_dec(v_x_2608_);
lean_dec(v_a_2607_);
v_a_2659_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2624_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2624_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2607_ = stack[0].m_obj;
lean_object* v_x_2608_ = stack[1].m_obj;
lean_object* v_c_2609_ = stack[2].m_obj;
lean_object* v_y_2610_ = stack[3].m_obj;
lean_object* v_a_2611_ = stack[4].m_obj;
lean_object* v_a_2612_ = stack[5].m_obj;
lean_object* v_a_2613_ = stack[6].m_obj;
lean_object* v_a_2614_ = stack[7].m_obj;
lean_object* v_a_2615_ = stack[8].m_obj;
lean_object* v_a_2616_ = stack[9].m_obj;
lean_object* v_a_2617_ = stack[10].m_obj;
lean_object* v_a_2618_ = stack[11].m_obj;
lean_object* v_a_2619_ = stack[12].m_obj;
lean_object* v_a_2620_ = stack[13].m_obj;
lean_object* v_a_2621_ = stack[14].m_obj;
lean_object* v_res_2667_;
v_res_2667_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_2607_, v_x_2608_, v_c_2609_, v_y_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_);
stack->m_obj
 = v_res_2667_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object* v_a_2668_, lean_object* v_x_2669_, lean_object* v_c_2670_, lean_object* v_y_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_2668_, v_x_2669_, v_c_2670_, v_y_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
lean_dec_ref(v_a_2675_);
lean_dec(v_a_2674_);
lean_dec(v_a_2673_);
lean_dec(v_a_2672_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(lean_object* v___y_2685_, lean_object* v_a_2686_, lean_object* v_s_2687_){
_start:
{
lean_object* v_structs_2688_; lean_object* v_typeIdOf_2689_; lean_object* v_exprToStructId_2690_; lean_object* v_exprToStructIdEntries_2691_; lean_object* v_forbiddenNatModules_2692_; lean_object* v_natStructs_2693_; lean_object* v_natTypeIdOf_2694_; lean_object* v_exprToNatStructId_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v_structs_2688_ = lean_ctor_get(v_s_2687_, 0);
v_typeIdOf_2689_ = lean_ctor_get(v_s_2687_, 1);
v_exprToStructId_2690_ = lean_ctor_get(v_s_2687_, 2);
v_exprToStructIdEntries_2691_ = lean_ctor_get(v_s_2687_, 3);
v_forbiddenNatModules_2692_ = lean_ctor_get(v_s_2687_, 4);
v_natStructs_2693_ = lean_ctor_get(v_s_2687_, 5);
v_natTypeIdOf_2694_ = lean_ctor_get(v_s_2687_, 6);
v_exprToNatStructId_2695_ = lean_ctor_get(v_s_2687_, 7);
v___x_2696_ = lean_array_get_size(v_structs_2688_);
v___x_2697_ = lean_nat_dec_lt(v___y_2685_, v___x_2696_);
if (v___x_2697_ == 0)
{
lean_dec_ref(v_a_2686_);
return v_s_2687_;
}
else
{
lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2759_; 
lean_inc_ref(v_exprToNatStructId_2695_);
lean_inc_ref(v_natTypeIdOf_2694_);
lean_inc_ref(v_natStructs_2693_);
lean_inc_ref(v_forbiddenNatModules_2692_);
lean_inc_ref(v_exprToStructIdEntries_2691_);
lean_inc_ref(v_exprToStructId_2690_);
lean_inc_ref(v_typeIdOf_2689_);
lean_inc_ref(v_structs_2688_);
v_isSharedCheck_2759_ = !lean_is_exclusive(v_s_2687_);
if (v_isSharedCheck_2759_ == 0)
{
lean_object* v_unused_2760_; lean_object* v_unused_2761_; lean_object* v_unused_2762_; lean_object* v_unused_2763_; lean_object* v_unused_2764_; lean_object* v_unused_2765_; lean_object* v_unused_2766_; lean_object* v_unused_2767_; 
v_unused_2760_ = lean_ctor_get(v_s_2687_, 7);
lean_dec(v_unused_2760_);
v_unused_2761_ = lean_ctor_get(v_s_2687_, 6);
lean_dec(v_unused_2761_);
v_unused_2762_ = lean_ctor_get(v_s_2687_, 5);
lean_dec(v_unused_2762_);
v_unused_2763_ = lean_ctor_get(v_s_2687_, 4);
lean_dec(v_unused_2763_);
v_unused_2764_ = lean_ctor_get(v_s_2687_, 3);
lean_dec(v_unused_2764_);
v_unused_2765_ = lean_ctor_get(v_s_2687_, 2);
lean_dec(v_unused_2765_);
v_unused_2766_ = lean_ctor_get(v_s_2687_, 1);
lean_dec(v_unused_2766_);
v_unused_2767_ = lean_ctor_get(v_s_2687_, 0);
lean_dec(v_unused_2767_);
v___x_2699_ = v_s_2687_;
v_isShared_2700_ = v_isSharedCheck_2759_;
goto v_resetjp_2698_;
}
else
{
lean_dec(v_s_2687_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2759_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v_v_2701_; lean_object* v_id_2702_; lean_object* v_ringId_x3f_2703_; lean_object* v_type_2704_; lean_object* v_u_2705_; lean_object* v_intModuleInst_2706_; lean_object* v_leInst_x3f_2707_; lean_object* v_ltInst_x3f_2708_; lean_object* v_lawfulOrderLTInst_x3f_2709_; lean_object* v_isPreorderInst_x3f_2710_; lean_object* v_orderedAddInst_x3f_2711_; lean_object* v_isLinearInst_x3f_2712_; lean_object* v_noNatDivInst_x3f_2713_; lean_object* v_ringInst_x3f_2714_; lean_object* v_commRingInst_x3f_2715_; lean_object* v_orderedRingInst_x3f_2716_; lean_object* v_fieldInst_x3f_2717_; lean_object* v_charInst_x3f_2718_; lean_object* v_zero_2719_; lean_object* v_ofNatZero_2720_; lean_object* v_one_x3f_2721_; lean_object* v_leFn_x3f_2722_; lean_object* v_ltFn_x3f_2723_; lean_object* v_addFn_2724_; lean_object* v_zsmulFn_2725_; lean_object* v_nsmulFn_2726_; lean_object* v_zsmulFn_x3f_2727_; lean_object* v_nsmulFn_x3f_2728_; lean_object* v_homomulFn_x3f_2729_; lean_object* v_subFn_2730_; lean_object* v_negFn_2731_; lean_object* v_vars_2732_; lean_object* v_varMap_2733_; lean_object* v_lowers_2734_; lean_object* v_uppers_2735_; lean_object* v_diseqs_2736_; lean_object* v_assignment_2737_; uint8_t v_caseSplits_2738_; lean_object* v_conflict_x3f_2739_; lean_object* v_diseqSplits_2740_; lean_object* v_elimEqs_2741_; lean_object* v_elimStack_2742_; lean_object* v_occurs_2743_; lean_object* v_ignored_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2758_; 
v_v_2701_ = lean_array_fget(v_structs_2688_, v___y_2685_);
v_id_2702_ = lean_ctor_get(v_v_2701_, 0);
v_ringId_x3f_2703_ = lean_ctor_get(v_v_2701_, 1);
v_type_2704_ = lean_ctor_get(v_v_2701_, 2);
v_u_2705_ = lean_ctor_get(v_v_2701_, 3);
v_intModuleInst_2706_ = lean_ctor_get(v_v_2701_, 4);
v_leInst_x3f_2707_ = lean_ctor_get(v_v_2701_, 5);
v_ltInst_x3f_2708_ = lean_ctor_get(v_v_2701_, 6);
v_lawfulOrderLTInst_x3f_2709_ = lean_ctor_get(v_v_2701_, 7);
v_isPreorderInst_x3f_2710_ = lean_ctor_get(v_v_2701_, 8);
v_orderedAddInst_x3f_2711_ = lean_ctor_get(v_v_2701_, 9);
v_isLinearInst_x3f_2712_ = lean_ctor_get(v_v_2701_, 10);
v_noNatDivInst_x3f_2713_ = lean_ctor_get(v_v_2701_, 11);
v_ringInst_x3f_2714_ = lean_ctor_get(v_v_2701_, 12);
v_commRingInst_x3f_2715_ = lean_ctor_get(v_v_2701_, 13);
v_orderedRingInst_x3f_2716_ = lean_ctor_get(v_v_2701_, 14);
v_fieldInst_x3f_2717_ = lean_ctor_get(v_v_2701_, 15);
v_charInst_x3f_2718_ = lean_ctor_get(v_v_2701_, 16);
v_zero_2719_ = lean_ctor_get(v_v_2701_, 17);
v_ofNatZero_2720_ = lean_ctor_get(v_v_2701_, 18);
v_one_x3f_2721_ = lean_ctor_get(v_v_2701_, 19);
v_leFn_x3f_2722_ = lean_ctor_get(v_v_2701_, 20);
v_ltFn_x3f_2723_ = lean_ctor_get(v_v_2701_, 21);
v_addFn_2724_ = lean_ctor_get(v_v_2701_, 22);
v_zsmulFn_2725_ = lean_ctor_get(v_v_2701_, 23);
v_nsmulFn_2726_ = lean_ctor_get(v_v_2701_, 24);
v_zsmulFn_x3f_2727_ = lean_ctor_get(v_v_2701_, 25);
v_nsmulFn_x3f_2728_ = lean_ctor_get(v_v_2701_, 26);
v_homomulFn_x3f_2729_ = lean_ctor_get(v_v_2701_, 27);
v_subFn_2730_ = lean_ctor_get(v_v_2701_, 28);
v_negFn_2731_ = lean_ctor_get(v_v_2701_, 29);
v_vars_2732_ = lean_ctor_get(v_v_2701_, 30);
v_varMap_2733_ = lean_ctor_get(v_v_2701_, 31);
v_lowers_2734_ = lean_ctor_get(v_v_2701_, 32);
v_uppers_2735_ = lean_ctor_get(v_v_2701_, 33);
v_diseqs_2736_ = lean_ctor_get(v_v_2701_, 34);
v_assignment_2737_ = lean_ctor_get(v_v_2701_, 35);
v_caseSplits_2738_ = lean_ctor_get_uint8(v_v_2701_, sizeof(void*)*42);
v_conflict_x3f_2739_ = lean_ctor_get(v_v_2701_, 36);
v_diseqSplits_2740_ = lean_ctor_get(v_v_2701_, 37);
v_elimEqs_2741_ = lean_ctor_get(v_v_2701_, 38);
v_elimStack_2742_ = lean_ctor_get(v_v_2701_, 39);
v_occurs_2743_ = lean_ctor_get(v_v_2701_, 40);
v_ignored_2744_ = lean_ctor_get(v_v_2701_, 41);
v_isSharedCheck_2758_ = !lean_is_exclusive(v_v_2701_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2746_ = v_v_2701_;
v_isShared_2747_ = v_isSharedCheck_2758_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_ignored_2744_);
lean_inc(v_occurs_2743_);
lean_inc(v_elimStack_2742_);
lean_inc(v_elimEqs_2741_);
lean_inc(v_diseqSplits_2740_);
lean_inc(v_conflict_x3f_2739_);
lean_inc(v_assignment_2737_);
lean_inc(v_diseqs_2736_);
lean_inc(v_uppers_2735_);
lean_inc(v_lowers_2734_);
lean_inc(v_varMap_2733_);
lean_inc(v_vars_2732_);
lean_inc(v_negFn_2731_);
lean_inc(v_subFn_2730_);
lean_inc(v_homomulFn_x3f_2729_);
lean_inc(v_nsmulFn_x3f_2728_);
lean_inc(v_zsmulFn_x3f_2727_);
lean_inc(v_nsmulFn_2726_);
lean_inc(v_zsmulFn_2725_);
lean_inc(v_addFn_2724_);
lean_inc(v_ltFn_x3f_2723_);
lean_inc(v_leFn_x3f_2722_);
lean_inc(v_one_x3f_2721_);
lean_inc(v_ofNatZero_2720_);
lean_inc(v_zero_2719_);
lean_inc(v_charInst_x3f_2718_);
lean_inc(v_fieldInst_x3f_2717_);
lean_inc(v_orderedRingInst_x3f_2716_);
lean_inc(v_commRingInst_x3f_2715_);
lean_inc(v_ringInst_x3f_2714_);
lean_inc(v_noNatDivInst_x3f_2713_);
lean_inc(v_isLinearInst_x3f_2712_);
lean_inc(v_orderedAddInst_x3f_2711_);
lean_inc(v_isPreorderInst_x3f_2710_);
lean_inc(v_lawfulOrderLTInst_x3f_2709_);
lean_inc(v_ltInst_x3f_2708_);
lean_inc(v_leInst_x3f_2707_);
lean_inc(v_intModuleInst_2706_);
lean_inc(v_u_2705_);
lean_inc(v_type_2704_);
lean_inc(v_ringId_x3f_2703_);
lean_inc(v_id_2702_);
lean_dec(v_v_2701_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2758_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2748_; lean_object* v_xs_x27_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2748_ = lean_box(0);
v_xs_x27_2749_ = lean_array_fset(v_structs_2688_, v___y_2685_, v___x_2748_);
v___x_2750_ = l_Lean_PersistentArray_push___redArg(v_ignored_2744_, v_a_2686_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 41, v___x_2750_);
v___x_2752_ = v___x_2746_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_id_2702_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v_ringId_x3f_2703_);
lean_ctor_set(v_reuseFailAlloc_2757_, 2, v_type_2704_);
lean_ctor_set(v_reuseFailAlloc_2757_, 3, v_u_2705_);
lean_ctor_set(v_reuseFailAlloc_2757_, 4, v_intModuleInst_2706_);
lean_ctor_set(v_reuseFailAlloc_2757_, 5, v_leInst_x3f_2707_);
lean_ctor_set(v_reuseFailAlloc_2757_, 6, v_ltInst_x3f_2708_);
lean_ctor_set(v_reuseFailAlloc_2757_, 7, v_lawfulOrderLTInst_x3f_2709_);
lean_ctor_set(v_reuseFailAlloc_2757_, 8, v_isPreorderInst_x3f_2710_);
lean_ctor_set(v_reuseFailAlloc_2757_, 9, v_orderedAddInst_x3f_2711_);
lean_ctor_set(v_reuseFailAlloc_2757_, 10, v_isLinearInst_x3f_2712_);
lean_ctor_set(v_reuseFailAlloc_2757_, 11, v_noNatDivInst_x3f_2713_);
lean_ctor_set(v_reuseFailAlloc_2757_, 12, v_ringInst_x3f_2714_);
lean_ctor_set(v_reuseFailAlloc_2757_, 13, v_commRingInst_x3f_2715_);
lean_ctor_set(v_reuseFailAlloc_2757_, 14, v_orderedRingInst_x3f_2716_);
lean_ctor_set(v_reuseFailAlloc_2757_, 15, v_fieldInst_x3f_2717_);
lean_ctor_set(v_reuseFailAlloc_2757_, 16, v_charInst_x3f_2718_);
lean_ctor_set(v_reuseFailAlloc_2757_, 17, v_zero_2719_);
lean_ctor_set(v_reuseFailAlloc_2757_, 18, v_ofNatZero_2720_);
lean_ctor_set(v_reuseFailAlloc_2757_, 19, v_one_x3f_2721_);
lean_ctor_set(v_reuseFailAlloc_2757_, 20, v_leFn_x3f_2722_);
lean_ctor_set(v_reuseFailAlloc_2757_, 21, v_ltFn_x3f_2723_);
lean_ctor_set(v_reuseFailAlloc_2757_, 22, v_addFn_2724_);
lean_ctor_set(v_reuseFailAlloc_2757_, 23, v_zsmulFn_2725_);
lean_ctor_set(v_reuseFailAlloc_2757_, 24, v_nsmulFn_2726_);
lean_ctor_set(v_reuseFailAlloc_2757_, 25, v_zsmulFn_x3f_2727_);
lean_ctor_set(v_reuseFailAlloc_2757_, 26, v_nsmulFn_x3f_2728_);
lean_ctor_set(v_reuseFailAlloc_2757_, 27, v_homomulFn_x3f_2729_);
lean_ctor_set(v_reuseFailAlloc_2757_, 28, v_subFn_2730_);
lean_ctor_set(v_reuseFailAlloc_2757_, 29, v_negFn_2731_);
lean_ctor_set(v_reuseFailAlloc_2757_, 30, v_vars_2732_);
lean_ctor_set(v_reuseFailAlloc_2757_, 31, v_varMap_2733_);
lean_ctor_set(v_reuseFailAlloc_2757_, 32, v_lowers_2734_);
lean_ctor_set(v_reuseFailAlloc_2757_, 33, v_uppers_2735_);
lean_ctor_set(v_reuseFailAlloc_2757_, 34, v_diseqs_2736_);
lean_ctor_set(v_reuseFailAlloc_2757_, 35, v_assignment_2737_);
lean_ctor_set(v_reuseFailAlloc_2757_, 36, v_conflict_x3f_2739_);
lean_ctor_set(v_reuseFailAlloc_2757_, 37, v_diseqSplits_2740_);
lean_ctor_set(v_reuseFailAlloc_2757_, 38, v_elimEqs_2741_);
lean_ctor_set(v_reuseFailAlloc_2757_, 39, v_elimStack_2742_);
lean_ctor_set(v_reuseFailAlloc_2757_, 40, v_occurs_2743_);
lean_ctor_set(v_reuseFailAlloc_2757_, 41, v___x_2750_);
lean_ctor_set_uint8(v_reuseFailAlloc_2757_, sizeof(void*)*42, v_caseSplits_2738_);
v___x_2752_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; lean_object* v___x_2755_; 
v___x_2753_ = lean_array_fset(v_xs_x27_2749_, v___y_2685_, v___x_2752_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v___x_2753_);
v___x_2755_ = v___x_2699_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
lean_ctor_set(v_reuseFailAlloc_2756_, 1, v_typeIdOf_2689_);
lean_ctor_set(v_reuseFailAlloc_2756_, 2, v_exprToStructId_2690_);
lean_ctor_set(v_reuseFailAlloc_2756_, 3, v_exprToStructIdEntries_2691_);
lean_ctor_set(v_reuseFailAlloc_2756_, 4, v_forbiddenNatModules_2692_);
lean_ctor_set(v_reuseFailAlloc_2756_, 5, v_natStructs_2693_);
lean_ctor_set(v_reuseFailAlloc_2756_, 6, v_natTypeIdOf_2694_);
lean_ctor_set(v_reuseFailAlloc_2756_, 7, v_exprToNatStructId_2695_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed(lean_object* v___y_2768_, lean_object* v_a_2769_, lean_object* v_s_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(v___y_2768_, v_a_2769_, v_s_2770_);
lean_dec(v___y_2768_);
return v_res_2771_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3(void){
_start:
{
lean_object* v_cls_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v_cls_2779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_2781_ = l_Lean_Name_append(v___x_2780_, v_cls_2779_);
return v___x_2781_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object* v_c_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v_toCold_2820_; lean_object* v_options_2821_; uint8_t v_hasTrace_2822_; 
v_toCold_2820_ = lean_ctor_get(v_a_2792_, 0);
v_options_2821_ = lean_ctor_get(v_toCold_2820_, 2);
v_hasTrace_2822_ = lean_ctor_get_uint8(v_options_2821_, sizeof(void*)*1);
if (v_hasTrace_2822_ == 0)
{
v___y_2796_ = v_a_2783_;
v___y_2797_ = v_a_2784_;
v___y_2798_ = v_a_2785_;
v___y_2799_ = v_a_2786_;
v___y_2800_ = v_a_2787_;
v___y_2801_ = v_a_2788_;
v___y_2802_ = v_a_2789_;
v___y_2803_ = v_a_2790_;
v___y_2804_ = v_a_2791_;
v___y_2805_ = v_a_2792_;
v___y_2806_ = v_a_2793_;
goto v___jp_2795_;
}
else
{
lean_object* v_inheritedTraceOptions_2823_; lean_object* v_cls_2824_; lean_object* v___x_2825_; uint8_t v___x_2826_; 
v_inheritedTraceOptions_2823_ = lean_ctor_get(v_toCold_2820_, 11);
v_cls_2824_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2825_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3);
v___x_2826_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2823_, v_options_2821_, v___x_2825_);
if (v___x_2826_ == 0)
{
v___y_2796_ = v_a_2783_;
v___y_2797_ = v_a_2784_;
v___y_2798_ = v_a_2785_;
v___y_2799_ = v_a_2786_;
v___y_2800_ = v_a_2787_;
v___y_2801_ = v_a_2788_;
v___y_2802_ = v_a_2789_;
v___y_2803_ = v_a_2790_;
v___y_2804_ = v_a_2791_;
v___y_2805_ = v_a_2792_;
v___y_2806_ = v_a_2793_;
goto v___jp_2795_;
}
else
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2827_, 1);
v___x_2829_ = l_Lean_MessageData_ofExpr(v_a_2828_);
v___x_2830_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_2824_, v___x_2829_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_dec_ref_known(v___x_2830_, 1);
v___y_2796_ = v_a_2783_;
v___y_2797_ = v_a_2784_;
v___y_2798_ = v_a_2785_;
v___y_2799_ = v_a_2786_;
v___y_2800_ = v_a_2787_;
v___y_2801_ = v_a_2788_;
v___y_2802_ = v_a_2789_;
v___y_2803_ = v_a_2790_;
v___y_2804_ = v_a_2791_;
v___y_2805_ = v_a_2792_;
v___y_2806_ = v_a_2793_;
goto v___jp_2795_;
}
else
{
return v___x_2830_;
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
v_a_2831_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2827_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2827_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
}
v___jp_2795_:
{
lean_object* v___x_2807_; 
v___x_2807_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2782_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___f_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
lean_inc(v___y_2796_);
v___f_2809_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2809_, 0, v___y_2796_);
lean_closure_set(v___f_2809_, 1, v_a_2808_);
v___x_2810_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2811_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2810_, v___f_2809_, v___y_2797_);
return v___x_2811_;
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
v_a_2812_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2807_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2807_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2782_ = stack[0].m_obj;
lean_object* v_a_2783_ = stack[1].m_obj;
lean_object* v_a_2784_ = stack[2].m_obj;
lean_object* v_a_2785_ = stack[3].m_obj;
lean_object* v_a_2786_ = stack[4].m_obj;
lean_object* v_a_2787_ = stack[5].m_obj;
lean_object* v_a_2788_ = stack[6].m_obj;
lean_object* v_a_2789_ = stack[7].m_obj;
lean_object* v_a_2790_ = stack[8].m_obj;
lean_object* v_a_2791_ = stack[9].m_obj;
lean_object* v_a_2792_ = stack[10].m_obj;
lean_object* v_a_2793_ = stack[11].m_obj;
lean_object* v_res_2839_;
v_res_2839_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
stack->m_obj
 = v_res_2839_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object* v_c_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
lean_dec(v_a_2847_);
lean_dec_ref(v_a_2846_);
lean_dec(v_a_2845_);
lean_dec_ref(v_a_2844_);
lean_dec(v_a_2843_);
lean_dec(v_a_2842_);
lean_dec(v_a_2841_);
lean_dec_ref(v_c_2840_);
return v_res_2853_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object* v_c_u2082_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_){
_start:
{
lean_object* v_p_2867_; lean_object* v_toCold_2868_; lean_object* v_currRecDepth_2869_; lean_object* v_ref_2870_; uint16_t v_optionFlags_2871_; uint8_t v_suppressElabErrors_2872_; uint8_t v_isRecordingDeps_2873_; lean_object* v_maxRecDepth_2925_; lean_object* v___x_2926_; uint8_t v___x_2927_; 
v_p_2867_ = lean_ctor_get(v_c_u2082_2854_, 0);
v_toCold_2868_ = lean_ctor_get(v_a_2864_, 0);
lean_inc_ref(v_toCold_2868_);
v_currRecDepth_2869_ = lean_ctor_get(v_a_2864_, 1);
lean_inc(v_currRecDepth_2869_);
v_ref_2870_ = lean_ctor_get(v_a_2864_, 2);
lean_inc(v_ref_2870_);
v_optionFlags_2871_ = lean_ctor_get_uint16(v_a_2864_, sizeof(void*)*3);
v_suppressElabErrors_2872_ = lean_ctor_get_uint8(v_a_2864_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2873_ = lean_ctor_get_uint8(v_a_2864_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_2864_);
v_maxRecDepth_2925_ = lean_ctor_get(v_toCold_2868_, 3);
v___x_2926_ = lean_unsigned_to_nat(0u);
v___x_2927_ = lean_nat_dec_eq(v_maxRecDepth_2925_, v___x_2926_);
if (v___x_2927_ == 0)
{
uint8_t v___x_2928_; 
v___x_2928_ = lean_nat_dec_eq(v_currRecDepth_2869_, v_maxRecDepth_2925_);
if (v___x_2928_ == 0)
{
goto v___jp_2874_;
}
else
{
lean_object* v___x_2929_; 
lean_dec(v_currRecDepth_2869_);
lean_dec_ref(v_toCold_2868_);
lean_dec_ref(v_c_u2082_2854_);
v___x_2929_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_2870_);
return v___x_2929_;
}
}
else
{
goto v___jp_2874_;
}
v___jp_2874_:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2875_ = lean_unsigned_to_nat(1u);
v___x_2876_ = lean_nat_add(v_currRecDepth_2869_, v___x_2875_);
lean_dec(v_currRecDepth_2869_);
v___x_2877_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2877_, 0, v_toCold_2868_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
lean_ctor_set(v___x_2877_, 2, v_ref_2870_);
lean_ctor_set_uint16(v___x_2877_, sizeof(void*)*3, v_optionFlags_2871_);
lean_ctor_set_uint8(v___x_2877_, sizeof(void*)*3 + 2, v_suppressElabErrors_2872_);
lean_ctor_set_uint8(v___x_2877_, sizeof(void*)*3 + 3, v_isRecordingDeps_2873_);
v___x_2878_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2867_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v___x_2877_, v_a_2865_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2916_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2881_ = v___x_2878_;
v_isShared_2882_ = v_isSharedCheck_2916_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2878_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2916_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
if (lean_obj_tag(v_a_2879_) == 1)
{
lean_object* v_val_2883_; lean_object* v_snd_2884_; lean_object* v_snd_2885_; lean_object* v_fst_2886_; lean_object* v_fst_2887_; lean_object* v_p_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
lean_del_object(v___x_2881_);
v_val_2883_ = lean_ctor_get(v_a_2879_, 0);
lean_inc(v_val_2883_);
lean_dec_ref_known(v_a_2879_, 1);
v_snd_2884_ = lean_ctor_get(v_val_2883_, 1);
lean_inc(v_snd_2884_);
v_snd_2885_ = lean_ctor_get(v_snd_2884_, 1);
lean_inc(v_snd_2885_);
v_fst_2886_ = lean_ctor_get(v_val_2883_, 0);
lean_inc(v_fst_2886_);
lean_dec(v_val_2883_);
v_fst_2887_ = lean_ctor_get(v_snd_2884_, 0);
lean_inc(v_fst_2887_);
lean_dec(v_snd_2884_);
v_p_2888_ = lean_ctor_get(v_snd_2885_, 0);
v___x_2889_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2888_, v_fst_2887_);
lean_inc_ref(v_c_u2082_2854_);
v___x_2890_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v___x_2889_, v_fst_2887_, v_snd_2885_, v_fst_2886_, v_c_u2082_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v___x_2877_, v_a_2865_);
lean_dec(v_fst_2887_);
lean_dec(v___x_2889_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref_known(v___x_2890_, 1);
if (lean_obj_tag(v_a_2891_) == 1)
{
lean_object* v_val_2892_; 
lean_dec_ref(v_c_u2082_2854_);
v_val_2892_ = lean_ctor_get(v_a_2891_, 0);
lean_inc(v_val_2892_);
lean_dec_ref_known(v_a_2891_, 1);
v_c_u2082_2854_ = v_val_2892_;
v_a_2864_ = v___x_2877_;
goto _start;
}
else
{
lean_object* v___x_2894_; 
lean_dec(v_a_2891_);
v___x_2894_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_u2082_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v___x_2877_, v_a_2865_);
lean_dec_ref_known(v___x_2877_, 3);
lean_dec_ref(v_c_u2082_2854_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2902_; 
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2902_ == 0)
{
lean_object* v_unused_2903_; 
v_unused_2903_ = lean_ctor_get(v___x_2894_, 0);
lean_dec(v_unused_2903_);
v___x_2896_ = v___x_2894_;
v_isShared_2897_ = v_isSharedCheck_2902_;
goto v_resetjp_2895_;
}
else
{
lean_dec(v___x_2894_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2902_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2898_; lean_object* v___x_2900_; 
v___x_2898_ = lean_box(0);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v___x_2898_);
v___x_2900_ = v___x_2896_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2898_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
v_a_2904_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2894_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2894_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2877_, 3);
lean_dec_ref(v_c_u2082_2854_);
return v___x_2890_;
}
}
else
{
lean_object* v___x_2912_; lean_object* v___x_2914_; 
lean_dec(v_a_2879_);
lean_dec_ref_known(v___x_2877_, 3);
v___x_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2912_, 0, v_c_u2082_2854_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v___x_2912_);
v___x_2914_ = v___x_2881_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec_ref_known(v___x_2877_, 3);
lean_dec_ref(v_c_u2082_2854_);
v_a_2917_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2878_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2878_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_u2082_2854_ = stack[0].m_obj;
lean_object* v_a_2855_ = stack[1].m_obj;
lean_object* v_a_2856_ = stack[2].m_obj;
lean_object* v_a_2857_ = stack[3].m_obj;
lean_object* v_a_2858_ = stack[4].m_obj;
lean_object* v_a_2859_ = stack[5].m_obj;
lean_object* v_a_2860_ = stack[6].m_obj;
lean_object* v_a_2861_ = stack[7].m_obj;
lean_object* v_a_2862_ = stack[8].m_obj;
lean_object* v_a_2863_ = stack[9].m_obj;
lean_object* v_a_2864_ = stack[10].m_obj;
lean_object* v_a_2865_ = stack[11].m_obj;
lean_object* v_res_2930_;
v_res_2930_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_u2082_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_);
stack->m_obj
 = v_res_2930_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object* v_c_u2082_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_u2082_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
lean_dec(v_a_2942_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
lean_dec(v_a_2938_);
lean_dec_ref(v_a_2937_);
lean_dec(v_a_2936_);
lean_dec_ref(v_a_2935_);
lean_dec(v_a_2934_);
lean_dec(v_a_2933_);
lean_dec(v_a_2932_);
return v_res_2944_;
}
}
lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object* v_val_2945_, lean_object* v_x_2946_, size_t v_x_2947_, size_t v_x_2948_){
_start:
{
if (lean_obj_tag(v_x_2946_) == 0)
{
lean_object* v_cs_2949_; size_t v_j_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; uint8_t v___x_2953_; 
v_cs_2949_ = lean_ctor_get(v_x_2946_, 0);
v_j_2950_ = lean_usize_shift_right(v_x_2947_, v_x_2948_);
v___x_2951_ = lean_usize_to_nat(v_j_2950_);
v___x_2952_ = lean_array_get_size(v_cs_2949_);
v___x_2953_ = lean_nat_dec_lt(v___x_2951_, v___x_2952_);
if (v___x_2953_ == 0)
{
lean_dec(v___x_2951_);
lean_dec_ref(v_val_2945_);
return v_x_2946_;
}
else
{
lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2971_; 
lean_inc_ref(v_cs_2949_);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_x_2946_);
if (v_isSharedCheck_2971_ == 0)
{
lean_object* v_unused_2972_; 
v_unused_2972_ = lean_ctor_get(v_x_2946_, 0);
lean_dec(v_unused_2972_);
v___x_2955_ = v_x_2946_;
v_isShared_2956_ = v_isSharedCheck_2971_;
goto v_resetjp_2954_;
}
else
{
lean_dec(v_x_2946_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2971_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
size_t v___x_2957_; size_t v___x_2958_; size_t v___x_2959_; size_t v_i_2960_; size_t v___x_2961_; size_t v_shift_2962_; lean_object* v_v_2963_; lean_object* v___x_2964_; lean_object* v_xs_x27_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2969_; 
v___x_2957_ = ((size_t)1ULL);
v___x_2958_ = lean_usize_shift_left(v___x_2957_, v_x_2948_);
v___x_2959_ = lean_usize_sub(v___x_2958_, v___x_2957_);
v_i_2960_ = lean_usize_land(v_x_2947_, v___x_2959_);
v___x_2961_ = ((size_t)5ULL);
v_shift_2962_ = lean_usize_sub(v_x_2948_, v___x_2961_);
v_v_2963_ = lean_array_fget(v_cs_2949_, v___x_2951_);
v___x_2964_ = lean_box(0);
v_xs_x27_2965_ = lean_array_fset(v_cs_2949_, v___x_2951_, v___x_2964_);
v___x_2966_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2945_, v_v_2963_, v_i_2960_, v_shift_2962_);
v___x_2967_ = lean_array_fset(v_xs_x27_2965_, v___x_2951_, v___x_2966_);
lean_dec(v___x_2951_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 0, v___x_2967_);
v___x_2969_ = v___x_2955_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
else
{
lean_object* v_vs_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; uint8_t v___x_2976_; 
v_vs_2973_ = lean_ctor_get(v_x_2946_, 0);
v___x_2974_ = lean_usize_to_nat(v_x_2947_);
v___x_2975_ = lean_array_get_size(v_vs_2973_);
v___x_2976_ = lean_nat_dec_lt(v___x_2974_, v___x_2975_);
if (v___x_2976_ == 0)
{
lean_dec(v___x_2974_);
lean_dec_ref(v_val_2945_);
return v_x_2946_;
}
else
{
lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2988_; 
lean_inc_ref(v_vs_2973_);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_x_2946_);
if (v_isSharedCheck_2988_ == 0)
{
lean_object* v_unused_2989_; 
v_unused_2989_ = lean_ctor_get(v_x_2946_, 0);
lean_dec(v_unused_2989_);
v___x_2978_ = v_x_2946_;
v_isShared_2979_ = v_isSharedCheck_2988_;
goto v_resetjp_2977_;
}
else
{
lean_dec(v_x_2946_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2988_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v_v_2980_; lean_object* v___x_2981_; lean_object* v_xs_x27_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2986_; 
v_v_2980_ = lean_array_fget(v_vs_2973_, v___x_2974_);
v___x_2981_ = lean_box(0);
v_xs_x27_2982_ = lean_array_fset(v_vs_2973_, v___x_2974_, v___x_2981_);
v___x_2983_ = l_Lean_PersistentArray_push___redArg(v_v_2980_, v_val_2945_);
v___x_2984_ = lean_array_fset(v_xs_x27_2982_, v___x_2974_, v___x_2983_);
lean_dec(v___x_2974_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 0, v___x_2984_);
v___x_2986_ = v___x_2978_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2984_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2945_ = stack[0].m_obj;
lean_object* v_x_2946_ = stack[1].m_obj;
size_t v_x_2947_ = stack[2].m_num;
size_t v_x_2948_ = stack[3].m_num;
lean_object* v_res_2990_;
v_res_2990_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2945_, v_x_2946_, v_x_2947_, v_x_2948_);
stack->m_obj
 = v_res_2990_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_val_2991_, lean_object* v_x_2992_, lean_object* v_x_2993_, lean_object* v_x_2994_){
_start:
{
size_t v_x_41338__boxed_2995_; size_t v_x_41339__boxed_2996_; lean_object* v_res_2997_; 
v_x_41338__boxed_2995_ = lean_unbox_usize(v_x_2993_);
lean_dec(v_x_2993_);
v_x_41339__boxed_2996_ = lean_unbox_usize(v_x_2994_);
lean_dec(v_x_2994_);
v_res_2997_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2991_, v_x_2992_, v_x_41338__boxed_2995_, v_x_41339__boxed_2996_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object* v_val_2998_, lean_object* v_t_2999_, lean_object* v_i_3000_){
_start:
{
lean_object* v_root_3001_; lean_object* v_tail_3002_; lean_object* v_size_3003_; size_t v_shift_3004_; lean_object* v_tailOff_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3029_; 
v_root_3001_ = lean_ctor_get(v_t_2999_, 0);
v_tail_3002_ = lean_ctor_get(v_t_2999_, 1);
v_size_3003_ = lean_ctor_get(v_t_2999_, 2);
v_shift_3004_ = lean_ctor_get_usize(v_t_2999_, 4);
v_tailOff_3005_ = lean_ctor_get(v_t_2999_, 3);
v_isSharedCheck_3029_ = !lean_is_exclusive(v_t_2999_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3007_ = v_t_2999_;
v_isShared_3008_ = v_isSharedCheck_3029_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_tailOff_3005_);
lean_inc(v_size_3003_);
lean_inc(v_tail_3002_);
lean_inc(v_root_3001_);
lean_dec(v_t_2999_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3029_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
uint8_t v___x_3009_; 
v___x_3009_ = lean_nat_dec_le(v_tailOff_3005_, v_i_3000_);
if (v___x_3009_ == 0)
{
size_t v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3013_; 
v___x_3010_ = lean_usize_of_nat(v_i_3000_);
v___x_3011_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2998_, v_root_3001_, v___x_3010_, v_shift_3004_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 0, v___x_3011_);
v___x_3013_ = v___x_3007_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3011_);
lean_ctor_set(v_reuseFailAlloc_3014_, 1, v_tail_3002_);
lean_ctor_set(v_reuseFailAlloc_3014_, 2, v_size_3003_);
lean_ctor_set(v_reuseFailAlloc_3014_, 3, v_tailOff_3005_);
lean_ctor_set_usize(v_reuseFailAlloc_3014_, 4, v_shift_3004_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
else
{
lean_object* v___x_3015_; lean_object* v___x_3016_; uint8_t v___x_3017_; 
v___x_3015_ = lean_nat_sub(v_i_3000_, v_tailOff_3005_);
v___x_3016_ = lean_array_get_size(v_tail_3002_);
v___x_3017_ = lean_nat_dec_lt(v___x_3015_, v___x_3016_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3019_; 
lean_dec(v___x_3015_);
lean_dec_ref(v_val_2998_);
if (v_isShared_3008_ == 0)
{
v___x_3019_ = v___x_3007_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_root_3001_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v_tail_3002_);
lean_ctor_set(v_reuseFailAlloc_3020_, 2, v_size_3003_);
lean_ctor_set(v_reuseFailAlloc_3020_, 3, v_tailOff_3005_);
lean_ctor_set_usize(v_reuseFailAlloc_3020_, 4, v_shift_3004_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
else
{
lean_object* v_v_3021_; lean_object* v___x_3022_; lean_object* v_xs_x27_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3027_; 
v_v_3021_ = lean_array_fget(v_tail_3002_, v___x_3015_);
v___x_3022_ = lean_box(0);
v_xs_x27_3023_ = lean_array_fset(v_tail_3002_, v___x_3015_, v___x_3022_);
v___x_3024_ = l_Lean_PersistentArray_push___redArg(v_v_3021_, v_val_2998_);
v___x_3025_ = lean_array_fset(v_xs_x27_3023_, v___x_3015_, v___x_3024_);
lean_dec(v___x_3015_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 1, v___x_3025_);
v___x_3027_ = v___x_3007_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_root_3001_);
lean_ctor_set(v_reuseFailAlloc_3028_, 1, v___x_3025_);
lean_ctor_set(v_reuseFailAlloc_3028_, 2, v_size_3003_);
lean_ctor_set(v_reuseFailAlloc_3028_, 3, v_tailOff_3005_);
lean_ctor_set_usize(v_reuseFailAlloc_3028_, 4, v_shift_3004_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object* v_val_3030_, lean_object* v_t_3031_, lean_object* v_i_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3030_, v_t_3031_, v_i_3032_);
lean_dec(v_i_3032_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(lean_object* v___y_3034_, lean_object* v_val_3035_, lean_object* v_v_3036_, lean_object* v_s_3037_){
_start:
{
lean_object* v_structs_3038_; lean_object* v_typeIdOf_3039_; lean_object* v_exprToStructId_3040_; lean_object* v_exprToStructIdEntries_3041_; lean_object* v_forbiddenNatModules_3042_; lean_object* v_natStructs_3043_; lean_object* v_natTypeIdOf_3044_; lean_object* v_exprToNatStructId_3045_; lean_object* v___x_3046_; uint8_t v___x_3047_; 
v_structs_3038_ = lean_ctor_get(v_s_3037_, 0);
v_typeIdOf_3039_ = lean_ctor_get(v_s_3037_, 1);
v_exprToStructId_3040_ = lean_ctor_get(v_s_3037_, 2);
v_exprToStructIdEntries_3041_ = lean_ctor_get(v_s_3037_, 3);
v_forbiddenNatModules_3042_ = lean_ctor_get(v_s_3037_, 4);
v_natStructs_3043_ = lean_ctor_get(v_s_3037_, 5);
v_natTypeIdOf_3044_ = lean_ctor_get(v_s_3037_, 6);
v_exprToNatStructId_3045_ = lean_ctor_get(v_s_3037_, 7);
v___x_3046_ = lean_array_get_size(v_structs_3038_);
v___x_3047_ = lean_nat_dec_lt(v___y_3034_, v___x_3046_);
if (v___x_3047_ == 0)
{
lean_dec_ref(v_val_3035_);
return v_s_3037_;
}
else
{
lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3109_; 
lean_inc_ref(v_exprToNatStructId_3045_);
lean_inc_ref(v_natTypeIdOf_3044_);
lean_inc_ref(v_natStructs_3043_);
lean_inc_ref(v_forbiddenNatModules_3042_);
lean_inc_ref(v_exprToStructIdEntries_3041_);
lean_inc_ref(v_exprToStructId_3040_);
lean_inc_ref(v_typeIdOf_3039_);
lean_inc_ref(v_structs_3038_);
v_isSharedCheck_3109_ = !lean_is_exclusive(v_s_3037_);
if (v_isSharedCheck_3109_ == 0)
{
lean_object* v_unused_3110_; lean_object* v_unused_3111_; lean_object* v_unused_3112_; lean_object* v_unused_3113_; lean_object* v_unused_3114_; lean_object* v_unused_3115_; lean_object* v_unused_3116_; lean_object* v_unused_3117_; 
v_unused_3110_ = lean_ctor_get(v_s_3037_, 7);
lean_dec(v_unused_3110_);
v_unused_3111_ = lean_ctor_get(v_s_3037_, 6);
lean_dec(v_unused_3111_);
v_unused_3112_ = lean_ctor_get(v_s_3037_, 5);
lean_dec(v_unused_3112_);
v_unused_3113_ = lean_ctor_get(v_s_3037_, 4);
lean_dec(v_unused_3113_);
v_unused_3114_ = lean_ctor_get(v_s_3037_, 3);
lean_dec(v_unused_3114_);
v_unused_3115_ = lean_ctor_get(v_s_3037_, 2);
lean_dec(v_unused_3115_);
v_unused_3116_ = lean_ctor_get(v_s_3037_, 1);
lean_dec(v_unused_3116_);
v_unused_3117_ = lean_ctor_get(v_s_3037_, 0);
lean_dec(v_unused_3117_);
v___x_3049_ = v_s_3037_;
v_isShared_3050_ = v_isSharedCheck_3109_;
goto v_resetjp_3048_;
}
else
{
lean_dec(v_s_3037_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3109_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v_v_3051_; lean_object* v_id_3052_; lean_object* v_ringId_x3f_3053_; lean_object* v_type_3054_; lean_object* v_u_3055_; lean_object* v_intModuleInst_3056_; lean_object* v_leInst_x3f_3057_; lean_object* v_ltInst_x3f_3058_; lean_object* v_lawfulOrderLTInst_x3f_3059_; lean_object* v_isPreorderInst_x3f_3060_; lean_object* v_orderedAddInst_x3f_3061_; lean_object* v_isLinearInst_x3f_3062_; lean_object* v_noNatDivInst_x3f_3063_; lean_object* v_ringInst_x3f_3064_; lean_object* v_commRingInst_x3f_3065_; lean_object* v_orderedRingInst_x3f_3066_; lean_object* v_fieldInst_x3f_3067_; lean_object* v_charInst_x3f_3068_; lean_object* v_zero_3069_; lean_object* v_ofNatZero_3070_; lean_object* v_one_x3f_3071_; lean_object* v_leFn_x3f_3072_; lean_object* v_ltFn_x3f_3073_; lean_object* v_addFn_3074_; lean_object* v_zsmulFn_3075_; lean_object* v_nsmulFn_3076_; lean_object* v_zsmulFn_x3f_3077_; lean_object* v_nsmulFn_x3f_3078_; lean_object* v_homomulFn_x3f_3079_; lean_object* v_subFn_3080_; lean_object* v_negFn_3081_; lean_object* v_vars_3082_; lean_object* v_varMap_3083_; lean_object* v_lowers_3084_; lean_object* v_uppers_3085_; lean_object* v_diseqs_3086_; lean_object* v_assignment_3087_; uint8_t v_caseSplits_3088_; lean_object* v_conflict_x3f_3089_; lean_object* v_diseqSplits_3090_; lean_object* v_elimEqs_3091_; lean_object* v_elimStack_3092_; lean_object* v_occurs_3093_; lean_object* v_ignored_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3108_; 
v_v_3051_ = lean_array_fget(v_structs_3038_, v___y_3034_);
v_id_3052_ = lean_ctor_get(v_v_3051_, 0);
v_ringId_x3f_3053_ = lean_ctor_get(v_v_3051_, 1);
v_type_3054_ = lean_ctor_get(v_v_3051_, 2);
v_u_3055_ = lean_ctor_get(v_v_3051_, 3);
v_intModuleInst_3056_ = lean_ctor_get(v_v_3051_, 4);
v_leInst_x3f_3057_ = lean_ctor_get(v_v_3051_, 5);
v_ltInst_x3f_3058_ = lean_ctor_get(v_v_3051_, 6);
v_lawfulOrderLTInst_x3f_3059_ = lean_ctor_get(v_v_3051_, 7);
v_isPreorderInst_x3f_3060_ = lean_ctor_get(v_v_3051_, 8);
v_orderedAddInst_x3f_3061_ = lean_ctor_get(v_v_3051_, 9);
v_isLinearInst_x3f_3062_ = lean_ctor_get(v_v_3051_, 10);
v_noNatDivInst_x3f_3063_ = lean_ctor_get(v_v_3051_, 11);
v_ringInst_x3f_3064_ = lean_ctor_get(v_v_3051_, 12);
v_commRingInst_x3f_3065_ = lean_ctor_get(v_v_3051_, 13);
v_orderedRingInst_x3f_3066_ = lean_ctor_get(v_v_3051_, 14);
v_fieldInst_x3f_3067_ = lean_ctor_get(v_v_3051_, 15);
v_charInst_x3f_3068_ = lean_ctor_get(v_v_3051_, 16);
v_zero_3069_ = lean_ctor_get(v_v_3051_, 17);
v_ofNatZero_3070_ = lean_ctor_get(v_v_3051_, 18);
v_one_x3f_3071_ = lean_ctor_get(v_v_3051_, 19);
v_leFn_x3f_3072_ = lean_ctor_get(v_v_3051_, 20);
v_ltFn_x3f_3073_ = lean_ctor_get(v_v_3051_, 21);
v_addFn_3074_ = lean_ctor_get(v_v_3051_, 22);
v_zsmulFn_3075_ = lean_ctor_get(v_v_3051_, 23);
v_nsmulFn_3076_ = lean_ctor_get(v_v_3051_, 24);
v_zsmulFn_x3f_3077_ = lean_ctor_get(v_v_3051_, 25);
v_nsmulFn_x3f_3078_ = lean_ctor_get(v_v_3051_, 26);
v_homomulFn_x3f_3079_ = lean_ctor_get(v_v_3051_, 27);
v_subFn_3080_ = lean_ctor_get(v_v_3051_, 28);
v_negFn_3081_ = lean_ctor_get(v_v_3051_, 29);
v_vars_3082_ = lean_ctor_get(v_v_3051_, 30);
v_varMap_3083_ = lean_ctor_get(v_v_3051_, 31);
v_lowers_3084_ = lean_ctor_get(v_v_3051_, 32);
v_uppers_3085_ = lean_ctor_get(v_v_3051_, 33);
v_diseqs_3086_ = lean_ctor_get(v_v_3051_, 34);
v_assignment_3087_ = lean_ctor_get(v_v_3051_, 35);
v_caseSplits_3088_ = lean_ctor_get_uint8(v_v_3051_, sizeof(void*)*42);
v_conflict_x3f_3089_ = lean_ctor_get(v_v_3051_, 36);
v_diseqSplits_3090_ = lean_ctor_get(v_v_3051_, 37);
v_elimEqs_3091_ = lean_ctor_get(v_v_3051_, 38);
v_elimStack_3092_ = lean_ctor_get(v_v_3051_, 39);
v_occurs_3093_ = lean_ctor_get(v_v_3051_, 40);
v_ignored_3094_ = lean_ctor_get(v_v_3051_, 41);
v_isSharedCheck_3108_ = !lean_is_exclusive(v_v_3051_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3096_ = v_v_3051_;
v_isShared_3097_ = v_isSharedCheck_3108_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_ignored_3094_);
lean_inc(v_occurs_3093_);
lean_inc(v_elimStack_3092_);
lean_inc(v_elimEqs_3091_);
lean_inc(v_diseqSplits_3090_);
lean_inc(v_conflict_x3f_3089_);
lean_inc(v_assignment_3087_);
lean_inc(v_diseqs_3086_);
lean_inc(v_uppers_3085_);
lean_inc(v_lowers_3084_);
lean_inc(v_varMap_3083_);
lean_inc(v_vars_3082_);
lean_inc(v_negFn_3081_);
lean_inc(v_subFn_3080_);
lean_inc(v_homomulFn_x3f_3079_);
lean_inc(v_nsmulFn_x3f_3078_);
lean_inc(v_zsmulFn_x3f_3077_);
lean_inc(v_nsmulFn_3076_);
lean_inc(v_zsmulFn_3075_);
lean_inc(v_addFn_3074_);
lean_inc(v_ltFn_x3f_3073_);
lean_inc(v_leFn_x3f_3072_);
lean_inc(v_one_x3f_3071_);
lean_inc(v_ofNatZero_3070_);
lean_inc(v_zero_3069_);
lean_inc(v_charInst_x3f_3068_);
lean_inc(v_fieldInst_x3f_3067_);
lean_inc(v_orderedRingInst_x3f_3066_);
lean_inc(v_commRingInst_x3f_3065_);
lean_inc(v_ringInst_x3f_3064_);
lean_inc(v_noNatDivInst_x3f_3063_);
lean_inc(v_isLinearInst_x3f_3062_);
lean_inc(v_orderedAddInst_x3f_3061_);
lean_inc(v_isPreorderInst_x3f_3060_);
lean_inc(v_lawfulOrderLTInst_x3f_3059_);
lean_inc(v_ltInst_x3f_3058_);
lean_inc(v_leInst_x3f_3057_);
lean_inc(v_intModuleInst_3056_);
lean_inc(v_u_3055_);
lean_inc(v_type_3054_);
lean_inc(v_ringId_x3f_3053_);
lean_inc(v_id_3052_);
lean_dec(v_v_3051_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3108_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3098_; lean_object* v_xs_x27_3099_; lean_object* v___x_3100_; lean_object* v___x_3102_; 
v___x_3098_ = lean_box(0);
v_xs_x27_3099_ = lean_array_fset(v_structs_3038_, v___y_3034_, v___x_3098_);
v___x_3100_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3035_, v_diseqs_3086_, v_v_3036_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 34, v___x_3100_);
v___x_3102_ = v___x_3096_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_id_3052_);
lean_ctor_set(v_reuseFailAlloc_3107_, 1, v_ringId_x3f_3053_);
lean_ctor_set(v_reuseFailAlloc_3107_, 2, v_type_3054_);
lean_ctor_set(v_reuseFailAlloc_3107_, 3, v_u_3055_);
lean_ctor_set(v_reuseFailAlloc_3107_, 4, v_intModuleInst_3056_);
lean_ctor_set(v_reuseFailAlloc_3107_, 5, v_leInst_x3f_3057_);
lean_ctor_set(v_reuseFailAlloc_3107_, 6, v_ltInst_x3f_3058_);
lean_ctor_set(v_reuseFailAlloc_3107_, 7, v_lawfulOrderLTInst_x3f_3059_);
lean_ctor_set(v_reuseFailAlloc_3107_, 8, v_isPreorderInst_x3f_3060_);
lean_ctor_set(v_reuseFailAlloc_3107_, 9, v_orderedAddInst_x3f_3061_);
lean_ctor_set(v_reuseFailAlloc_3107_, 10, v_isLinearInst_x3f_3062_);
lean_ctor_set(v_reuseFailAlloc_3107_, 11, v_noNatDivInst_x3f_3063_);
lean_ctor_set(v_reuseFailAlloc_3107_, 12, v_ringInst_x3f_3064_);
lean_ctor_set(v_reuseFailAlloc_3107_, 13, v_commRingInst_x3f_3065_);
lean_ctor_set(v_reuseFailAlloc_3107_, 14, v_orderedRingInst_x3f_3066_);
lean_ctor_set(v_reuseFailAlloc_3107_, 15, v_fieldInst_x3f_3067_);
lean_ctor_set(v_reuseFailAlloc_3107_, 16, v_charInst_x3f_3068_);
lean_ctor_set(v_reuseFailAlloc_3107_, 17, v_zero_3069_);
lean_ctor_set(v_reuseFailAlloc_3107_, 18, v_ofNatZero_3070_);
lean_ctor_set(v_reuseFailAlloc_3107_, 19, v_one_x3f_3071_);
lean_ctor_set(v_reuseFailAlloc_3107_, 20, v_leFn_x3f_3072_);
lean_ctor_set(v_reuseFailAlloc_3107_, 21, v_ltFn_x3f_3073_);
lean_ctor_set(v_reuseFailAlloc_3107_, 22, v_addFn_3074_);
lean_ctor_set(v_reuseFailAlloc_3107_, 23, v_zsmulFn_3075_);
lean_ctor_set(v_reuseFailAlloc_3107_, 24, v_nsmulFn_3076_);
lean_ctor_set(v_reuseFailAlloc_3107_, 25, v_zsmulFn_x3f_3077_);
lean_ctor_set(v_reuseFailAlloc_3107_, 26, v_nsmulFn_x3f_3078_);
lean_ctor_set(v_reuseFailAlloc_3107_, 27, v_homomulFn_x3f_3079_);
lean_ctor_set(v_reuseFailAlloc_3107_, 28, v_subFn_3080_);
lean_ctor_set(v_reuseFailAlloc_3107_, 29, v_negFn_3081_);
lean_ctor_set(v_reuseFailAlloc_3107_, 30, v_vars_3082_);
lean_ctor_set(v_reuseFailAlloc_3107_, 31, v_varMap_3083_);
lean_ctor_set(v_reuseFailAlloc_3107_, 32, v_lowers_3084_);
lean_ctor_set(v_reuseFailAlloc_3107_, 33, v_uppers_3085_);
lean_ctor_set(v_reuseFailAlloc_3107_, 34, v___x_3100_);
lean_ctor_set(v_reuseFailAlloc_3107_, 35, v_assignment_3087_);
lean_ctor_set(v_reuseFailAlloc_3107_, 36, v_conflict_x3f_3089_);
lean_ctor_set(v_reuseFailAlloc_3107_, 37, v_diseqSplits_3090_);
lean_ctor_set(v_reuseFailAlloc_3107_, 38, v_elimEqs_3091_);
lean_ctor_set(v_reuseFailAlloc_3107_, 39, v_elimStack_3092_);
lean_ctor_set(v_reuseFailAlloc_3107_, 40, v_occurs_3093_);
lean_ctor_set(v_reuseFailAlloc_3107_, 41, v_ignored_3094_);
lean_ctor_set_uint8(v_reuseFailAlloc_3107_, sizeof(void*)*42, v_caseSplits_3088_);
v___x_3102_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
lean_object* v___x_3103_; lean_object* v___x_3105_; 
v___x_3103_ = lean_array_fset(v_xs_x27_3099_, v___y_3034_, v___x_3102_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 0, v___x_3103_);
v___x_3105_ = v___x_3049_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3106_, 1, v_typeIdOf_3039_);
lean_ctor_set(v_reuseFailAlloc_3106_, 2, v_exprToStructId_3040_);
lean_ctor_set(v_reuseFailAlloc_3106_, 3, v_exprToStructIdEntries_3041_);
lean_ctor_set(v_reuseFailAlloc_3106_, 4, v_forbiddenNatModules_3042_);
lean_ctor_set(v_reuseFailAlloc_3106_, 5, v_natStructs_3043_);
lean_ctor_set(v_reuseFailAlloc_3106_, 6, v_natTypeIdOf_3044_);
lean_ctor_set(v_reuseFailAlloc_3106_, 7, v_exprToNatStructId_3045_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed(lean_object* v___y_3118_, lean_object* v_val_3119_, lean_object* v_v_3120_, lean_object* v_s_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(v___y_3118_, v_val_3119_, v_v_3120_, v_s_3121_);
lean_dec(v_v_3120_);
lean_dec(v___y_3118_);
return v_res_3122_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3129_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3130_ = l_Lean_Name_append(v___x_3129_, v___x_3128_);
return v___x_3130_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3138_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3139_ = l_Lean_Name_append(v___x_3138_, v___x_3137_);
return v___x_3139_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7(void){
_start:
{
lean_object* v_cls_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v_cls_3144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3145_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3146_ = l_Lean_Name_append(v___x_3145_, v_cls_3144_);
return v___x_3146_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object* v_c_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_){
_start:
{
lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v_toCold_3218_; lean_object* v_options_3219_; lean_object* v_inheritedTraceOptions_3220_; uint8_t v_hasTrace_3221_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; 
v_toCold_3218_ = lean_ctor_get(v_a_3157_, 0);
v_options_3219_ = lean_ctor_get(v_toCold_3218_, 2);
v_inheritedTraceOptions_3220_ = lean_ctor_get(v_toCold_3218_, 11);
v_hasTrace_3221_ = lean_ctor_get_uint8(v_options_3219_, sizeof(void*)*1);
if (v_hasTrace_3221_ == 0)
{
v___y_3223_ = v_a_3148_;
v___y_3224_ = v_a_3149_;
v___y_3225_ = v_a_3150_;
v___y_3226_ = v_a_3151_;
v___y_3227_ = v_a_3152_;
v___y_3228_ = v_a_3153_;
v___y_3229_ = v_a_3154_;
v___y_3230_ = v_a_3155_;
v___y_3231_ = v_a_3156_;
v___y_3232_ = v_a_3157_;
v___y_3233_ = v_a_3158_;
goto v___jp_3222_;
}
else
{
lean_object* v_cls_3294_; lean_object* v___x_3295_; uint8_t v___x_3296_; 
v_cls_3294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3295_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_3296_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3220_, v_options_3219_, v___x_3295_);
if (v___x_3296_ == 0)
{
v___y_3223_ = v_a_3148_;
v___y_3224_ = v_a_3149_;
v___y_3225_ = v_a_3150_;
v___y_3226_ = v_a_3151_;
v___y_3227_ = v_a_3152_;
v___y_3228_ = v_a_3153_;
v___y_3229_ = v_a_3154_;
v___y_3230_ = v_a_3155_;
v___y_3231_ = v_a_3156_;
v___y_3232_ = v_a_3157_;
v___y_3233_ = v_a_3158_;
goto v___jp_3222_;
}
else
{
lean_object* v___x_3297_; 
v___x_3297_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref_known(v___x_3297_, 1);
v___x_3299_ = l_Lean_MessageData_ofExpr(v_a_3298_);
v___x_3300_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_3294_, v___x_3299_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_dec_ref_known(v___x_3300_, 1);
v___y_3223_ = v_a_3148_;
v___y_3224_ = v_a_3149_;
v___y_3225_ = v_a_3150_;
v___y_3226_ = v_a_3151_;
v___y_3227_ = v_a_3152_;
v___y_3228_ = v_a_3153_;
v___y_3229_ = v_a_3154_;
v___y_3230_ = v_a_3155_;
v___y_3231_ = v_a_3156_;
v___y_3232_ = v_a_3157_;
v___y_3233_ = v_a_3158_;
goto v___jp_3222_;
}
else
{
lean_dec_ref(v_c_3147_);
return v___x_3300_;
}
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
lean_dec_ref(v_c_3147_);
v_a_3301_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3297_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3297_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
}
v___jp_3160_:
{
lean_object* v___f_3177_; lean_object* v___x_3178_; 
lean_inc(v___y_3166_);
v___f_3177_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3177_, 0, v___y_3166_);
lean_closure_set(v___f_3177_, 1, v___y_3162_);
lean_closure_set(v___f_3177_, 2, v___y_3161_);
v___x_3178_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_3163_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
lean_dec_ref_known(v___x_3178_, 1);
v___x_3179_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3180_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3179_, v___f_3177_, v___y_3167_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v___x_3181_; 
lean_dec_ref_known(v___x_3180_, 1);
v___x_3181_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3194_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3184_ = v___x_3181_;
v_isShared_3185_ = v_isSharedCheck_3194_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3181_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3194_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
uint8_t v___x_3186_; uint8_t v___x_3187_; uint8_t v___x_3188_; 
v___x_3186_ = 0;
v___x_3187_ = lean_unbox(v_a_3182_);
lean_dec(v_a_3182_);
v___x_3188_ = l_Lean_instBEqLBool_beq(v___x_3187_, v___x_3186_);
if (v___x_3188_ == 0)
{
lean_object* v___x_3189_; lean_object* v___x_3191_; 
lean_dec(v___y_3164_);
v___x_3189_ = lean_box(0);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 0, v___x_3189_);
v___x_3191_ = v___x_3184_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3189_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
else
{
lean_object* v___x_3193_; 
lean_del_object(v___x_3184_);
v___x_3193_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_3164_, v___y_3166_, v___y_3167_);
return v___x_3193_;
}
}
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_dec(v___y_3164_);
v_a_3195_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3181_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3181_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
else
{
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
return v___x_3180_;
}
}
else
{
lean_dec_ref(v___f_3177_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
return v___x_3178_;
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
lean_object* v___x_3234_; 
lean_inc_ref(v___y_3232_);
v___x_3234_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_3147_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3285_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3237_ = v___x_3234_;
v_isShared_3238_ = v_isSharedCheck_3285_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3234_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3285_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
if (lean_obj_tag(v_a_3235_) == 1)
{
lean_object* v_val_3239_; lean_object* v_p_3240_; 
lean_del_object(v___x_3237_);
v_val_3239_ = lean_ctor_get(v_a_3235_, 0);
lean_inc(v_val_3239_);
lean_dec_ref_known(v_a_3235_, 1);
v_p_3240_ = lean_ctor_get(v_val_3239_, 0);
if (lean_obj_tag(v_p_3240_) == 0)
{
lean_object* v_toCold_3241_; lean_object* v_options_3242_; uint8_t v_hasTrace_3243_; 
v_toCold_3241_ = lean_ctor_get(v___y_3232_, 0);
v_options_3242_ = lean_ctor_get(v_toCold_3241_, 2);
v_hasTrace_3243_ = lean_ctor_get_uint8(v_options_3242_, sizeof(void*)*1);
if (v_hasTrace_3243_ == 0)
{
v___y_3204_ = v_val_3239_;
v___y_3205_ = v___y_3223_;
v___y_3206_ = v___y_3224_;
v___y_3207_ = v___y_3225_;
v___y_3208_ = v___y_3226_;
v___y_3209_ = v___y_3227_;
v___y_3210_ = v___y_3228_;
v___y_3211_ = v___y_3229_;
v___y_3212_ = v___y_3230_;
v___y_3213_ = v___y_3231_;
v___y_3214_ = v___y_3232_;
v___y_3215_ = v___y_3233_;
goto v___jp_3203_;
}
else
{
lean_object* v_inheritedTraceOptions_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; uint8_t v___x_3247_; 
v_inheritedTraceOptions_3244_ = lean_ctor_get(v_toCold_3241_, 11);
v___x_3245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3246_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2);
v___x_3247_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3244_, v_options_3242_, v___x_3246_);
if (v___x_3247_ == 0)
{
v___y_3204_ = v_val_3239_;
v___y_3205_ = v___y_3223_;
v___y_3206_ = v___y_3224_;
v___y_3207_ = v___y_3225_;
v___y_3208_ = v___y_3226_;
v___y_3209_ = v___y_3227_;
v___y_3210_ = v___y_3228_;
v___y_3211_ = v___y_3229_;
v___y_3212_ = v___y_3230_;
v___y_3213_ = v___y_3231_;
v___y_3214_ = v___y_3232_;
v___y_3215_ = v___y_3233_;
goto v___jp_3203_;
}
else
{
lean_object* v___x_3248_; 
v___x_3248_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3239_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___x_3248_, 1);
v___x_3250_ = l_Lean_MessageData_ofExpr(v_a_3249_);
v___x_3251_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3245_, v___x_3250_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_dec_ref_known(v___x_3251_, 1);
v___y_3204_ = v_val_3239_;
v___y_3205_ = v___y_3223_;
v___y_3206_ = v___y_3224_;
v___y_3207_ = v___y_3225_;
v___y_3208_ = v___y_3226_;
v___y_3209_ = v___y_3227_;
v___y_3210_ = v___y_3228_;
v___y_3211_ = v___y_3229_;
v___y_3212_ = v___y_3230_;
v___y_3213_ = v___y_3231_;
v___y_3214_ = v___y_3232_;
v___y_3215_ = v___y_3233_;
goto v___jp_3203_;
}
else
{
lean_dec(v_val_3239_);
return v___x_3251_;
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec(v_val_3239_);
v_a_3252_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3248_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3248_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3260_; lean_object* v_options_3261_; uint8_t v_hasTrace_3262_; 
lean_inc_ref(v_p_3240_);
v_toCold_3260_ = lean_ctor_get(v___y_3232_, 0);
v_options_3261_ = lean_ctor_get(v_toCold_3260_, 2);
v_hasTrace_3262_ = lean_ctor_get_uint8(v_options_3261_, sizeof(void*)*1);
if (v_hasTrace_3262_ == 0)
{
lean_object* v_v_3263_; 
v_v_3263_ = lean_ctor_get(v_p_3240_, 1);
lean_inc_n(v_v_3263_, 2);
lean_inc(v_val_3239_);
v___y_3161_ = v_v_3263_;
v___y_3162_ = v_val_3239_;
v___y_3163_ = v_p_3240_;
v___y_3164_ = v_v_3263_;
v___y_3165_ = v_val_3239_;
v___y_3166_ = v___y_3223_;
v___y_3167_ = v___y_3224_;
v___y_3168_ = v___y_3225_;
v___y_3169_ = v___y_3226_;
v___y_3170_ = v___y_3227_;
v___y_3171_ = v___y_3228_;
v___y_3172_ = v___y_3229_;
v___y_3173_ = v___y_3230_;
v___y_3174_ = v___y_3231_;
v___y_3175_ = v___y_3232_;
v___y_3176_ = v___y_3233_;
goto v___jp_3160_;
}
else
{
lean_object* v_v_3264_; lean_object* v_inheritedTraceOptions_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; uint8_t v___x_3268_; 
v_v_3264_ = lean_ctor_get(v_p_3240_, 1);
lean_inc(v_v_3264_);
v_inheritedTraceOptions_3265_ = lean_ctor_get(v_toCold_3260_, 11);
v___x_3266_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3267_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_3268_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3265_, v_options_3261_, v___x_3267_);
if (v___x_3268_ == 0)
{
lean_inc(v_val_3239_);
lean_inc(v_v_3264_);
v___y_3161_ = v_v_3264_;
v___y_3162_ = v_val_3239_;
v___y_3163_ = v_p_3240_;
v___y_3164_ = v_v_3264_;
v___y_3165_ = v_val_3239_;
v___y_3166_ = v___y_3223_;
v___y_3167_ = v___y_3224_;
v___y_3168_ = v___y_3225_;
v___y_3169_ = v___y_3226_;
v___y_3170_ = v___y_3227_;
v___y_3171_ = v___y_3228_;
v___y_3172_ = v___y_3229_;
v___y_3173_ = v___y_3230_;
v___y_3174_ = v___y_3231_;
v___y_3175_ = v___y_3232_;
v___y_3176_ = v___y_3233_;
goto v___jp_3160_;
}
else
{
lean_object* v___x_3269_; 
v___x_3269_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3239_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_a_3270_);
lean_dec_ref_known(v___x_3269_, 1);
v___x_3271_ = l_Lean_MessageData_ofExpr(v_a_3270_);
v___x_3272_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3266_, v___x_3271_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_dec_ref_known(v___x_3272_, 1);
lean_inc(v_val_3239_);
lean_inc(v_v_3264_);
v___y_3161_ = v_v_3264_;
v___y_3162_ = v_val_3239_;
v___y_3163_ = v_p_3240_;
v___y_3164_ = v_v_3264_;
v___y_3165_ = v_val_3239_;
v___y_3166_ = v___y_3223_;
v___y_3167_ = v___y_3224_;
v___y_3168_ = v___y_3225_;
v___y_3169_ = v___y_3226_;
v___y_3170_ = v___y_3227_;
v___y_3171_ = v___y_3228_;
v___y_3172_ = v___y_3229_;
v___y_3173_ = v___y_3230_;
v___y_3174_ = v___y_3231_;
v___y_3175_ = v___y_3232_;
v___y_3176_ = v___y_3233_;
goto v___jp_3160_;
}
else
{
lean_dec(v_v_3264_);
lean_dec_ref_known(v_p_3240_, 3);
lean_dec(v_val_3239_);
return v___x_3272_;
}
}
else
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
lean_dec(v_v_3264_);
lean_dec_ref_known(v_p_3240_, 3);
lean_dec(v_val_3239_);
v_a_3273_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___x_3269_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3269_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3281_; lean_object* v___x_3283_; 
lean_dec(v_a_3235_);
v___x_3281_ = lean_box(0);
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 0, v___x_3281_);
v___x_3283_ = v___x_3237_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3281_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
v_a_3286_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3234_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3234_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_3147_ = stack[0].m_obj;
lean_object* v_a_3148_ = stack[1].m_obj;
lean_object* v_a_3149_ = stack[2].m_obj;
lean_object* v_a_3150_ = stack[3].m_obj;
lean_object* v_a_3151_ = stack[4].m_obj;
lean_object* v_a_3152_ = stack[5].m_obj;
lean_object* v_a_3153_ = stack[6].m_obj;
lean_object* v_a_3154_ = stack[7].m_obj;
lean_object* v_a_3155_ = stack[8].m_obj;
lean_object* v_a_3156_ = stack[9].m_obj;
lean_object* v_a_3157_ = stack[10].m_obj;
lean_object* v_a_3158_ = stack[11].m_obj;
lean_object* v_res_3309_;
v_res_3309_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_c_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_);
stack->m_obj
 = v_res_3309_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___boxed(lean_object* v_c_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_c_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
lean_dec(v_a_3321_);
lean_dec_ref(v_a_3320_);
lean_dec(v_a_3319_);
lean_dec_ref(v_a_3318_);
lean_dec(v_a_3317_);
lean_dec_ref(v_a_3316_);
lean_dec(v_a_3315_);
lean_dec_ref(v_a_3314_);
lean_dec(v_a_3313_);
lean_dec(v_a_3312_);
lean_dec(v_a_3311_);
return v_res_3323_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_3324_, lean_object* v_as_3325_, size_t v_sz_3326_, size_t v_i_3327_, lean_object* v_b_3328_){
_start:
{
uint8_t v___x_3329_; 
v___x_3329_ = lean_usize_dec_lt(v_i_3327_, v_sz_3326_);
if (v___x_3329_ == 0)
{
return v_b_3328_;
}
else
{
lean_object* v_snd_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3371_; 
v_snd_3330_ = lean_ctor_get(v_b_3328_, 1);
v_isSharedCheck_3371_ = !lean_is_exclusive(v_b_3328_);
if (v_isSharedCheck_3371_ == 0)
{
lean_object* v_unused_3372_; 
v_unused_3372_ = lean_ctor_get(v_b_3328_, 0);
lean_dec(v_unused_3372_);
v___x_3332_ = v_b_3328_;
v_isShared_3333_ = v_isSharedCheck_3371_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_snd_3330_);
lean_dec(v_b_3328_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3371_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v_fst_3334_; lean_object* v_snd_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3370_; 
v_fst_3334_ = lean_ctor_get(v_snd_3330_, 0);
v_snd_3335_ = lean_ctor_get(v_snd_3330_, 1);
v_isSharedCheck_3370_ = !lean_is_exclusive(v_snd_3330_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3337_ = v_snd_3330_;
v_isShared_3338_ = v_isSharedCheck_3370_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_snd_3335_);
lean_inc(v_fst_3334_);
lean_dec(v_snd_3330_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3370_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v_a_3339_; lean_object* v_p_3340_; lean_object* v___x_3341_; lean_object* v_a_3343_; lean_object* v_b_3350_; lean_object* v___x_3351_; uint8_t v___x_3352_; 
v_a_3339_ = lean_array_uget(v_as_3325_, v_i_3327_);
v_p_3340_ = lean_ctor_get(v_a_3339_, 0);
v___x_3341_ = lean_box(0);
v_b_3350_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3340_, v_x_3324_);
v___x_3351_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3352_ = lean_int_dec_eq(v_b_3350_, v___x_3351_);
if (v___x_3352_ == 0)
{
lean_object* v___x_3354_; 
lean_inc(v_a_3339_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 1, v_a_3339_);
lean_ctor_set(v___x_3332_, 0, v_b_3350_);
v___x_3354_ = v___x_3332_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_b_3350_);
lean_ctor_set(v_reuseFailAlloc_3365_, 1, v_a_3339_);
v___x_3354_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3362_; 
v_isSharedCheck_3362_ = !lean_is_exclusive(v_a_3339_);
if (v_isSharedCheck_3362_ == 0)
{
lean_object* v_unused_3363_; lean_object* v_unused_3364_; 
v_unused_3363_ = lean_ctor_get(v_a_3339_, 1);
lean_dec(v_unused_3363_);
v_unused_3364_ = lean_ctor_get(v_a_3339_, 0);
lean_dec(v_unused_3364_);
v___x_3356_ = v_a_3339_;
v_isShared_3357_ = v_isSharedCheck_3362_;
goto v_resetjp_3355_;
}
else
{
lean_dec(v_a_3339_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3362_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v_todo_3358_; lean_object* v___x_3360_; 
v_todo_3358_ = lean_array_push(v_snd_3335_, v___x_3354_);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 1, v_todo_3358_);
lean_ctor_set(v___x_3356_, 0, v_fst_3334_);
v___x_3360_ = v___x_3356_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_fst_3334_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_todo_3358_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
v_a_3343_ = v___x_3360_;
goto v___jp_3342_;
}
}
}
}
else
{
lean_object* v_cs_x27_3366_; lean_object* v___x_3368_; 
lean_dec(v_b_3350_);
v_cs_x27_3366_ = l_Lean_PersistentArray_push___redArg(v_fst_3334_, v_a_3339_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 1, v_snd_3335_);
lean_ctor_set(v___x_3332_, 0, v_cs_x27_3366_);
v___x_3368_ = v___x_3332_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_cs_x27_3366_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v_snd_3335_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
v_a_3343_ = v___x_3368_;
goto v___jp_3342_;
}
}
v___jp_3342_:
{
lean_object* v___x_3345_; 
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 1, v_a_3343_);
lean_ctor_set(v___x_3337_, 0, v___x_3341_);
v___x_3345_ = v___x_3337_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3341_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_a_3343_);
v___x_3345_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
size_t v___x_3346_; size_t v___x_3347_; 
v___x_3346_ = ((size_t)1ULL);
v___x_3347_ = lean_usize_add(v_i_3327_, v___x_3346_);
v_i_3327_ = v___x_3347_;
v_b_3328_ = v___x_3345_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3324_ = stack[0].m_obj;
lean_object* v_as_3325_ = stack[1].m_obj;
size_t v_sz_3326_ = stack[2].m_num;
size_t v_i_3327_ = stack[3].m_num;
lean_object* v_b_3328_ = stack[4].m_obj;
lean_object* v_res_3373_;
v_res_3373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3324_, v_as_3325_, v_sz_3326_, v_i_3327_, v_b_3328_);
stack->m_obj
 = v_res_3373_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_3374_, lean_object* v_as_3375_, lean_object* v_sz_3376_, lean_object* v_i_3377_, lean_object* v_b_3378_){
_start:
{
size_t v_sz_boxed_3379_; size_t v_i_boxed_3380_; lean_object* v_res_3381_; 
v_sz_boxed_3379_ = lean_unbox_usize(v_sz_3376_);
lean_dec(v_sz_3376_);
v_i_boxed_3380_ = lean_unbox_usize(v_i_3377_);
lean_dec(v_i_3377_);
v_res_3381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3374_, v_as_3375_, v_sz_boxed_3379_, v_i_boxed_3380_, v_b_3378_);
lean_dec_ref(v_as_3375_);
lean_dec(v_x_3374_);
return v_res_3381_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(lean_object* v_x_3382_, lean_object* v_as_3383_, size_t v_sz_3384_, size_t v_i_3385_, lean_object* v_b_3386_){
_start:
{
uint8_t v___x_3387_; 
v___x_3387_ = lean_usize_dec_lt(v_i_3385_, v_sz_3384_);
if (v___x_3387_ == 0)
{
return v_b_3386_;
}
else
{
lean_object* v_snd_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3429_; 
v_snd_3388_ = lean_ctor_get(v_b_3386_, 1);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_b_3386_);
if (v_isSharedCheck_3429_ == 0)
{
lean_object* v_unused_3430_; 
v_unused_3430_ = lean_ctor_get(v_b_3386_, 0);
lean_dec(v_unused_3430_);
v___x_3390_ = v_b_3386_;
v_isShared_3391_ = v_isSharedCheck_3429_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_snd_3388_);
lean_dec(v_b_3386_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3429_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v_fst_3392_; lean_object* v_snd_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3428_; 
v_fst_3392_ = lean_ctor_get(v_snd_3388_, 0);
v_snd_3393_ = lean_ctor_get(v_snd_3388_, 1);
v_isSharedCheck_3428_ = !lean_is_exclusive(v_snd_3388_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3395_ = v_snd_3388_;
v_isShared_3396_ = v_isSharedCheck_3428_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_snd_3393_);
lean_inc(v_fst_3392_);
lean_dec(v_snd_3388_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3428_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v_a_3397_; lean_object* v_p_3398_; lean_object* v___x_3399_; lean_object* v_a_3401_; lean_object* v_b_3408_; lean_object* v___x_3409_; uint8_t v___x_3410_; 
v_a_3397_ = lean_array_uget(v_as_3383_, v_i_3385_);
v_p_3398_ = lean_ctor_get(v_a_3397_, 0);
v___x_3399_ = lean_box(0);
v_b_3408_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3398_, v_x_3382_);
v___x_3409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3410_ = lean_int_dec_eq(v_b_3408_, v___x_3409_);
if (v___x_3410_ == 0)
{
lean_object* v___x_3412_; 
lean_inc(v_a_3397_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 1, v_a_3397_);
lean_ctor_set(v___x_3390_, 0, v_b_3408_);
v___x_3412_ = v___x_3390_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_b_3408_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v_a_3397_);
v___x_3412_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3420_; 
v_isSharedCheck_3420_ = !lean_is_exclusive(v_a_3397_);
if (v_isSharedCheck_3420_ == 0)
{
lean_object* v_unused_3421_; lean_object* v_unused_3422_; 
v_unused_3421_ = lean_ctor_get(v_a_3397_, 1);
lean_dec(v_unused_3421_);
v_unused_3422_ = lean_ctor_get(v_a_3397_, 0);
lean_dec(v_unused_3422_);
v___x_3414_ = v_a_3397_;
v_isShared_3415_ = v_isSharedCheck_3420_;
goto v_resetjp_3413_;
}
else
{
lean_dec(v_a_3397_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3420_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v_todo_3416_; lean_object* v___x_3418_; 
v_todo_3416_ = lean_array_push(v_snd_3393_, v___x_3412_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 1, v_todo_3416_);
lean_ctor_set(v___x_3414_, 0, v_fst_3392_);
v___x_3418_ = v___x_3414_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_fst_3392_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v_todo_3416_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
v_a_3401_ = v___x_3418_;
goto v___jp_3400_;
}
}
}
}
else
{
lean_object* v_cs_x27_3424_; lean_object* v___x_3426_; 
lean_dec(v_b_3408_);
v_cs_x27_3424_ = l_Lean_PersistentArray_push___redArg(v_fst_3392_, v_a_3397_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 1, v_snd_3393_);
lean_ctor_set(v___x_3390_, 0, v_cs_x27_3424_);
v___x_3426_ = v___x_3390_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_cs_x27_3424_);
lean_ctor_set(v_reuseFailAlloc_3427_, 1, v_snd_3393_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
v_a_3401_ = v___x_3426_;
goto v___jp_3400_;
}
}
v___jp_3400_:
{
lean_object* v___x_3403_; 
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 1, v_a_3401_);
lean_ctor_set(v___x_3395_, 0, v___x_3399_);
v___x_3403_ = v___x_3395_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3399_);
lean_ctor_set(v_reuseFailAlloc_3407_, 1, v_a_3401_);
v___x_3403_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
size_t v___x_3404_; size_t v___x_3405_; lean_object* v___x_3406_; 
v___x_3404_ = ((size_t)1ULL);
v___x_3405_ = lean_usize_add(v_i_3385_, v___x_3404_);
v___x_3406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3382_, v_as_3383_, v_sz_3384_, v___x_3405_, v___x_3403_);
return v___x_3406_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3382_ = stack[0].m_obj;
lean_object* v_as_3383_ = stack[1].m_obj;
size_t v_sz_3384_ = stack[2].m_num;
size_t v_i_3385_ = stack[3].m_num;
lean_object* v_b_3386_ = stack[4].m_obj;
lean_object* v_res_3431_;
v_res_3431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3382_, v_as_3383_, v_sz_3384_, v_i_3385_, v_b_3386_);
stack->m_obj
 = v_res_3431_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_3432_, lean_object* v_as_3433_, lean_object* v_sz_3434_, lean_object* v_i_3435_, lean_object* v_b_3436_){
_start:
{
size_t v_sz_boxed_3437_; size_t v_i_boxed_3438_; lean_object* v_res_3439_; 
v_sz_boxed_3437_ = lean_unbox_usize(v_sz_3434_);
lean_dec(v_sz_3434_);
v_i_boxed_3438_ = lean_unbox_usize(v_i_3435_);
lean_dec(v_i_3435_);
v_res_3439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3432_, v_as_3433_, v_sz_boxed_3437_, v_i_boxed_3438_, v_b_3436_);
lean_dec_ref(v_as_3433_);
lean_dec(v_x_3432_);
return v_res_3439_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_3440_, lean_object* v_as_3441_, size_t v_sz_3442_, size_t v_i_3443_, lean_object* v_b_3444_){
_start:
{
uint8_t v___x_3445_; 
v___x_3445_ = lean_usize_dec_lt(v_i_3443_, v_sz_3442_);
if (v___x_3445_ == 0)
{
return v_b_3444_;
}
else
{
lean_object* v_snd_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3487_; 
v_snd_3446_ = lean_ctor_get(v_b_3444_, 1);
v_isSharedCheck_3487_ = !lean_is_exclusive(v_b_3444_);
if (v_isSharedCheck_3487_ == 0)
{
lean_object* v_unused_3488_; 
v_unused_3488_ = lean_ctor_get(v_b_3444_, 0);
lean_dec(v_unused_3488_);
v___x_3448_ = v_b_3444_;
v_isShared_3449_ = v_isSharedCheck_3487_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_snd_3446_);
lean_dec(v_b_3444_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3487_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v_fst_3450_; lean_object* v_snd_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3486_; 
v_fst_3450_ = lean_ctor_get(v_snd_3446_, 0);
v_snd_3451_ = lean_ctor_get(v_snd_3446_, 1);
v_isSharedCheck_3486_ = !lean_is_exclusive(v_snd_3446_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3453_ = v_snd_3446_;
v_isShared_3454_ = v_isSharedCheck_3486_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_snd_3451_);
lean_inc(v_fst_3450_);
lean_dec(v_snd_3446_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3486_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v_a_3455_; lean_object* v_p_3456_; lean_object* v___x_3457_; lean_object* v_a_3459_; lean_object* v_b_3466_; lean_object* v___x_3467_; uint8_t v___x_3468_; 
v_a_3455_ = lean_array_uget(v_as_3441_, v_i_3443_);
v_p_3456_ = lean_ctor_get(v_a_3455_, 0);
v___x_3457_ = lean_box(0);
v_b_3466_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3456_, v_x_3440_);
v___x_3467_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3468_ = lean_int_dec_eq(v_b_3466_, v___x_3467_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3470_; 
lean_inc(v_a_3455_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 1, v_a_3455_);
lean_ctor_set(v___x_3448_, 0, v_b_3466_);
v___x_3470_ = v___x_3448_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_b_3466_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_a_3455_);
v___x_3470_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3478_; 
v_isSharedCheck_3478_ = !lean_is_exclusive(v_a_3455_);
if (v_isSharedCheck_3478_ == 0)
{
lean_object* v_unused_3479_; lean_object* v_unused_3480_; 
v_unused_3479_ = lean_ctor_get(v_a_3455_, 1);
lean_dec(v_unused_3479_);
v_unused_3480_ = lean_ctor_get(v_a_3455_, 0);
lean_dec(v_unused_3480_);
v___x_3472_ = v_a_3455_;
v_isShared_3473_ = v_isSharedCheck_3478_;
goto v_resetjp_3471_;
}
else
{
lean_dec(v_a_3455_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3478_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v_todo_3474_; lean_object* v___x_3476_; 
v_todo_3474_ = lean_array_push(v_snd_3451_, v___x_3470_);
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 1, v_todo_3474_);
lean_ctor_set(v___x_3472_, 0, v_fst_3450_);
v___x_3476_ = v___x_3472_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_fst_3450_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_todo_3474_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
v_a_3459_ = v___x_3476_;
goto v___jp_3458_;
}
}
}
}
else
{
lean_object* v_cs_x27_3482_; lean_object* v___x_3484_; 
lean_dec(v_b_3466_);
v_cs_x27_3482_ = l_Lean_PersistentArray_push___redArg(v_fst_3450_, v_a_3455_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 1, v_snd_3451_);
lean_ctor_set(v___x_3448_, 0, v_cs_x27_3482_);
v___x_3484_ = v___x_3448_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_cs_x27_3482_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_snd_3451_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
v_a_3459_ = v___x_3484_;
goto v___jp_3458_;
}
}
v___jp_3458_:
{
lean_object* v___x_3461_; 
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 1, v_a_3459_);
lean_ctor_set(v___x_3453_, 0, v___x_3457_);
v___x_3461_ = v___x_3453_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3457_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_a_3459_);
v___x_3461_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
size_t v___x_3462_; size_t v___x_3463_; 
v___x_3462_ = ((size_t)1ULL);
v___x_3463_ = lean_usize_add(v_i_3443_, v___x_3462_);
v_i_3443_ = v___x_3463_;
v_b_3444_ = v___x_3461_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3440_ = stack[0].m_obj;
lean_object* v_as_3441_ = stack[1].m_obj;
size_t v_sz_3442_ = stack[2].m_num;
size_t v_i_3443_ = stack[3].m_num;
lean_object* v_b_3444_ = stack[4].m_obj;
lean_object* v_res_3489_;
v_res_3489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3440_, v_as_3441_, v_sz_3442_, v_i_3443_, v_b_3444_);
stack->m_obj
 = v_res_3489_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3490_, lean_object* v_as_3491_, lean_object* v_sz_3492_, lean_object* v_i_3493_, lean_object* v_b_3494_){
_start:
{
size_t v_sz_boxed_3495_; size_t v_i_boxed_3496_; lean_object* v_res_3497_; 
v_sz_boxed_3495_ = lean_unbox_usize(v_sz_3492_);
lean_dec(v_sz_3492_);
v_i_boxed_3496_ = lean_unbox_usize(v_i_3493_);
lean_dec(v_i_3493_);
v_res_3497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3490_, v_as_3491_, v_sz_boxed_3495_, v_i_boxed_3496_, v_b_3494_);
lean_dec_ref(v_as_3491_);
lean_dec(v_x_3490_);
return v_res_3497_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_3498_, lean_object* v_as_3499_, size_t v_sz_3500_, size_t v_i_3501_, lean_object* v_b_3502_){
_start:
{
uint8_t v___x_3503_; 
v___x_3503_ = lean_usize_dec_lt(v_i_3501_, v_sz_3500_);
if (v___x_3503_ == 0)
{
return v_b_3502_;
}
else
{
lean_object* v_snd_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3545_; 
v_snd_3504_ = lean_ctor_get(v_b_3502_, 1);
v_isSharedCheck_3545_ = !lean_is_exclusive(v_b_3502_);
if (v_isSharedCheck_3545_ == 0)
{
lean_object* v_unused_3546_; 
v_unused_3546_ = lean_ctor_get(v_b_3502_, 0);
lean_dec(v_unused_3546_);
v___x_3506_ = v_b_3502_;
v_isShared_3507_ = v_isSharedCheck_3545_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_snd_3504_);
lean_dec(v_b_3502_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3545_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v_fst_3508_; lean_object* v_snd_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3544_; 
v_fst_3508_ = lean_ctor_get(v_snd_3504_, 0);
v_snd_3509_ = lean_ctor_get(v_snd_3504_, 1);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_snd_3504_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3511_ = v_snd_3504_;
v_isShared_3512_ = v_isSharedCheck_3544_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_snd_3509_);
lean_inc(v_fst_3508_);
lean_dec(v_snd_3504_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3544_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v_a_3513_; lean_object* v_p_3514_; lean_object* v___x_3515_; lean_object* v_a_3517_; lean_object* v_b_3524_; lean_object* v___x_3525_; uint8_t v___x_3526_; 
v_a_3513_ = lean_array_uget(v_as_3499_, v_i_3501_);
v_p_3514_ = lean_ctor_get(v_a_3513_, 0);
v___x_3515_ = lean_box(0);
v_b_3524_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3514_, v_x_3498_);
v___x_3525_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3526_ = lean_int_dec_eq(v_b_3524_, v___x_3525_);
if (v___x_3526_ == 0)
{
lean_object* v___x_3528_; 
lean_inc(v_a_3513_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 1, v_a_3513_);
lean_ctor_set(v___x_3506_, 0, v_b_3524_);
v___x_3528_ = v___x_3506_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_b_3524_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_a_3513_);
v___x_3528_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3536_; 
v_isSharedCheck_3536_ = !lean_is_exclusive(v_a_3513_);
if (v_isSharedCheck_3536_ == 0)
{
lean_object* v_unused_3537_; lean_object* v_unused_3538_; 
v_unused_3537_ = lean_ctor_get(v_a_3513_, 1);
lean_dec(v_unused_3537_);
v_unused_3538_ = lean_ctor_get(v_a_3513_, 0);
lean_dec(v_unused_3538_);
v___x_3530_ = v_a_3513_;
v_isShared_3531_ = v_isSharedCheck_3536_;
goto v_resetjp_3529_;
}
else
{
lean_dec(v_a_3513_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3536_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v_todo_3532_; lean_object* v___x_3534_; 
v_todo_3532_ = lean_array_push(v_snd_3509_, v___x_3528_);
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 1, v_todo_3532_);
lean_ctor_set(v___x_3530_, 0, v_fst_3508_);
v___x_3534_ = v___x_3530_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_fst_3508_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v_todo_3532_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
v_a_3517_ = v___x_3534_;
goto v___jp_3516_;
}
}
}
}
else
{
lean_object* v_cs_x27_3540_; lean_object* v___x_3542_; 
lean_dec(v_b_3524_);
v_cs_x27_3540_ = l_Lean_PersistentArray_push___redArg(v_fst_3508_, v_a_3513_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 1, v_snd_3509_);
lean_ctor_set(v___x_3506_, 0, v_cs_x27_3540_);
v___x_3542_ = v___x_3506_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_cs_x27_3540_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v_snd_3509_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
v_a_3517_ = v___x_3542_;
goto v___jp_3516_;
}
}
v___jp_3516_:
{
lean_object* v___x_3519_; 
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 1, v_a_3517_);
lean_ctor_set(v___x_3511_, 0, v___x_3515_);
v___x_3519_ = v___x_3511_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3515_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v_a_3517_);
v___x_3519_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
size_t v___x_3520_; size_t v___x_3521_; lean_object* v___x_3522_; 
v___x_3520_ = ((size_t)1ULL);
v___x_3521_ = lean_usize_add(v_i_3501_, v___x_3520_);
v___x_3522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3498_, v_as_3499_, v_sz_3500_, v___x_3521_, v___x_3519_);
return v___x_3522_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3498_ = stack[0].m_obj;
lean_object* v_as_3499_ = stack[1].m_obj;
size_t v_sz_3500_ = stack[2].m_num;
size_t v_i_3501_ = stack[3].m_num;
lean_object* v_b_3502_ = stack[4].m_obj;
lean_object* v_res_3547_;
v_res_3547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3498_, v_as_3499_, v_sz_3500_, v_i_3501_, v_b_3502_);
stack->m_obj
 = v_res_3547_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_3548_, lean_object* v_as_3549_, lean_object* v_sz_3550_, lean_object* v_i_3551_, lean_object* v_b_3552_){
_start:
{
size_t v_sz_boxed_3553_; size_t v_i_boxed_3554_; lean_object* v_res_3555_; 
v_sz_boxed_3553_ = lean_unbox_usize(v_sz_3550_);
lean_dec(v_sz_3550_);
v_i_boxed_3554_ = lean_unbox_usize(v_i_3551_);
lean_dec(v_i_3551_);
v_res_3555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3548_, v_as_3549_, v_sz_boxed_3553_, v_i_boxed_3554_, v_b_3552_);
lean_dec_ref(v_as_3549_);
lean_dec(v_x_3548_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(lean_object* v_init_3556_, lean_object* v_x_3557_, lean_object* v_n_3558_, lean_object* v_b_3559_){
_start:
{
if (lean_obj_tag(v_n_3558_) == 0)
{
lean_object* v_cs_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; size_t v_sz_3563_; size_t v___x_3564_; lean_object* v___x_3565_; lean_object* v_fst_3566_; 
v_cs_3560_ = lean_ctor_get(v_n_3558_, 0);
v___x_3561_ = lean_box(0);
v___x_3562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3561_);
lean_ctor_set(v___x_3562_, 1, v_b_3559_);
v_sz_3563_ = lean_array_size(v_cs_3560_);
v___x_3564_ = ((size_t)0ULL);
v___x_3565_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3556_, v_x_3557_, v_cs_3560_, v_sz_3563_, v___x_3564_, v___x_3562_);
v_fst_3566_ = lean_ctor_get(v___x_3565_, 0);
if (lean_obj_tag(v_fst_3566_) == 0)
{
lean_object* v_snd_3567_; lean_object* v___x_3568_; 
v_snd_3567_ = lean_ctor_get(v___x_3565_, 1);
lean_inc(v_snd_3567_);
lean_dec_ref(v___x_3565_);
v___x_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3568_, 0, v_snd_3567_);
return v___x_3568_;
}
else
{
lean_object* v_val_3569_; 
lean_inc_ref(v_fst_3566_);
lean_dec_ref(v___x_3565_);
v_val_3569_ = lean_ctor_get(v_fst_3566_, 0);
lean_inc(v_val_3569_);
lean_dec_ref_known(v_fst_3566_, 1);
return v_val_3569_;
}
}
else
{
lean_object* v_vs_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; size_t v_sz_3573_; size_t v___x_3574_; lean_object* v___x_3575_; lean_object* v_fst_3576_; 
v_vs_3570_ = lean_ctor_get(v_n_3558_, 0);
v___x_3571_ = lean_box(0);
v___x_3572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3571_);
lean_ctor_set(v___x_3572_, 1, v_b_3559_);
v_sz_3573_ = lean_array_size(v_vs_3570_);
v___x_3574_ = ((size_t)0ULL);
v___x_3575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3557_, v_vs_3570_, v_sz_3573_, v___x_3574_, v___x_3572_);
v_fst_3576_ = lean_ctor_get(v___x_3575_, 0);
if (lean_obj_tag(v_fst_3576_) == 0)
{
lean_object* v_snd_3577_; lean_object* v___x_3578_; 
v_snd_3577_ = lean_ctor_get(v___x_3575_, 1);
lean_inc(v_snd_3577_);
lean_dec_ref(v___x_3575_);
v___x_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3578_, 0, v_snd_3577_);
return v___x_3578_;
}
else
{
lean_object* v_val_3579_; 
lean_inc_ref(v_fst_3576_);
lean_dec_ref(v___x_3575_);
v_val_3579_ = lean_ctor_get(v_fst_3576_, 0);
lean_inc(v_val_3579_);
lean_dec_ref_known(v_fst_3576_, 1);
return v_val_3579_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3580_, lean_object* v_x_3581_, lean_object* v_as_3582_, size_t v_sz_3583_, size_t v_i_3584_, lean_object* v_b_3585_){
_start:
{
uint8_t v___x_3586_; 
v___x_3586_ = lean_usize_dec_lt(v_i_3584_, v_sz_3583_);
if (v___x_3586_ == 0)
{
return v_b_3585_;
}
else
{
lean_object* v_snd_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3605_; 
v_snd_3587_ = lean_ctor_get(v_b_3585_, 1);
v_isSharedCheck_3605_ = !lean_is_exclusive(v_b_3585_);
if (v_isSharedCheck_3605_ == 0)
{
lean_object* v_unused_3606_; 
v_unused_3606_ = lean_ctor_get(v_b_3585_, 0);
lean_dec(v_unused_3606_);
v___x_3589_ = v_b_3585_;
v_isShared_3590_ = v_isSharedCheck_3605_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_snd_3587_);
lean_dec(v_b_3585_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3605_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v_a_3591_; lean_object* v___x_3592_; 
v_a_3591_ = lean_array_uget_borrowed(v_as_3582_, v_i_3584_);
lean_inc(v_snd_3587_);
v___x_3592_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3580_, v_x_3581_, v_a_3591_, v_snd_3587_);
if (lean_obj_tag(v___x_3592_) == 0)
{
lean_object* v___x_3593_; lean_object* v___x_3595_; 
v___x_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 0, v___x_3593_);
v___x_3595_ = v___x_3589_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3593_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_snd_3587_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
else
{
lean_object* v_a_3597_; lean_object* v___x_3598_; lean_object* v___x_3600_; 
lean_dec(v_snd_3587_);
v_a_3597_ = lean_ctor_get(v___x_3592_, 0);
lean_inc(v_a_3597_);
lean_dec_ref_known(v___x_3592_, 1);
v___x_3598_ = lean_box(0);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 1, v_a_3597_);
lean_ctor_set(v___x_3589_, 0, v___x_3598_);
v___x_3600_ = v___x_3589_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3598_);
lean_ctor_set(v_reuseFailAlloc_3604_, 1, v_a_3597_);
v___x_3600_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
size_t v___x_3601_; size_t v___x_3602_; 
v___x_3601_ = ((size_t)1ULL);
v___x_3602_ = lean_usize_add(v_i_3584_, v___x_3601_);
v_i_3584_ = v___x_3602_;
v_b_3585_ = v___x_3600_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3580_ = stack[0].m_obj;
lean_object* v_x_3581_ = stack[1].m_obj;
lean_object* v_as_3582_ = stack[2].m_obj;
size_t v_sz_3583_ = stack[3].m_num;
size_t v_i_3584_ = stack[4].m_num;
lean_object* v_b_3585_ = stack[5].m_obj;
lean_object* v_res_3607_;
v_res_3607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3580_, v_x_3581_, v_as_3582_, v_sz_3583_, v_i_3584_, v_b_3585_);
stack->m_obj
 = v_res_3607_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3608_, lean_object* v_x_3609_, lean_object* v_as_3610_, lean_object* v_sz_3611_, lean_object* v_i_3612_, lean_object* v_b_3613_){
_start:
{
size_t v_sz_boxed_3614_; size_t v_i_boxed_3615_; lean_object* v_res_3616_; 
v_sz_boxed_3614_ = lean_unbox_usize(v_sz_3611_);
lean_dec(v_sz_3611_);
v_i_boxed_3615_ = lean_unbox_usize(v_i_3612_);
lean_dec(v_i_3612_);
v_res_3616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3608_, v_x_3609_, v_as_3610_, v_sz_boxed_3614_, v_i_boxed_3615_, v_b_3613_);
lean_dec_ref(v_as_3610_);
lean_dec(v_x_3609_);
lean_dec_ref(v_init_3608_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3617_, lean_object* v_x_3618_, lean_object* v_n_3619_, lean_object* v_b_3620_){
_start:
{
lean_object* v_res_3621_; 
v_res_3621_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3617_, v_x_3618_, v_n_3619_, v_b_3620_);
lean_dec_ref(v_n_3619_);
lean_dec(v_x_3618_);
lean_dec_ref(v_init_3617_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object* v_x_3622_, lean_object* v_t_3623_, lean_object* v_init_3624_){
_start:
{
lean_object* v_root_3625_; lean_object* v_tail_3626_; lean_object* v___x_3627_; 
v_root_3625_ = lean_ctor_get(v_t_3623_, 0);
v_tail_3626_ = lean_ctor_get(v_t_3623_, 1);
lean_inc_ref(v_init_3624_);
v___x_3627_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3624_, v_x_3622_, v_root_3625_, v_init_3624_);
lean_dec_ref(v_init_3624_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_a_3628_; 
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
lean_inc(v_a_3628_);
lean_dec_ref_known(v___x_3627_, 1);
return v_a_3628_;
}
else
{
lean_object* v_a_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; size_t v_sz_3632_; size_t v___x_3633_; lean_object* v___x_3634_; lean_object* v_fst_3635_; 
v_a_3629_ = lean_ctor_get(v___x_3627_, 0);
lean_inc(v_a_3629_);
lean_dec_ref_known(v___x_3627_, 1);
v___x_3630_ = lean_box(0);
v___x_3631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3630_);
lean_ctor_set(v___x_3631_, 1, v_a_3629_);
v_sz_3632_ = lean_array_size(v_tail_3626_);
v___x_3633_ = ((size_t)0ULL);
v___x_3634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3622_, v_tail_3626_, v_sz_3632_, v___x_3633_, v___x_3631_);
v_fst_3635_ = lean_ctor_get(v___x_3634_, 0);
if (lean_obj_tag(v_fst_3635_) == 0)
{
lean_object* v_snd_3636_; 
v_snd_3636_ = lean_ctor_get(v___x_3634_, 1);
lean_inc(v_snd_3636_);
lean_dec_ref(v___x_3634_);
return v_snd_3636_;
}
else
{
lean_object* v_val_3637_; 
lean_inc_ref(v_fst_3635_);
lean_dec_ref(v___x_3634_);
v_val_3637_ = lean_ctor_get(v_fst_3635_, 0);
lean_inc(v_val_3637_);
lean_dec_ref_known(v_fst_3635_, 1);
return v_val_3637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object* v_x_3638_, lean_object* v_t_3639_, lean_object* v_init_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3638_, v_t_3639_, v_init_3640_);
lean_dec_ref(v_t_3639_);
lean_dec(v_x_3638_);
return v_res_3641_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3642_ = lean_unsigned_to_nat(32u);
v___x_3643_ = lean_mk_empty_array_with_capacity(v___x_3642_);
v___x_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
return v___x_3644_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1(void){
_start:
{
size_t v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v_cs_x27_3650_; 
v___x_3645_ = ((size_t)5ULL);
v___x_3646_ = lean_unsigned_to_nat(0u);
v___x_3647_ = lean_unsigned_to_nat(32u);
v___x_3648_ = lean_mk_empty_array_with_capacity(v___x_3647_);
v___x_3649_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0);
v_cs_x27_3650_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_3650_, 0, v___x_3649_);
lean_ctor_set(v_cs_x27_3650_, 1, v___x_3648_);
lean_ctor_set(v_cs_x27_3650_, 2, v___x_3646_);
lean_ctor_set(v_cs_x27_3650_, 3, v___x_3646_);
lean_ctor_set_usize(v_cs_x27_3650_, 4, v___x_3645_);
return v_cs_x27_3650_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_3653_; lean_object* v_cs_x27_3654_; lean_object* v___x_3655_; 
v_todo_3653_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2));
v_cs_x27_3654_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1);
v___x_3655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3655_, 0, v_cs_x27_3654_);
lean_ctor_set(v___x_3655_, 1, v_todo_3653_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object* v_x_3656_, lean_object* v_cs_3657_){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v_fst_3660_; lean_object* v_snd_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
v___x_3658_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3);
v___x_3659_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3656_, v_cs_3657_, v___x_3658_);
v_fst_3660_ = lean_ctor_get(v___x_3659_, 0);
v_snd_3661_ = lean_ctor_get(v___x_3659_, 1);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3659_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_snd_3661_);
lean_inc(v_fst_3660_);
lean_dec(v___x_3659_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
if (v_isShared_3664_ == 0)
{
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_fst_3660_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_snd_3661_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object* v_x_3669_, lean_object* v_cs_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3669_, v_cs_3670_);
lean_dec_ref(v_cs_3670_);
lean_dec(v_x_3669_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object* v_x_3672_, lean_object* v_cs_3673_){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3672_, v_cs_3673_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object* v_x_3675_, lean_object* v_cs_3676_){
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(v_x_3675_, v_cs_3676_);
lean_dec_ref(v_cs_3676_);
lean_dec(v_x_3675_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(lean_object* v_a_3678_, lean_object* v_y_3679_, lean_object* v_fst_3680_, lean_object* v_s_3681_){
_start:
{
lean_object* v_structs_3682_; lean_object* v_typeIdOf_3683_; lean_object* v_exprToStructId_3684_; lean_object* v_exprToStructIdEntries_3685_; lean_object* v_forbiddenNatModules_3686_; lean_object* v_natStructs_3687_; lean_object* v_natTypeIdOf_3688_; lean_object* v_exprToNatStructId_3689_; lean_object* v___x_3690_; uint8_t v___x_3691_; 
v_structs_3682_ = lean_ctor_get(v_s_3681_, 0);
v_typeIdOf_3683_ = lean_ctor_get(v_s_3681_, 1);
v_exprToStructId_3684_ = lean_ctor_get(v_s_3681_, 2);
v_exprToStructIdEntries_3685_ = lean_ctor_get(v_s_3681_, 3);
v_forbiddenNatModules_3686_ = lean_ctor_get(v_s_3681_, 4);
v_natStructs_3687_ = lean_ctor_get(v_s_3681_, 5);
v_natTypeIdOf_3688_ = lean_ctor_get(v_s_3681_, 6);
v_exprToNatStructId_3689_ = lean_ctor_get(v_s_3681_, 7);
v___x_3690_ = lean_array_get_size(v_structs_3682_);
v___x_3691_ = lean_nat_dec_lt(v_a_3678_, v___x_3690_);
if (v___x_3691_ == 0)
{
lean_dec_ref(v_fst_3680_);
return v_s_3681_;
}
else
{
lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3753_; 
lean_inc_ref(v_exprToNatStructId_3689_);
lean_inc_ref(v_natTypeIdOf_3688_);
lean_inc_ref(v_natStructs_3687_);
lean_inc_ref(v_forbiddenNatModules_3686_);
lean_inc_ref(v_exprToStructIdEntries_3685_);
lean_inc_ref(v_exprToStructId_3684_);
lean_inc_ref(v_typeIdOf_3683_);
lean_inc_ref(v_structs_3682_);
v_isSharedCheck_3753_ = !lean_is_exclusive(v_s_3681_);
if (v_isSharedCheck_3753_ == 0)
{
lean_object* v_unused_3754_; lean_object* v_unused_3755_; lean_object* v_unused_3756_; lean_object* v_unused_3757_; lean_object* v_unused_3758_; lean_object* v_unused_3759_; lean_object* v_unused_3760_; lean_object* v_unused_3761_; 
v_unused_3754_ = lean_ctor_get(v_s_3681_, 7);
lean_dec(v_unused_3754_);
v_unused_3755_ = lean_ctor_get(v_s_3681_, 6);
lean_dec(v_unused_3755_);
v_unused_3756_ = lean_ctor_get(v_s_3681_, 5);
lean_dec(v_unused_3756_);
v_unused_3757_ = lean_ctor_get(v_s_3681_, 4);
lean_dec(v_unused_3757_);
v_unused_3758_ = lean_ctor_get(v_s_3681_, 3);
lean_dec(v_unused_3758_);
v_unused_3759_ = lean_ctor_get(v_s_3681_, 2);
lean_dec(v_unused_3759_);
v_unused_3760_ = lean_ctor_get(v_s_3681_, 1);
lean_dec(v_unused_3760_);
v_unused_3761_ = lean_ctor_get(v_s_3681_, 0);
lean_dec(v_unused_3761_);
v___x_3693_ = v_s_3681_;
v_isShared_3694_ = v_isSharedCheck_3753_;
goto v_resetjp_3692_;
}
else
{
lean_dec(v_s_3681_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3753_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v_v_3695_; lean_object* v_id_3696_; lean_object* v_ringId_x3f_3697_; lean_object* v_type_3698_; lean_object* v_u_3699_; lean_object* v_intModuleInst_3700_; lean_object* v_leInst_x3f_3701_; lean_object* v_ltInst_x3f_3702_; lean_object* v_lawfulOrderLTInst_x3f_3703_; lean_object* v_isPreorderInst_x3f_3704_; lean_object* v_orderedAddInst_x3f_3705_; lean_object* v_isLinearInst_x3f_3706_; lean_object* v_noNatDivInst_x3f_3707_; lean_object* v_ringInst_x3f_3708_; lean_object* v_commRingInst_x3f_3709_; lean_object* v_orderedRingInst_x3f_3710_; lean_object* v_fieldInst_x3f_3711_; lean_object* v_charInst_x3f_3712_; lean_object* v_zero_3713_; lean_object* v_ofNatZero_3714_; lean_object* v_one_x3f_3715_; lean_object* v_leFn_x3f_3716_; lean_object* v_ltFn_x3f_3717_; lean_object* v_addFn_3718_; lean_object* v_zsmulFn_3719_; lean_object* v_nsmulFn_3720_; lean_object* v_zsmulFn_x3f_3721_; lean_object* v_nsmulFn_x3f_3722_; lean_object* v_homomulFn_x3f_3723_; lean_object* v_subFn_3724_; lean_object* v_negFn_3725_; lean_object* v_vars_3726_; lean_object* v_varMap_3727_; lean_object* v_lowers_3728_; lean_object* v_uppers_3729_; lean_object* v_diseqs_3730_; lean_object* v_assignment_3731_; uint8_t v_caseSplits_3732_; lean_object* v_conflict_x3f_3733_; lean_object* v_diseqSplits_3734_; lean_object* v_elimEqs_3735_; lean_object* v_elimStack_3736_; lean_object* v_occurs_3737_; lean_object* v_ignored_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3752_; 
v_v_3695_ = lean_array_fget(v_structs_3682_, v_a_3678_);
v_id_3696_ = lean_ctor_get(v_v_3695_, 0);
v_ringId_x3f_3697_ = lean_ctor_get(v_v_3695_, 1);
v_type_3698_ = lean_ctor_get(v_v_3695_, 2);
v_u_3699_ = lean_ctor_get(v_v_3695_, 3);
v_intModuleInst_3700_ = lean_ctor_get(v_v_3695_, 4);
v_leInst_x3f_3701_ = lean_ctor_get(v_v_3695_, 5);
v_ltInst_x3f_3702_ = lean_ctor_get(v_v_3695_, 6);
v_lawfulOrderLTInst_x3f_3703_ = lean_ctor_get(v_v_3695_, 7);
v_isPreorderInst_x3f_3704_ = lean_ctor_get(v_v_3695_, 8);
v_orderedAddInst_x3f_3705_ = lean_ctor_get(v_v_3695_, 9);
v_isLinearInst_x3f_3706_ = lean_ctor_get(v_v_3695_, 10);
v_noNatDivInst_x3f_3707_ = lean_ctor_get(v_v_3695_, 11);
v_ringInst_x3f_3708_ = lean_ctor_get(v_v_3695_, 12);
v_commRingInst_x3f_3709_ = lean_ctor_get(v_v_3695_, 13);
v_orderedRingInst_x3f_3710_ = lean_ctor_get(v_v_3695_, 14);
v_fieldInst_x3f_3711_ = lean_ctor_get(v_v_3695_, 15);
v_charInst_x3f_3712_ = lean_ctor_get(v_v_3695_, 16);
v_zero_3713_ = lean_ctor_get(v_v_3695_, 17);
v_ofNatZero_3714_ = lean_ctor_get(v_v_3695_, 18);
v_one_x3f_3715_ = lean_ctor_get(v_v_3695_, 19);
v_leFn_x3f_3716_ = lean_ctor_get(v_v_3695_, 20);
v_ltFn_x3f_3717_ = lean_ctor_get(v_v_3695_, 21);
v_addFn_3718_ = lean_ctor_get(v_v_3695_, 22);
v_zsmulFn_3719_ = lean_ctor_get(v_v_3695_, 23);
v_nsmulFn_3720_ = lean_ctor_get(v_v_3695_, 24);
v_zsmulFn_x3f_3721_ = lean_ctor_get(v_v_3695_, 25);
v_nsmulFn_x3f_3722_ = lean_ctor_get(v_v_3695_, 26);
v_homomulFn_x3f_3723_ = lean_ctor_get(v_v_3695_, 27);
v_subFn_3724_ = lean_ctor_get(v_v_3695_, 28);
v_negFn_3725_ = lean_ctor_get(v_v_3695_, 29);
v_vars_3726_ = lean_ctor_get(v_v_3695_, 30);
v_varMap_3727_ = lean_ctor_get(v_v_3695_, 31);
v_lowers_3728_ = lean_ctor_get(v_v_3695_, 32);
v_uppers_3729_ = lean_ctor_get(v_v_3695_, 33);
v_diseqs_3730_ = lean_ctor_get(v_v_3695_, 34);
v_assignment_3731_ = lean_ctor_get(v_v_3695_, 35);
v_caseSplits_3732_ = lean_ctor_get_uint8(v_v_3695_, sizeof(void*)*42);
v_conflict_x3f_3733_ = lean_ctor_get(v_v_3695_, 36);
v_diseqSplits_3734_ = lean_ctor_get(v_v_3695_, 37);
v_elimEqs_3735_ = lean_ctor_get(v_v_3695_, 38);
v_elimStack_3736_ = lean_ctor_get(v_v_3695_, 39);
v_occurs_3737_ = lean_ctor_get(v_v_3695_, 40);
v_ignored_3738_ = lean_ctor_get(v_v_3695_, 41);
v_isSharedCheck_3752_ = !lean_is_exclusive(v_v_3695_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3740_ = v_v_3695_;
v_isShared_3741_ = v_isSharedCheck_3752_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_ignored_3738_);
lean_inc(v_occurs_3737_);
lean_inc(v_elimStack_3736_);
lean_inc(v_elimEqs_3735_);
lean_inc(v_diseqSplits_3734_);
lean_inc(v_conflict_x3f_3733_);
lean_inc(v_assignment_3731_);
lean_inc(v_diseqs_3730_);
lean_inc(v_uppers_3729_);
lean_inc(v_lowers_3728_);
lean_inc(v_varMap_3727_);
lean_inc(v_vars_3726_);
lean_inc(v_negFn_3725_);
lean_inc(v_subFn_3724_);
lean_inc(v_homomulFn_x3f_3723_);
lean_inc(v_nsmulFn_x3f_3722_);
lean_inc(v_zsmulFn_x3f_3721_);
lean_inc(v_nsmulFn_3720_);
lean_inc(v_zsmulFn_3719_);
lean_inc(v_addFn_3718_);
lean_inc(v_ltFn_x3f_3717_);
lean_inc(v_leFn_x3f_3716_);
lean_inc(v_one_x3f_3715_);
lean_inc(v_ofNatZero_3714_);
lean_inc(v_zero_3713_);
lean_inc(v_charInst_x3f_3712_);
lean_inc(v_fieldInst_x3f_3711_);
lean_inc(v_orderedRingInst_x3f_3710_);
lean_inc(v_commRingInst_x3f_3709_);
lean_inc(v_ringInst_x3f_3708_);
lean_inc(v_noNatDivInst_x3f_3707_);
lean_inc(v_isLinearInst_x3f_3706_);
lean_inc(v_orderedAddInst_x3f_3705_);
lean_inc(v_isPreorderInst_x3f_3704_);
lean_inc(v_lawfulOrderLTInst_x3f_3703_);
lean_inc(v_ltInst_x3f_3702_);
lean_inc(v_leInst_x3f_3701_);
lean_inc(v_intModuleInst_3700_);
lean_inc(v_u_3699_);
lean_inc(v_type_3698_);
lean_inc(v_ringId_x3f_3697_);
lean_inc(v_id_3696_);
lean_dec(v_v_3695_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3752_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3742_; lean_object* v_xs_x27_3743_; lean_object* v___x_3744_; lean_object* v___x_3746_; 
v___x_3742_ = lean_box(0);
v_xs_x27_3743_ = lean_array_fset(v_structs_3682_, v_a_3678_, v___x_3742_);
v___x_3744_ = l_Lean_PersistentArray_set___redArg(v_diseqs_3730_, v_y_3679_, v_fst_3680_);
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 34, v___x_3744_);
v___x_3746_ = v___x_3740_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_id_3696_);
lean_ctor_set(v_reuseFailAlloc_3751_, 1, v_ringId_x3f_3697_);
lean_ctor_set(v_reuseFailAlloc_3751_, 2, v_type_3698_);
lean_ctor_set(v_reuseFailAlloc_3751_, 3, v_u_3699_);
lean_ctor_set(v_reuseFailAlloc_3751_, 4, v_intModuleInst_3700_);
lean_ctor_set(v_reuseFailAlloc_3751_, 5, v_leInst_x3f_3701_);
lean_ctor_set(v_reuseFailAlloc_3751_, 6, v_ltInst_x3f_3702_);
lean_ctor_set(v_reuseFailAlloc_3751_, 7, v_lawfulOrderLTInst_x3f_3703_);
lean_ctor_set(v_reuseFailAlloc_3751_, 8, v_isPreorderInst_x3f_3704_);
lean_ctor_set(v_reuseFailAlloc_3751_, 9, v_orderedAddInst_x3f_3705_);
lean_ctor_set(v_reuseFailAlloc_3751_, 10, v_isLinearInst_x3f_3706_);
lean_ctor_set(v_reuseFailAlloc_3751_, 11, v_noNatDivInst_x3f_3707_);
lean_ctor_set(v_reuseFailAlloc_3751_, 12, v_ringInst_x3f_3708_);
lean_ctor_set(v_reuseFailAlloc_3751_, 13, v_commRingInst_x3f_3709_);
lean_ctor_set(v_reuseFailAlloc_3751_, 14, v_orderedRingInst_x3f_3710_);
lean_ctor_set(v_reuseFailAlloc_3751_, 15, v_fieldInst_x3f_3711_);
lean_ctor_set(v_reuseFailAlloc_3751_, 16, v_charInst_x3f_3712_);
lean_ctor_set(v_reuseFailAlloc_3751_, 17, v_zero_3713_);
lean_ctor_set(v_reuseFailAlloc_3751_, 18, v_ofNatZero_3714_);
lean_ctor_set(v_reuseFailAlloc_3751_, 19, v_one_x3f_3715_);
lean_ctor_set(v_reuseFailAlloc_3751_, 20, v_leFn_x3f_3716_);
lean_ctor_set(v_reuseFailAlloc_3751_, 21, v_ltFn_x3f_3717_);
lean_ctor_set(v_reuseFailAlloc_3751_, 22, v_addFn_3718_);
lean_ctor_set(v_reuseFailAlloc_3751_, 23, v_zsmulFn_3719_);
lean_ctor_set(v_reuseFailAlloc_3751_, 24, v_nsmulFn_3720_);
lean_ctor_set(v_reuseFailAlloc_3751_, 25, v_zsmulFn_x3f_3721_);
lean_ctor_set(v_reuseFailAlloc_3751_, 26, v_nsmulFn_x3f_3722_);
lean_ctor_set(v_reuseFailAlloc_3751_, 27, v_homomulFn_x3f_3723_);
lean_ctor_set(v_reuseFailAlloc_3751_, 28, v_subFn_3724_);
lean_ctor_set(v_reuseFailAlloc_3751_, 29, v_negFn_3725_);
lean_ctor_set(v_reuseFailAlloc_3751_, 30, v_vars_3726_);
lean_ctor_set(v_reuseFailAlloc_3751_, 31, v_varMap_3727_);
lean_ctor_set(v_reuseFailAlloc_3751_, 32, v_lowers_3728_);
lean_ctor_set(v_reuseFailAlloc_3751_, 33, v_uppers_3729_);
lean_ctor_set(v_reuseFailAlloc_3751_, 34, v___x_3744_);
lean_ctor_set(v_reuseFailAlloc_3751_, 35, v_assignment_3731_);
lean_ctor_set(v_reuseFailAlloc_3751_, 36, v_conflict_x3f_3733_);
lean_ctor_set(v_reuseFailAlloc_3751_, 37, v_diseqSplits_3734_);
lean_ctor_set(v_reuseFailAlloc_3751_, 38, v_elimEqs_3735_);
lean_ctor_set(v_reuseFailAlloc_3751_, 39, v_elimStack_3736_);
lean_ctor_set(v_reuseFailAlloc_3751_, 40, v_occurs_3737_);
lean_ctor_set(v_reuseFailAlloc_3751_, 41, v_ignored_3738_);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, sizeof(void*)*42, v_caseSplits_3732_);
v___x_3746_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
lean_object* v___x_3747_; lean_object* v___x_3749_; 
v___x_3747_ = lean_array_fset(v_xs_x27_3743_, v_a_3678_, v___x_3746_);
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 0, v___x_3747_);
v___x_3749_ = v___x_3693_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3747_);
lean_ctor_set(v_reuseFailAlloc_3750_, 1, v_typeIdOf_3683_);
lean_ctor_set(v_reuseFailAlloc_3750_, 2, v_exprToStructId_3684_);
lean_ctor_set(v_reuseFailAlloc_3750_, 3, v_exprToStructIdEntries_3685_);
lean_ctor_set(v_reuseFailAlloc_3750_, 4, v_forbiddenNatModules_3686_);
lean_ctor_set(v_reuseFailAlloc_3750_, 5, v_natStructs_3687_);
lean_ctor_set(v_reuseFailAlloc_3750_, 6, v_natTypeIdOf_3688_);
lean_ctor_set(v_reuseFailAlloc_3750_, 7, v_exprToNatStructId_3689_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed(lean_object* v_a_3762_, lean_object* v_y_3763_, lean_object* v_fst_3764_, lean_object* v_s_3765_){
_start:
{
lean_object* v_res_3766_; 
v_res_3766_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(v_a_3762_, v_y_3763_, v_fst_3764_, v_s_3765_);
lean_dec(v_y_3763_);
lean_dec(v_a_3762_);
return v_res_3766_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object* v_a_3767_, lean_object* v_x_3768_, lean_object* v_c_3769_, lean_object* v_as_3770_, size_t v_sz_3771_, size_t v_i_3772_, lean_object* v_b_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v_a_3787_; uint8_t v___x_3791_; 
v___x_3791_ = lean_usize_dec_lt(v_i_3772_, v_sz_3771_);
if (v___x_3791_ == 0)
{
lean_object* v___x_3792_; 
lean_dec_ref(v_c_3769_);
v___x_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3792_, 0, v_b_3773_);
return v___x_3792_;
}
else
{
lean_object* v_a_3793_; lean_object* v_fst_3794_; lean_object* v_snd_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
lean_dec_ref(v_b_3773_);
v_a_3793_ = lean_array_uget_borrowed(v_as_3770_, v_i_3772_);
v_fst_3794_ = lean_ctor_get(v_a_3793_, 0);
v_snd_3795_ = lean_ctor_get(v_a_3793_, 1);
v___x_3796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
lean_inc(v_snd_3795_);
lean_inc(v_fst_3794_);
lean_inc_ref(v_c_3769_);
v___x_3797_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_3767_, v_x_3768_, v_c_3769_, v_fst_3794_, v_snd_3795_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref_known(v___x_3797_, 1);
if (lean_obj_tag(v_a_3798_) == 1)
{
lean_object* v_val_3799_; lean_object* v___x_3800_; 
v_val_3799_ = lean_ctor_get(v_a_3798_, 0);
lean_inc(v_val_3799_);
lean_dec_ref_known(v_a_3798_, 1);
v___x_3800_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_val_3799_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v___x_3801_; 
lean_dec_ref_known(v___x_3800_, 1);
v___x_3801_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3811_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3804_ = v___x_3801_;
v_isShared_3805_ = v_isSharedCheck_3811_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3801_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3811_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
uint8_t v___x_3806_; 
v___x_3806_ = lean_unbox(v_a_3802_);
lean_dec(v_a_3802_);
if (v___x_3806_ == 0)
{
lean_del_object(v___x_3804_);
v_a_3787_ = v___x_3796_;
goto v___jp_3786_;
}
else
{
lean_object* v___x_3807_; lean_object* v___x_3809_; 
lean_dec_ref(v_c_3769_);
v___x_3807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v___x_3807_);
v___x_3809_ = v___x_3804_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3807_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_dec_ref(v_c_3769_);
v_a_3812_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3801_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3801_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
lean_dec_ref(v_c_3769_);
v_a_3820_ = lean_ctor_get(v___x_3800_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3800_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3800_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3820_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
else
{
lean_object* v___x_3828_; 
lean_dec(v_a_3798_);
v___x_3828_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_snd_3795_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_dec_ref_known(v___x_3828_, 1);
v_a_3787_ = v___x_3796_;
goto v___jp_3786_;
}
else
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
lean_dec_ref(v_c_3769_);
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___x_3828_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3828_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
lean_dec_ref(v_c_3769_);
v_a_3837_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3797_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3797_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
v___jp_3786_:
{
size_t v___x_3788_; size_t v___x_3789_; 
v___x_3788_ = ((size_t)1ULL);
v___x_3789_ = lean_usize_add(v_i_3772_, v___x_3788_);
lean_inc_ref(v_a_3787_);
v_i_3772_ = v___x_3789_;
v_b_3773_ = v_a_3787_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3767_ = stack[0].m_obj;
lean_object* v_x_3768_ = stack[1].m_obj;
lean_object* v_c_3769_ = stack[2].m_obj;
lean_object* v_as_3770_ = stack[3].m_obj;
size_t v_sz_3771_ = stack[4].m_num;
size_t v_i_3772_ = stack[5].m_num;
lean_object* v_b_3773_ = stack[6].m_obj;
lean_object* v___y_3774_ = stack[7].m_obj;
lean_object* v___y_3775_ = stack[8].m_obj;
lean_object* v___y_3776_ = stack[9].m_obj;
lean_object* v___y_3777_ = stack[10].m_obj;
lean_object* v___y_3778_ = stack[11].m_obj;
lean_object* v___y_3779_ = stack[12].m_obj;
lean_object* v___y_3780_ = stack[13].m_obj;
lean_object* v___y_3781_ = stack[14].m_obj;
lean_object* v___y_3782_ = stack[15].m_obj;
lean_object* v___y_3783_ = stack[16].m_obj;
lean_object* v___y_3784_ = stack[17].m_obj;
lean_object* v_res_3845_;
v_res_3845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3767_, v_x_3768_, v_c_3769_, v_as_3770_, v_sz_3771_, v_i_3772_, v_b_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
stack->m_obj
 = v_res_3845_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object** _args){
lean_object* v_a_3846_ = _args[0];
lean_object* v_x_3847_ = _args[1];
lean_object* v_c_3848_ = _args[2];
lean_object* v_as_3849_ = _args[3];
lean_object* v_sz_3850_ = _args[4];
lean_object* v_i_3851_ = _args[5];
lean_object* v_b_3852_ = _args[6];
lean_object* v___y_3853_ = _args[7];
lean_object* v___y_3854_ = _args[8];
lean_object* v___y_3855_ = _args[9];
lean_object* v___y_3856_ = _args[10];
lean_object* v___y_3857_ = _args[11];
lean_object* v___y_3858_ = _args[12];
lean_object* v___y_3859_ = _args[13];
lean_object* v___y_3860_ = _args[14];
lean_object* v___y_3861_ = _args[15];
lean_object* v___y_3862_ = _args[16];
lean_object* v___y_3863_ = _args[17];
lean_object* v___y_3864_ = _args[18];
_start:
{
size_t v_sz_boxed_3865_; size_t v_i_boxed_3866_; lean_object* v_res_3867_; 
v_sz_boxed_3865_ = lean_unbox_usize(v_sz_3850_);
lean_dec(v_sz_3850_);
v_i_boxed_3866_ = lean_unbox_usize(v_i_3851_);
lean_dec(v_i_3851_);
v_res_3867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3846_, v_x_3847_, v_c_3848_, v_as_3849_, v_sz_boxed_3865_, v_i_boxed_3866_, v_b_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec_ref(v_as_3849_);
lean_dec(v_x_3847_);
lean_dec(v_a_3846_);
return v_res_3867_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object* v_a_3868_, lean_object* v_x_3869_, lean_object* v_c_3870_, lean_object* v_y_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_){
_start:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3884_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_3885_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3944_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3888_ = v___x_3885_;
v_isShared_3889_ = v_isSharedCheck_3944_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3885_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3944_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
uint8_t v___x_3890_; 
v___x_3890_ = lean_unbox(v_a_3886_);
lean_dec(v_a_3886_);
if (v___x_3890_ == 0)
{
lean_object* v___x_3891_; 
lean_del_object(v___x_3888_);
v___x_3891_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; lean_object* v___y_3894_; lean_object* v_diseqs_3927_; lean_object* v_size_3928_; uint8_t v___x_3929_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_a_3892_);
lean_dec_ref_known(v___x_3891_, 1);
v_diseqs_3927_ = lean_ctor_get(v_a_3892_, 34);
lean_inc_ref(v_diseqs_3927_);
lean_dec(v_a_3892_);
v_size_3928_ = lean_ctor_get(v_diseqs_3927_, 2);
v___x_3929_ = lean_nat_dec_lt(v_y_3871_, v_size_3928_);
if (v___x_3929_ == 0)
{
lean_object* v___x_3930_; 
lean_dec_ref(v_diseqs_3927_);
v___x_3930_ = l_outOfBounds___redArg(v___x_3884_);
v___y_3894_ = v___x_3930_;
goto v___jp_3893_;
}
else
{
lean_object* v___x_3931_; 
v___x_3931_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3884_, v_diseqs_3927_, v_y_3871_);
lean_dec_ref(v_diseqs_3927_);
v___y_3894_ = v___x_3931_;
goto v___jp_3893_;
}
v___jp_3893_:
{
lean_object* v___x_3895_; lean_object* v_fst_3896_; lean_object* v_snd_3897_; lean_object* v___f_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3895_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3869_, v___y_3894_);
lean_dec_ref(v___y_3894_);
v_fst_3896_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_fst_3896_);
v_snd_3897_ = lean_ctor_get(v___x_3895_, 1);
lean_inc(v_snd_3897_);
lean_dec_ref(v___x_3895_);
lean_inc(v_a_3872_);
v___f_3898_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3898_, 0, v_a_3872_);
lean_closure_set(v___f_3898_, 1, v_y_3871_);
lean_closure_set(v___f_3898_, 2, v_fst_3896_);
v___x_3899_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3900_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3899_, v___f_3898_, v_a_3873_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v___x_3901_; lean_object* v___x_3902_; size_t v_sz_3903_; size_t v___x_3904_; lean_object* v___x_3905_; 
lean_dec_ref_known(v___x_3900_, 1);
v___x_3901_ = lean_box(0);
v___x_3902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_3903_ = lean_array_size(v_snd_3897_);
v___x_3904_ = ((size_t)0ULL);
v___x_3905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3868_, v_x_3869_, v_c_3870_, v_snd_3897_, v_sz_3903_, v___x_3904_, v___x_3902_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
lean_dec(v_snd_3897_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3918_; 
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3908_ = v___x_3905_;
v_isShared_3909_ = v_isSharedCheck_3918_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3905_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3918_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v_fst_3910_; 
v_fst_3910_ = lean_ctor_get(v_a_3906_, 0);
lean_inc(v_fst_3910_);
lean_dec(v_a_3906_);
if (lean_obj_tag(v_fst_3910_) == 0)
{
lean_object* v___x_3912_; 
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v___x_3901_);
v___x_3912_ = v___x_3908_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3901_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
else
{
lean_object* v_val_3914_; lean_object* v___x_3916_; 
v_val_3914_ = lean_ctor_get(v_fst_3910_, 0);
lean_inc(v_val_3914_);
lean_dec_ref_known(v_fst_3910_, 1);
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v_val_3914_);
v___x_3916_ = v___x_3908_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_val_3914_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
}
else
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3926_; 
v_a_3919_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3921_ = v___x_3905_;
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3905_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3924_; 
if (v_isShared_3922_ == 0)
{
v___x_3924_ = v___x_3921_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
else
{
lean_dec(v_snd_3897_);
lean_dec_ref(v_c_3870_);
return v___x_3900_;
}
}
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
lean_dec(v_y_3871_);
lean_dec_ref(v_c_3870_);
v_a_3932_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3891_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3891_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
else
{
lean_object* v___x_3940_; lean_object* v___x_3942_; 
lean_dec(v_y_3871_);
lean_dec_ref(v_c_3870_);
v___x_3940_ = lean_box(0);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3940_);
v___x_3942_ = v___x_3888_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3940_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
lean_dec(v_y_3871_);
lean_dec_ref(v_c_3870_);
v_a_3945_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3947_ = v___x_3885_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3885_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3868_ = stack[0].m_obj;
lean_object* v_x_3869_ = stack[1].m_obj;
lean_object* v_c_3870_ = stack[2].m_obj;
lean_object* v_y_3871_ = stack[3].m_obj;
lean_object* v_a_3872_ = stack[4].m_obj;
lean_object* v_a_3873_ = stack[5].m_obj;
lean_object* v_a_3874_ = stack[6].m_obj;
lean_object* v_a_3875_ = stack[7].m_obj;
lean_object* v_a_3876_ = stack[8].m_obj;
lean_object* v_a_3877_ = stack[9].m_obj;
lean_object* v_a_3878_ = stack[10].m_obj;
lean_object* v_a_3879_ = stack[11].m_obj;
lean_object* v_a_3880_ = stack[12].m_obj;
lean_object* v_a_3881_ = stack[13].m_obj;
lean_object* v_a_3882_ = stack[14].m_obj;
lean_object* v_res_3953_;
v_res_3953_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v_a_3868_, v_x_3869_, v_c_3870_, v_y_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
stack->m_obj
 = v_res_3953_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object* v_a_3954_, lean_object* v_x_3955_, lean_object* v_c_3956_, lean_object* v_y_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v_a_3954_, v_x_3955_, v_c_3956_, v_y_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
lean_dec(v_a_3968_);
lean_dec_ref(v_a_3967_);
lean_dec(v_a_3966_);
lean_dec_ref(v_a_3965_);
lean_dec(v_a_3964_);
lean_dec_ref(v_a_3963_);
lean_dec(v_a_3962_);
lean_dec_ref(v_a_3961_);
lean_dec(v_a_3960_);
lean_dec(v_a_3959_);
lean_dec(v_a_3958_);
lean_dec(v_x_3955_);
lean_dec(v_a_3954_);
return v_res_3970_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object* v_a_3971_, lean_object* v_x_3972_, lean_object* v_c_3973_, lean_object* v_y_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_){
_start:
{
lean_object* v___x_3987_; 
lean_inc(v_y_3974_);
lean_inc_ref(v_c_3973_);
lean_inc(v_x_3972_);
lean_inc(v_a_3971_);
v___x_3987_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_3971_, v_x_3972_, v_c_3973_, v_y_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v___x_3988_; 
lean_dec_ref_known(v___x_3987_, 1);
lean_inc(v_y_3974_);
lean_inc_ref(v_c_3973_);
lean_inc(v_x_3972_);
lean_inc(v_a_3971_);
v___x_3988_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_3971_, v_x_3972_, v_c_3973_, v_y_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v___x_3989_; lean_object* v___x_3990_; 
lean_dec_ref_known(v___x_3988_, 1);
v___x_3989_ = lean_nat_to_int(v_a_3971_);
v___x_3990_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v___x_3989_, v_x_3972_, v_c_3973_, v_y_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
lean_dec(v_x_3972_);
lean_dec(v___x_3989_);
return v___x_3990_;
}
else
{
lean_dec(v_y_3974_);
lean_dec_ref(v_c_3973_);
lean_dec(v_x_3972_);
lean_dec(v_a_3971_);
return v___x_3988_;
}
}
else
{
lean_dec(v_y_3974_);
lean_dec_ref(v_c_3973_);
lean_dec(v_x_3972_);
lean_dec(v_a_3971_);
return v___x_3987_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3971_ = stack[0].m_obj;
lean_object* v_x_3972_ = stack[1].m_obj;
lean_object* v_c_3973_ = stack[2].m_obj;
lean_object* v_y_3974_ = stack[3].m_obj;
lean_object* v_a_3975_ = stack[4].m_obj;
lean_object* v_a_3976_ = stack[5].m_obj;
lean_object* v_a_3977_ = stack[6].m_obj;
lean_object* v_a_3978_ = stack[7].m_obj;
lean_object* v_a_3979_ = stack[8].m_obj;
lean_object* v_a_3980_ = stack[9].m_obj;
lean_object* v_a_3981_ = stack[10].m_obj;
lean_object* v_a_3982_ = stack[11].m_obj;
lean_object* v_a_3983_ = stack[12].m_obj;
lean_object* v_a_3984_ = stack[13].m_obj;
lean_object* v_a_3985_ = stack[14].m_obj;
lean_object* v_res_3991_;
v_res_3991_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_3971_, v_x_3972_, v_c_3973_, v_y_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
stack->m_obj
 = v_res_3991_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object* v_a_3992_, lean_object* v_x_3993_, lean_object* v_c_3994_, lean_object* v_y_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_3992_, v_x_3993_, v_c_3994_, v_y_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_);
lean_dec(v_a_4006_);
lean_dec_ref(v_a_4005_);
lean_dec(v_a_4004_);
lean_dec_ref(v_a_4003_);
lean_dec(v_a_4002_);
lean_dec_ref(v_a_4001_);
lean_dec(v_a_4000_);
lean_dec_ref(v_a_3999_);
lean_dec(v_a_3998_);
lean_dec(v_a_3997_);
lean_dec(v_a_3996_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(lean_object* v_a_4009_, lean_object* v_x_4010_, lean_object* v_s_4011_){
_start:
{
lean_object* v_structs_4012_; lean_object* v_typeIdOf_4013_; lean_object* v_exprToStructId_4014_; lean_object* v_exprToStructIdEntries_4015_; lean_object* v_forbiddenNatModules_4016_; lean_object* v_natStructs_4017_; lean_object* v_natTypeIdOf_4018_; lean_object* v_exprToNatStructId_4019_; lean_object* v___x_4020_; uint8_t v___x_4021_; 
v_structs_4012_ = lean_ctor_get(v_s_4011_, 0);
v_typeIdOf_4013_ = lean_ctor_get(v_s_4011_, 1);
v_exprToStructId_4014_ = lean_ctor_get(v_s_4011_, 2);
v_exprToStructIdEntries_4015_ = lean_ctor_get(v_s_4011_, 3);
v_forbiddenNatModules_4016_ = lean_ctor_get(v_s_4011_, 4);
v_natStructs_4017_ = lean_ctor_get(v_s_4011_, 5);
v_natTypeIdOf_4018_ = lean_ctor_get(v_s_4011_, 6);
v_exprToNatStructId_4019_ = lean_ctor_get(v_s_4011_, 7);
v___x_4020_ = lean_array_get_size(v_structs_4012_);
v___x_4021_ = lean_nat_dec_lt(v_a_4009_, v___x_4020_);
if (v___x_4021_ == 0)
{
return v_s_4011_;
}
else
{
lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4084_; 
lean_inc_ref(v_exprToNatStructId_4019_);
lean_inc_ref(v_natTypeIdOf_4018_);
lean_inc_ref(v_natStructs_4017_);
lean_inc_ref(v_forbiddenNatModules_4016_);
lean_inc_ref(v_exprToStructIdEntries_4015_);
lean_inc_ref(v_exprToStructId_4014_);
lean_inc_ref(v_typeIdOf_4013_);
lean_inc_ref(v_structs_4012_);
v_isSharedCheck_4084_ = !lean_is_exclusive(v_s_4011_);
if (v_isSharedCheck_4084_ == 0)
{
lean_object* v_unused_4085_; lean_object* v_unused_4086_; lean_object* v_unused_4087_; lean_object* v_unused_4088_; lean_object* v_unused_4089_; lean_object* v_unused_4090_; lean_object* v_unused_4091_; lean_object* v_unused_4092_; 
v_unused_4085_ = lean_ctor_get(v_s_4011_, 7);
lean_dec(v_unused_4085_);
v_unused_4086_ = lean_ctor_get(v_s_4011_, 6);
lean_dec(v_unused_4086_);
v_unused_4087_ = lean_ctor_get(v_s_4011_, 5);
lean_dec(v_unused_4087_);
v_unused_4088_ = lean_ctor_get(v_s_4011_, 4);
lean_dec(v_unused_4088_);
v_unused_4089_ = lean_ctor_get(v_s_4011_, 3);
lean_dec(v_unused_4089_);
v_unused_4090_ = lean_ctor_get(v_s_4011_, 2);
lean_dec(v_unused_4090_);
v_unused_4091_ = lean_ctor_get(v_s_4011_, 1);
lean_dec(v_unused_4091_);
v_unused_4092_ = lean_ctor_get(v_s_4011_, 0);
lean_dec(v_unused_4092_);
v___x_4023_ = v_s_4011_;
v_isShared_4024_ = v_isSharedCheck_4084_;
goto v_resetjp_4022_;
}
else
{
lean_dec(v_s_4011_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4084_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v_v_4025_; lean_object* v_id_4026_; lean_object* v_ringId_x3f_4027_; lean_object* v_type_4028_; lean_object* v_u_4029_; lean_object* v_intModuleInst_4030_; lean_object* v_leInst_x3f_4031_; lean_object* v_ltInst_x3f_4032_; lean_object* v_lawfulOrderLTInst_x3f_4033_; lean_object* v_isPreorderInst_x3f_4034_; lean_object* v_orderedAddInst_x3f_4035_; lean_object* v_isLinearInst_x3f_4036_; lean_object* v_noNatDivInst_x3f_4037_; lean_object* v_ringInst_x3f_4038_; lean_object* v_commRingInst_x3f_4039_; lean_object* v_orderedRingInst_x3f_4040_; lean_object* v_fieldInst_x3f_4041_; lean_object* v_charInst_x3f_4042_; lean_object* v_zero_4043_; lean_object* v_ofNatZero_4044_; lean_object* v_one_x3f_4045_; lean_object* v_leFn_x3f_4046_; lean_object* v_ltFn_x3f_4047_; lean_object* v_addFn_4048_; lean_object* v_zsmulFn_4049_; lean_object* v_nsmulFn_4050_; lean_object* v_zsmulFn_x3f_4051_; lean_object* v_nsmulFn_x3f_4052_; lean_object* v_homomulFn_x3f_4053_; lean_object* v_subFn_4054_; lean_object* v_negFn_4055_; lean_object* v_vars_4056_; lean_object* v_varMap_4057_; lean_object* v_lowers_4058_; lean_object* v_uppers_4059_; lean_object* v_diseqs_4060_; lean_object* v_assignment_4061_; uint8_t v_caseSplits_4062_; lean_object* v_conflict_x3f_4063_; lean_object* v_diseqSplits_4064_; lean_object* v_elimEqs_4065_; lean_object* v_elimStack_4066_; lean_object* v_occurs_4067_; lean_object* v_ignored_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4083_; 
v_v_4025_ = lean_array_fget(v_structs_4012_, v_a_4009_);
v_id_4026_ = lean_ctor_get(v_v_4025_, 0);
v_ringId_x3f_4027_ = lean_ctor_get(v_v_4025_, 1);
v_type_4028_ = lean_ctor_get(v_v_4025_, 2);
v_u_4029_ = lean_ctor_get(v_v_4025_, 3);
v_intModuleInst_4030_ = lean_ctor_get(v_v_4025_, 4);
v_leInst_x3f_4031_ = lean_ctor_get(v_v_4025_, 5);
v_ltInst_x3f_4032_ = lean_ctor_get(v_v_4025_, 6);
v_lawfulOrderLTInst_x3f_4033_ = lean_ctor_get(v_v_4025_, 7);
v_isPreorderInst_x3f_4034_ = lean_ctor_get(v_v_4025_, 8);
v_orderedAddInst_x3f_4035_ = lean_ctor_get(v_v_4025_, 9);
v_isLinearInst_x3f_4036_ = lean_ctor_get(v_v_4025_, 10);
v_noNatDivInst_x3f_4037_ = lean_ctor_get(v_v_4025_, 11);
v_ringInst_x3f_4038_ = lean_ctor_get(v_v_4025_, 12);
v_commRingInst_x3f_4039_ = lean_ctor_get(v_v_4025_, 13);
v_orderedRingInst_x3f_4040_ = lean_ctor_get(v_v_4025_, 14);
v_fieldInst_x3f_4041_ = lean_ctor_get(v_v_4025_, 15);
v_charInst_x3f_4042_ = lean_ctor_get(v_v_4025_, 16);
v_zero_4043_ = lean_ctor_get(v_v_4025_, 17);
v_ofNatZero_4044_ = lean_ctor_get(v_v_4025_, 18);
v_one_x3f_4045_ = lean_ctor_get(v_v_4025_, 19);
v_leFn_x3f_4046_ = lean_ctor_get(v_v_4025_, 20);
v_ltFn_x3f_4047_ = lean_ctor_get(v_v_4025_, 21);
v_addFn_4048_ = lean_ctor_get(v_v_4025_, 22);
v_zsmulFn_4049_ = lean_ctor_get(v_v_4025_, 23);
v_nsmulFn_4050_ = lean_ctor_get(v_v_4025_, 24);
v_zsmulFn_x3f_4051_ = lean_ctor_get(v_v_4025_, 25);
v_nsmulFn_x3f_4052_ = lean_ctor_get(v_v_4025_, 26);
v_homomulFn_x3f_4053_ = lean_ctor_get(v_v_4025_, 27);
v_subFn_4054_ = lean_ctor_get(v_v_4025_, 28);
v_negFn_4055_ = lean_ctor_get(v_v_4025_, 29);
v_vars_4056_ = lean_ctor_get(v_v_4025_, 30);
v_varMap_4057_ = lean_ctor_get(v_v_4025_, 31);
v_lowers_4058_ = lean_ctor_get(v_v_4025_, 32);
v_uppers_4059_ = lean_ctor_get(v_v_4025_, 33);
v_diseqs_4060_ = lean_ctor_get(v_v_4025_, 34);
v_assignment_4061_ = lean_ctor_get(v_v_4025_, 35);
v_caseSplits_4062_ = lean_ctor_get_uint8(v_v_4025_, sizeof(void*)*42);
v_conflict_x3f_4063_ = lean_ctor_get(v_v_4025_, 36);
v_diseqSplits_4064_ = lean_ctor_get(v_v_4025_, 37);
v_elimEqs_4065_ = lean_ctor_get(v_v_4025_, 38);
v_elimStack_4066_ = lean_ctor_get(v_v_4025_, 39);
v_occurs_4067_ = lean_ctor_get(v_v_4025_, 40);
v_ignored_4068_ = lean_ctor_get(v_v_4025_, 41);
v_isSharedCheck_4083_ = !lean_is_exclusive(v_v_4025_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4070_ = v_v_4025_;
v_isShared_4071_ = v_isSharedCheck_4083_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_ignored_4068_);
lean_inc(v_occurs_4067_);
lean_inc(v_elimStack_4066_);
lean_inc(v_elimEqs_4065_);
lean_inc(v_diseqSplits_4064_);
lean_inc(v_conflict_x3f_4063_);
lean_inc(v_assignment_4061_);
lean_inc(v_diseqs_4060_);
lean_inc(v_uppers_4059_);
lean_inc(v_lowers_4058_);
lean_inc(v_varMap_4057_);
lean_inc(v_vars_4056_);
lean_inc(v_negFn_4055_);
lean_inc(v_subFn_4054_);
lean_inc(v_homomulFn_x3f_4053_);
lean_inc(v_nsmulFn_x3f_4052_);
lean_inc(v_zsmulFn_x3f_4051_);
lean_inc(v_nsmulFn_4050_);
lean_inc(v_zsmulFn_4049_);
lean_inc(v_addFn_4048_);
lean_inc(v_ltFn_x3f_4047_);
lean_inc(v_leFn_x3f_4046_);
lean_inc(v_one_x3f_4045_);
lean_inc(v_ofNatZero_4044_);
lean_inc(v_zero_4043_);
lean_inc(v_charInst_x3f_4042_);
lean_inc(v_fieldInst_x3f_4041_);
lean_inc(v_orderedRingInst_x3f_4040_);
lean_inc(v_commRingInst_x3f_4039_);
lean_inc(v_ringInst_x3f_4038_);
lean_inc(v_noNatDivInst_x3f_4037_);
lean_inc(v_isLinearInst_x3f_4036_);
lean_inc(v_orderedAddInst_x3f_4035_);
lean_inc(v_isPreorderInst_x3f_4034_);
lean_inc(v_lawfulOrderLTInst_x3f_4033_);
lean_inc(v_ltInst_x3f_4032_);
lean_inc(v_leInst_x3f_4031_);
lean_inc(v_intModuleInst_4030_);
lean_inc(v_u_4029_);
lean_inc(v_type_4028_);
lean_inc(v_ringId_x3f_4027_);
lean_inc(v_id_4026_);
lean_dec(v_v_4025_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4083_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4072_; lean_object* v_xs_x27_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4077_; 
v___x_4072_ = lean_box(0);
v_xs_x27_4073_ = lean_array_fset(v_structs_4012_, v_a_4009_, v___x_4072_);
v___x_4074_ = lean_box(1);
v___x_4075_ = l_Lean_PersistentArray_set___redArg(v_occurs_4067_, v_x_4010_, v___x_4074_);
if (v_isShared_4071_ == 0)
{
lean_ctor_set(v___x_4070_, 40, v___x_4075_);
v___x_4077_ = v___x_4070_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_id_4026_);
lean_ctor_set(v_reuseFailAlloc_4082_, 1, v_ringId_x3f_4027_);
lean_ctor_set(v_reuseFailAlloc_4082_, 2, v_type_4028_);
lean_ctor_set(v_reuseFailAlloc_4082_, 3, v_u_4029_);
lean_ctor_set(v_reuseFailAlloc_4082_, 4, v_intModuleInst_4030_);
lean_ctor_set(v_reuseFailAlloc_4082_, 5, v_leInst_x3f_4031_);
lean_ctor_set(v_reuseFailAlloc_4082_, 6, v_ltInst_x3f_4032_);
lean_ctor_set(v_reuseFailAlloc_4082_, 7, v_lawfulOrderLTInst_x3f_4033_);
lean_ctor_set(v_reuseFailAlloc_4082_, 8, v_isPreorderInst_x3f_4034_);
lean_ctor_set(v_reuseFailAlloc_4082_, 9, v_orderedAddInst_x3f_4035_);
lean_ctor_set(v_reuseFailAlloc_4082_, 10, v_isLinearInst_x3f_4036_);
lean_ctor_set(v_reuseFailAlloc_4082_, 11, v_noNatDivInst_x3f_4037_);
lean_ctor_set(v_reuseFailAlloc_4082_, 12, v_ringInst_x3f_4038_);
lean_ctor_set(v_reuseFailAlloc_4082_, 13, v_commRingInst_x3f_4039_);
lean_ctor_set(v_reuseFailAlloc_4082_, 14, v_orderedRingInst_x3f_4040_);
lean_ctor_set(v_reuseFailAlloc_4082_, 15, v_fieldInst_x3f_4041_);
lean_ctor_set(v_reuseFailAlloc_4082_, 16, v_charInst_x3f_4042_);
lean_ctor_set(v_reuseFailAlloc_4082_, 17, v_zero_4043_);
lean_ctor_set(v_reuseFailAlloc_4082_, 18, v_ofNatZero_4044_);
lean_ctor_set(v_reuseFailAlloc_4082_, 19, v_one_x3f_4045_);
lean_ctor_set(v_reuseFailAlloc_4082_, 20, v_leFn_x3f_4046_);
lean_ctor_set(v_reuseFailAlloc_4082_, 21, v_ltFn_x3f_4047_);
lean_ctor_set(v_reuseFailAlloc_4082_, 22, v_addFn_4048_);
lean_ctor_set(v_reuseFailAlloc_4082_, 23, v_zsmulFn_4049_);
lean_ctor_set(v_reuseFailAlloc_4082_, 24, v_nsmulFn_4050_);
lean_ctor_set(v_reuseFailAlloc_4082_, 25, v_zsmulFn_x3f_4051_);
lean_ctor_set(v_reuseFailAlloc_4082_, 26, v_nsmulFn_x3f_4052_);
lean_ctor_set(v_reuseFailAlloc_4082_, 27, v_homomulFn_x3f_4053_);
lean_ctor_set(v_reuseFailAlloc_4082_, 28, v_subFn_4054_);
lean_ctor_set(v_reuseFailAlloc_4082_, 29, v_negFn_4055_);
lean_ctor_set(v_reuseFailAlloc_4082_, 30, v_vars_4056_);
lean_ctor_set(v_reuseFailAlloc_4082_, 31, v_varMap_4057_);
lean_ctor_set(v_reuseFailAlloc_4082_, 32, v_lowers_4058_);
lean_ctor_set(v_reuseFailAlloc_4082_, 33, v_uppers_4059_);
lean_ctor_set(v_reuseFailAlloc_4082_, 34, v_diseqs_4060_);
lean_ctor_set(v_reuseFailAlloc_4082_, 35, v_assignment_4061_);
lean_ctor_set(v_reuseFailAlloc_4082_, 36, v_conflict_x3f_4063_);
lean_ctor_set(v_reuseFailAlloc_4082_, 37, v_diseqSplits_4064_);
lean_ctor_set(v_reuseFailAlloc_4082_, 38, v_elimEqs_4065_);
lean_ctor_set(v_reuseFailAlloc_4082_, 39, v_elimStack_4066_);
lean_ctor_set(v_reuseFailAlloc_4082_, 40, v___x_4075_);
lean_ctor_set(v_reuseFailAlloc_4082_, 41, v_ignored_4068_);
lean_ctor_set_uint8(v_reuseFailAlloc_4082_, sizeof(void*)*42, v_caseSplits_4062_);
v___x_4077_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
lean_object* v___x_4078_; lean_object* v___x_4080_; 
v___x_4078_ = lean_array_fset(v_xs_x27_4073_, v_a_4009_, v___x_4077_);
if (v_isShared_4024_ == 0)
{
lean_ctor_set(v___x_4023_, 0, v___x_4078_);
v___x_4080_ = v___x_4023_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v___x_4078_);
lean_ctor_set(v_reuseFailAlloc_4081_, 1, v_typeIdOf_4013_);
lean_ctor_set(v_reuseFailAlloc_4081_, 2, v_exprToStructId_4014_);
lean_ctor_set(v_reuseFailAlloc_4081_, 3, v_exprToStructIdEntries_4015_);
lean_ctor_set(v_reuseFailAlloc_4081_, 4, v_forbiddenNatModules_4016_);
lean_ctor_set(v_reuseFailAlloc_4081_, 5, v_natStructs_4017_);
lean_ctor_set(v_reuseFailAlloc_4081_, 6, v_natTypeIdOf_4018_);
lean_ctor_set(v_reuseFailAlloc_4081_, 7, v_exprToNatStructId_4019_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed(lean_object* v_a_4093_, lean_object* v_x_4094_, lean_object* v_s_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(v_a_4093_, v_x_4094_, v_s_4095_);
lean_dec(v_x_4094_);
lean_dec(v_a_4093_);
return v_res_4096_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object* v_a_4097_, lean_object* v_x_4098_, lean_object* v_c_4099_, lean_object* v_init_4100_, lean_object* v_x_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
if (lean_obj_tag(v_x_4101_) == 0)
{
lean_object* v_k_4114_; lean_object* v_l_4115_; lean_object* v_r_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v_k_4114_ = lean_ctor_get(v_x_4101_, 1);
lean_inc(v_k_4114_);
v_l_4115_ = lean_ctor_get(v_x_4101_, 3);
lean_inc(v_l_4115_);
v_r_4116_ = lean_ctor_get(v_x_4101_, 4);
lean_inc(v_r_4116_);
lean_dec_ref_known(v_x_4101_, 5);
v___x_4117_ = lean_box(0);
lean_inc_ref(v_c_4099_);
lean_inc(v_x_4098_);
lean_inc(v_a_4097_);
v___x_4118_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4097_, v_x_4098_, v_c_4099_, v_init_4100_, v_l_4115_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v___x_4119_; 
lean_dec_ref_known(v___x_4118_, 1);
lean_inc_ref(v_c_4099_);
lean_inc(v_x_4098_);
lean_inc(v_a_4097_);
v___x_4119_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4097_, v_x_4098_, v_c_4099_, v_k_4114_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_dec_ref_known(v___x_4119_, 1);
v_init_4100_ = v___x_4117_;
v_x_4101_ = v_r_4116_;
goto _start;
}
else
{
lean_object* v_a_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4128_; 
lean_dec(v_r_4116_);
lean_dec_ref(v_c_4099_);
lean_dec(v_x_4098_);
lean_dec(v_a_4097_);
v_a_4121_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4128_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4128_ == 0)
{
v___x_4123_ = v___x_4119_;
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_a_4121_);
lean_dec(v___x_4119_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4126_; 
if (v_isShared_4124_ == 0)
{
v___x_4126_ = v___x_4123_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_a_4121_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
return v___x_4126_;
}
}
}
}
else
{
lean_dec(v_r_4116_);
lean_dec(v_k_4114_);
lean_dec_ref(v_c_4099_);
lean_dec(v_x_4098_);
lean_dec(v_a_4097_);
return v___x_4118_;
}
}
else
{
lean_object* v___x_4129_; lean_object* v___x_4130_; 
lean_dec_ref(v_c_4099_);
lean_dec(v_x_4098_);
lean_dec(v_a_4097_);
v___x_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4129_, 0, v_init_4100_);
v___x_4130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4129_);
return v___x_4130_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4097_ = stack[0].m_obj;
lean_object* v_x_4098_ = stack[1].m_obj;
lean_object* v_c_4099_ = stack[2].m_obj;
lean_object* v_init_4100_ = stack[3].m_obj;
lean_object* v_x_4101_ = stack[4].m_obj;
lean_object* v___y_4102_ = stack[5].m_obj;
lean_object* v___y_4103_ = stack[6].m_obj;
lean_object* v___y_4104_ = stack[7].m_obj;
lean_object* v___y_4105_ = stack[8].m_obj;
lean_object* v___y_4106_ = stack[9].m_obj;
lean_object* v___y_4107_ = stack[10].m_obj;
lean_object* v___y_4108_ = stack[11].m_obj;
lean_object* v___y_4109_ = stack[12].m_obj;
lean_object* v___y_4110_ = stack[13].m_obj;
lean_object* v___y_4111_ = stack[14].m_obj;
lean_object* v___y_4112_ = stack[15].m_obj;
lean_object* v_res_4131_;
v_res_4131_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4097_, v_x_4098_, v_c_4099_, v_init_4100_, v_x_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
stack->m_obj
 = v_res_4131_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object** _args){
lean_object* v_a_4132_ = _args[0];
lean_object* v_x_4133_ = _args[1];
lean_object* v_c_4134_ = _args[2];
lean_object* v_init_4135_ = _args[3];
lean_object* v_x_4136_ = _args[4];
lean_object* v___y_4137_ = _args[5];
lean_object* v___y_4138_ = _args[6];
lean_object* v___y_4139_ = _args[7];
lean_object* v___y_4140_ = _args[8];
lean_object* v___y_4141_ = _args[9];
lean_object* v___y_4142_ = _args[10];
lean_object* v___y_4143_ = _args[11];
lean_object* v___y_4144_ = _args[12];
lean_object* v___y_4145_ = _args[13];
lean_object* v___y_4146_ = _args[14];
lean_object* v___y_4147_ = _args[15];
lean_object* v___y_4148_ = _args[16];
_start:
{
lean_object* v_res_4149_; 
v_res_4149_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4132_, v_x_4133_, v_c_4134_, v_init_4135_, v_x_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec(v___y_4139_);
lean_dec(v___y_4138_);
lean_dec(v___y_4137_);
return v_res_4149_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object* v_a_4150_, lean_object* v_x_4151_, lean_object* v_c_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_){
_start:
{
lean_object* v___f_4165_; lean_object* v___x_4166_; 
lean_inc(v_x_4151_);
lean_inc(v_a_4153_);
v___f_4165_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4165_, 0, v_a_4153_);
lean_closure_set(v___f_4165_, 1, v_x_4151_);
v___x_4166_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v___y_4169_; lean_object* v_occurs_4191_; lean_object* v_size_4192_; lean_object* v___x_4193_; uint8_t v___x_4194_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc(v_a_4167_);
lean_dec_ref_known(v___x_4166_, 1);
v_occurs_4191_ = lean_ctor_get(v_a_4167_, 40);
lean_inc_ref(v_occurs_4191_);
lean_dec(v_a_4167_);
v_size_4192_ = lean_ctor_get(v_occurs_4191_, 2);
v___x_4193_ = lean_box(1);
v___x_4194_ = lean_nat_dec_lt(v_x_4151_, v_size_4192_);
if (v___x_4194_ == 0)
{
lean_object* v___x_4195_; 
lean_dec_ref(v_occurs_4191_);
v___x_4195_ = l_outOfBounds___redArg(v___x_4193_);
v___y_4169_ = v___x_4195_;
goto v___jp_4168_;
}
else
{
lean_object* v___x_4196_; 
v___x_4196_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4193_, v_occurs_4191_, v_x_4151_);
lean_dec_ref(v_occurs_4191_);
v___y_4169_ = v___x_4196_;
goto v___jp_4168_;
}
v___jp_4168_:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4170_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4171_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4170_, v___f_4165_, v_a_4154_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_object* v___x_4172_; 
lean_dec_ref_known(v___x_4171_, 1);
lean_inc_ref(v_c_4152_);
lean_inc_n(v_x_4151_, 2);
lean_inc(v_a_4150_);
v___x_4172_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4150_, v_x_4151_, v_c_4152_, v_x_4151_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
lean_dec_ref_known(v___x_4172_, 1);
v___x_4173_ = lean_box(0);
v___x_4174_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4150_, v_x_4151_, v_c_4152_, v___x_4173_, v___y_4169_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4181_; 
v_isSharedCheck_4181_ = !lean_is_exclusive(v___x_4174_);
if (v_isSharedCheck_4181_ == 0)
{
lean_object* v_unused_4182_; 
v_unused_4182_ = lean_ctor_get(v___x_4174_, 0);
lean_dec(v_unused_4182_);
v___x_4176_ = v___x_4174_;
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
else
{
lean_dec(v___x_4174_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4179_; 
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 0, v___x_4173_);
v___x_4179_ = v___x_4176_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v___x_4173_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
else
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
v_a_4183_ = lean_ctor_get(v___x_4174_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4174_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4185_ = v___x_4174_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4174_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
else
{
lean_dec(v___y_4169_);
lean_dec_ref(v_c_4152_);
lean_dec(v_x_4151_);
lean_dec(v_a_4150_);
return v___x_4172_;
}
}
else
{
lean_dec(v___y_4169_);
lean_dec_ref(v_c_4152_);
lean_dec(v_x_4151_);
lean_dec(v_a_4150_);
return v___x_4171_;
}
}
}
else
{
lean_object* v_a_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4204_; 
lean_dec_ref(v___f_4165_);
lean_dec_ref(v_c_4152_);
lean_dec(v_x_4151_);
lean_dec(v_a_4150_);
v_a_4197_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4199_ = v___x_4166_;
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v___x_4166_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___x_4202_; 
if (v_isShared_4200_ == 0)
{
v___x_4202_ = v___x_4199_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4197_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4150_ = stack[0].m_obj;
lean_object* v_x_4151_ = stack[1].m_obj;
lean_object* v_c_4152_ = stack[2].m_obj;
lean_object* v_a_4153_ = stack[3].m_obj;
lean_object* v_a_4154_ = stack[4].m_obj;
lean_object* v_a_4155_ = stack[5].m_obj;
lean_object* v_a_4156_ = stack[6].m_obj;
lean_object* v_a_4157_ = stack[7].m_obj;
lean_object* v_a_4158_ = stack[8].m_obj;
lean_object* v_a_4159_ = stack[9].m_obj;
lean_object* v_a_4160_ = stack[10].m_obj;
lean_object* v_a_4161_ = stack[11].m_obj;
lean_object* v_a_4162_ = stack[12].m_obj;
lean_object* v_a_4163_ = stack[13].m_obj;
lean_object* v_res_4205_;
v_res_4205_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v_a_4150_, v_x_4151_, v_c_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
stack->m_obj
 = v_res_4205_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___boxed(lean_object* v_a_4206_, lean_object* v_x_4207_, lean_object* v_c_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v_a_4206_, v_x_4207_, v_c_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
lean_dec(v_a_4219_);
lean_dec_ref(v_a_4218_);
lean_dec(v_a_4217_);
lean_dec_ref(v_a_4216_);
lean_dec(v_a_4215_);
lean_dec_ref(v_a_4214_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
lean_dec(v_a_4211_);
lean_dec(v_a_4210_);
lean_dec(v_a_4209_);
return v_res_4221_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(lean_object* v_c_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_){
_start:
{
lean_object* v_p_4239_; 
v_p_4239_ = lean_ctor_get(v_c_4222_, 0);
if (lean_obj_tag(v_p_4239_) == 1)
{
lean_object* v_k_4240_; lean_object* v_v_4241_; lean_object* v_p_4242_; lean_object* v_y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___x_4293_; lean_object* v___x_4294_; uint8_t v___x_4295_; 
v_k_4240_ = lean_ctor_get(v_p_4239_, 0);
v_v_4241_ = lean_ctor_get(v_p_4239_, 1);
v_p_4242_ = lean_ctor_get(v_p_4239_, 2);
v___x_4293_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_4294_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4295_ = lean_int_dec_eq(v_k_4240_, v___x_4294_);
if (v___x_4295_ == 0)
{
uint8_t v___x_4296_; 
v___x_4296_ = lean_int_dec_eq(v_k_4240_, v___x_4293_);
if (v___x_4296_ == 0)
{
goto v___jp_4235_;
}
else
{
if (lean_obj_tag(v_p_4242_) == 1)
{
lean_object* v_k_4297_; lean_object* v_v_4298_; lean_object* v_p_4299_; uint8_t v___x_4300_; 
v_k_4297_ = lean_ctor_get(v_p_4242_, 0);
v_v_4298_ = lean_ctor_get(v_p_4242_, 1);
v_p_4299_ = lean_ctor_get(v_p_4242_, 2);
v___x_4300_ = lean_int_dec_eq(v_k_4297_, v___x_4294_);
if (v___x_4300_ == 0)
{
goto v___jp_4235_;
}
else
{
if (lean_obj_tag(v_p_4299_) == 0)
{
v_y_4244_ = v_v_4298_;
v___y_4245_ = v_a_4223_;
v___y_4246_ = v_a_4224_;
v___y_4247_ = v_a_4225_;
v___y_4248_ = v_a_4226_;
v___y_4249_ = v_a_4227_;
v___y_4250_ = v_a_4228_;
v___y_4251_ = v_a_4229_;
v___y_4252_ = v_a_4230_;
v___y_4253_ = v_a_4231_;
v___y_4254_ = v_a_4232_;
v___y_4255_ = v_a_4233_;
goto v___jp_4243_;
}
else
{
goto v___jp_4235_;
}
}
}
else
{
goto v___jp_4235_;
}
}
}
else
{
if (lean_obj_tag(v_p_4242_) == 1)
{
lean_object* v_k_4301_; lean_object* v_v_4302_; lean_object* v_p_4303_; uint8_t v___x_4304_; 
v_k_4301_ = lean_ctor_get(v_p_4242_, 0);
v_v_4302_ = lean_ctor_get(v_p_4242_, 1);
v_p_4303_ = lean_ctor_get(v_p_4242_, 2);
v___x_4304_ = lean_int_dec_eq(v_k_4301_, v___x_4293_);
if (v___x_4304_ == 0)
{
goto v___jp_4235_;
}
else
{
if (lean_obj_tag(v_p_4303_) == 0)
{
v_y_4244_ = v_v_4302_;
v___y_4245_ = v_a_4223_;
v___y_4246_ = v_a_4224_;
v___y_4247_ = v_a_4225_;
v___y_4248_ = v_a_4226_;
v___y_4249_ = v_a_4227_;
v___y_4250_ = v_a_4228_;
v___y_4251_ = v_a_4229_;
v___y_4252_ = v_a_4230_;
v___y_4253_ = v_a_4231_;
v___y_4254_ = v_a_4232_;
v___y_4255_ = v_a_4233_;
goto v___jp_4243_;
}
else
{
goto v___jp_4235_;
}
}
}
else
{
goto v___jp_4235_;
}
}
v___jp_4243_:
{
lean_object* v___x_4256_; 
v___x_4256_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_v_4241_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
if (lean_obj_tag(v___x_4256_) == 0)
{
lean_object* v_a_4257_; lean_object* v___x_4258_; 
v_a_4257_ = lean_ctor_get(v___x_4256_, 0);
lean_inc(v_a_4257_);
lean_dec_ref_known(v___x_4256_, 1);
v___x_4258_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
if (lean_obj_tag(v___x_4258_) == 0)
{
lean_object* v_a_4259_; lean_object* v___x_4260_; 
v_a_4259_ = lean_ctor_get(v___x_4258_, 0);
lean_inc(v_a_4259_);
lean_dec_ref_known(v___x_4258_, 1);
v___x_4260_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_4257_, v_a_4259_, v___y_4246_);
lean_dec(v_a_4259_);
lean_dec(v_a_4257_);
if (lean_obj_tag(v___x_4260_) == 0)
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4276_; 
v_a_4261_ = lean_ctor_get(v___x_4260_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4263_ = v___x_4260_;
v_isShared_4264_ = v_isSharedCheck_4276_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v___x_4260_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4276_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
uint8_t v___x_4265_; 
v___x_4265_ = lean_unbox(v_a_4261_);
lean_dec(v_a_4261_);
if (v___x_4265_ == 0)
{
uint8_t v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4269_; 
v___x_4266_ = 1;
v___x_4267_ = lean_box(v___x_4266_);
if (v_isShared_4264_ == 0)
{
lean_ctor_set(v___x_4263_, 0, v___x_4267_);
v___x_4269_ = v___x_4263_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v___x_4267_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
else
{
uint8_t v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4274_; 
v___x_4271_ = 0;
v___x_4272_ = lean_box(v___x_4271_);
if (v_isShared_4264_ == 0)
{
lean_ctor_set(v___x_4263_, 0, v___x_4272_);
v___x_4274_ = v___x_4263_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v___x_4272_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
}
else
{
return v___x_4260_;
}
}
else
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
lean_dec(v_a_4257_);
v_a_4277_ = lean_ctor_get(v___x_4258_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4258_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4279_ = v___x_4258_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___x_4258_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4282_; 
if (v_isShared_4280_ == 0)
{
v___x_4282_ = v___x_4279_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_a_4277_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
}
else
{
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4292_; 
v_a_4285_ = lean_ctor_get(v___x_4256_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4256_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4287_ = v___x_4256_;
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4256_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4290_; 
if (v_isShared_4288_ == 0)
{
v___x_4290_ = v___x_4287_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_a_4285_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
}
}
else
{
goto v___jp_4235_;
}
v___jp_4235_:
{
uint8_t v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4236_ = 0;
v___x_4237_ = lean_box(v___x_4236_);
v___x_4238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4237_);
return v___x_4238_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_4222_ = stack[0].m_obj;
lean_object* v_a_4223_ = stack[1].m_obj;
lean_object* v_a_4224_ = stack[2].m_obj;
lean_object* v_a_4225_ = stack[3].m_obj;
lean_object* v_a_4226_ = stack[4].m_obj;
lean_object* v_a_4227_ = stack[5].m_obj;
lean_object* v_a_4228_ = stack[6].m_obj;
lean_object* v_a_4229_ = stack[7].m_obj;
lean_object* v_a_4230_ = stack[8].m_obj;
lean_object* v_a_4231_ = stack[9].m_obj;
lean_object* v_a_4232_ = stack[10].m_obj;
lean_object* v_a_4233_ = stack[11].m_obj;
lean_object* v_res_4305_;
v_res_4305_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v_c_4222_, v_a_4223_, v_a_4224_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_);
stack->m_obj
 = v_res_4305_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq___boxed(lean_object* v_c_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_){
_start:
{
lean_object* v_res_4319_; 
v_res_4319_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v_c_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_);
lean_dec(v_a_4317_);
lean_dec_ref(v_a_4316_);
lean_dec(v_a_4315_);
lean_dec_ref(v_a_4314_);
lean_dec(v_a_4313_);
lean_dec_ref(v_a_4312_);
lean_dec(v_a_4311_);
lean_dec_ref(v_a_4310_);
lean_dec(v_a_4309_);
lean_dec(v_a_4308_);
lean_dec(v_a_4307_);
lean_dec_ref(v_c_4306_);
return v_res_4319_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(lean_object* v_c_4320_){
_start:
{
lean_object* v_p_4322_; 
v_p_4322_ = lean_ctor_get(v_c_4320_, 0);
if (lean_obj_tag(v_p_4322_) == 1)
{
lean_object* v_k_4323_; lean_object* v___x_4324_; uint8_t v___x_4325_; 
v_k_4323_ = lean_ctor_get(v_p_4322_, 0);
v___x_4324_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_4325_ = lean_int_dec_lt(v_k_4323_, v___x_4324_);
if (v___x_4325_ == 0)
{
lean_object* v___x_4326_; 
v___x_4326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4326_, 0, v_c_4320_);
return v___x_4326_;
}
else
{
lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4327_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_4322_);
v___x_4328_ = l_Lean_Grind_Linarith_Poly_mul(v_p_4322_, v___x_4327_);
v___x_4329_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4329_, 0, v_c_4320_);
v___x_4330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4328_);
lean_ctor_set(v___x_4330_, 1, v___x_4329_);
v___x_4331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4330_);
return v___x_4331_;
}
}
else
{
lean_object* v___x_4332_; 
v___x_4332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4332_, 0, v_c_4320_);
return v___x_4332_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_4320_ = stack[0].m_obj;
lean_object* v_res_4333_;
v_res_4333_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4320_);
stack->m_obj
 = v_res_4333_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg___boxed(lean_object* v_c_4334_, lean_object* v_a_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4334_);
return v_res_4336_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(lean_object* v_c_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_){
_start:
{
lean_object* v___x_4350_; 
v___x_4350_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4337_);
return v___x_4350_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_4337_ = stack[0].m_obj;
lean_object* v_a_4338_ = stack[1].m_obj;
lean_object* v_a_4339_ = stack[2].m_obj;
lean_object* v_a_4340_ = stack[3].m_obj;
lean_object* v_a_4341_ = stack[4].m_obj;
lean_object* v_a_4342_ = stack[5].m_obj;
lean_object* v_a_4343_ = stack[6].m_obj;
lean_object* v_a_4344_ = stack[7].m_obj;
lean_object* v_a_4345_ = stack[8].m_obj;
lean_object* v_a_4346_ = stack[9].m_obj;
lean_object* v_a_4347_ = stack[10].m_obj;
lean_object* v_a_4348_ = stack[11].m_obj;
lean_object* v_res_4351_;
v_res_4351_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(v_c_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_);
stack->m_obj
 = v_res_4351_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___boxed(lean_object* v_c_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(v_c_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_);
lean_dec(v_a_4363_);
lean_dec_ref(v_a_4362_);
lean_dec(v_a_4361_);
lean_dec_ref(v_a_4360_);
lean_dec(v_a_4359_);
lean_dec_ref(v_a_4358_);
lean_dec(v_a_4357_);
lean_dec_ref(v_a_4356_);
lean_dec(v_a_4355_);
lean_dec(v_a_4354_);
lean_dec(v_a_4353_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(lean_object* v___y_4366_, lean_object* v_snd_4367_, lean_object* v_fst_4368_, lean_object* v_s_4369_){
_start:
{
lean_object* v_structs_4370_; lean_object* v_typeIdOf_4371_; lean_object* v_exprToStructId_4372_; lean_object* v_exprToStructIdEntries_4373_; lean_object* v_forbiddenNatModules_4374_; lean_object* v_natStructs_4375_; lean_object* v_natTypeIdOf_4376_; lean_object* v_exprToNatStructId_4377_; lean_object* v___x_4378_; uint8_t v___x_4379_; 
v_structs_4370_ = lean_ctor_get(v_s_4369_, 0);
v_typeIdOf_4371_ = lean_ctor_get(v_s_4369_, 1);
v_exprToStructId_4372_ = lean_ctor_get(v_s_4369_, 2);
v_exprToStructIdEntries_4373_ = lean_ctor_get(v_s_4369_, 3);
v_forbiddenNatModules_4374_ = lean_ctor_get(v_s_4369_, 4);
v_natStructs_4375_ = lean_ctor_get(v_s_4369_, 5);
v_natTypeIdOf_4376_ = lean_ctor_get(v_s_4369_, 6);
v_exprToNatStructId_4377_ = lean_ctor_get(v_s_4369_, 7);
v___x_4378_ = lean_array_get_size(v_structs_4370_);
v___x_4379_ = lean_nat_dec_lt(v___y_4366_, v___x_4378_);
if (v___x_4379_ == 0)
{
lean_dec(v_fst_4368_);
lean_dec_ref(v_snd_4367_);
return v_s_4369_;
}
else
{
lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4443_; 
lean_inc_ref(v_exprToNatStructId_4377_);
lean_inc_ref(v_natTypeIdOf_4376_);
lean_inc_ref(v_natStructs_4375_);
lean_inc_ref(v_forbiddenNatModules_4374_);
lean_inc_ref(v_exprToStructIdEntries_4373_);
lean_inc_ref(v_exprToStructId_4372_);
lean_inc_ref(v_typeIdOf_4371_);
lean_inc_ref(v_structs_4370_);
v_isSharedCheck_4443_ = !lean_is_exclusive(v_s_4369_);
if (v_isSharedCheck_4443_ == 0)
{
lean_object* v_unused_4444_; lean_object* v_unused_4445_; lean_object* v_unused_4446_; lean_object* v_unused_4447_; lean_object* v_unused_4448_; lean_object* v_unused_4449_; lean_object* v_unused_4450_; lean_object* v_unused_4451_; 
v_unused_4444_ = lean_ctor_get(v_s_4369_, 7);
lean_dec(v_unused_4444_);
v_unused_4445_ = lean_ctor_get(v_s_4369_, 6);
lean_dec(v_unused_4445_);
v_unused_4446_ = lean_ctor_get(v_s_4369_, 5);
lean_dec(v_unused_4446_);
v_unused_4447_ = lean_ctor_get(v_s_4369_, 4);
lean_dec(v_unused_4447_);
v_unused_4448_ = lean_ctor_get(v_s_4369_, 3);
lean_dec(v_unused_4448_);
v_unused_4449_ = lean_ctor_get(v_s_4369_, 2);
lean_dec(v_unused_4449_);
v_unused_4450_ = lean_ctor_get(v_s_4369_, 1);
lean_dec(v_unused_4450_);
v_unused_4451_ = lean_ctor_get(v_s_4369_, 0);
lean_dec(v_unused_4451_);
v___x_4381_ = v_s_4369_;
v_isShared_4382_ = v_isSharedCheck_4443_;
goto v_resetjp_4380_;
}
else
{
lean_dec(v_s_4369_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4443_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v_v_4383_; lean_object* v_id_4384_; lean_object* v_ringId_x3f_4385_; lean_object* v_type_4386_; lean_object* v_u_4387_; lean_object* v_intModuleInst_4388_; lean_object* v_leInst_x3f_4389_; lean_object* v_ltInst_x3f_4390_; lean_object* v_lawfulOrderLTInst_x3f_4391_; lean_object* v_isPreorderInst_x3f_4392_; lean_object* v_orderedAddInst_x3f_4393_; lean_object* v_isLinearInst_x3f_4394_; lean_object* v_noNatDivInst_x3f_4395_; lean_object* v_ringInst_x3f_4396_; lean_object* v_commRingInst_x3f_4397_; lean_object* v_orderedRingInst_x3f_4398_; lean_object* v_fieldInst_x3f_4399_; lean_object* v_charInst_x3f_4400_; lean_object* v_zero_4401_; lean_object* v_ofNatZero_4402_; lean_object* v_one_x3f_4403_; lean_object* v_leFn_x3f_4404_; lean_object* v_ltFn_x3f_4405_; lean_object* v_addFn_4406_; lean_object* v_zsmulFn_4407_; lean_object* v_nsmulFn_4408_; lean_object* v_zsmulFn_x3f_4409_; lean_object* v_nsmulFn_x3f_4410_; lean_object* v_homomulFn_x3f_4411_; lean_object* v_subFn_4412_; lean_object* v_negFn_4413_; lean_object* v_vars_4414_; lean_object* v_varMap_4415_; lean_object* v_lowers_4416_; lean_object* v_uppers_4417_; lean_object* v_diseqs_4418_; lean_object* v_assignment_4419_; uint8_t v_caseSplits_4420_; lean_object* v_conflict_x3f_4421_; lean_object* v_diseqSplits_4422_; lean_object* v_elimEqs_4423_; lean_object* v_elimStack_4424_; lean_object* v_occurs_4425_; lean_object* v_ignored_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4442_; 
v_v_4383_ = lean_array_fget(v_structs_4370_, v___y_4366_);
v_id_4384_ = lean_ctor_get(v_v_4383_, 0);
v_ringId_x3f_4385_ = lean_ctor_get(v_v_4383_, 1);
v_type_4386_ = lean_ctor_get(v_v_4383_, 2);
v_u_4387_ = lean_ctor_get(v_v_4383_, 3);
v_intModuleInst_4388_ = lean_ctor_get(v_v_4383_, 4);
v_leInst_x3f_4389_ = lean_ctor_get(v_v_4383_, 5);
v_ltInst_x3f_4390_ = lean_ctor_get(v_v_4383_, 6);
v_lawfulOrderLTInst_x3f_4391_ = lean_ctor_get(v_v_4383_, 7);
v_isPreorderInst_x3f_4392_ = lean_ctor_get(v_v_4383_, 8);
v_orderedAddInst_x3f_4393_ = lean_ctor_get(v_v_4383_, 9);
v_isLinearInst_x3f_4394_ = lean_ctor_get(v_v_4383_, 10);
v_noNatDivInst_x3f_4395_ = lean_ctor_get(v_v_4383_, 11);
v_ringInst_x3f_4396_ = lean_ctor_get(v_v_4383_, 12);
v_commRingInst_x3f_4397_ = lean_ctor_get(v_v_4383_, 13);
v_orderedRingInst_x3f_4398_ = lean_ctor_get(v_v_4383_, 14);
v_fieldInst_x3f_4399_ = lean_ctor_get(v_v_4383_, 15);
v_charInst_x3f_4400_ = lean_ctor_get(v_v_4383_, 16);
v_zero_4401_ = lean_ctor_get(v_v_4383_, 17);
v_ofNatZero_4402_ = lean_ctor_get(v_v_4383_, 18);
v_one_x3f_4403_ = lean_ctor_get(v_v_4383_, 19);
v_leFn_x3f_4404_ = lean_ctor_get(v_v_4383_, 20);
v_ltFn_x3f_4405_ = lean_ctor_get(v_v_4383_, 21);
v_addFn_4406_ = lean_ctor_get(v_v_4383_, 22);
v_zsmulFn_4407_ = lean_ctor_get(v_v_4383_, 23);
v_nsmulFn_4408_ = lean_ctor_get(v_v_4383_, 24);
v_zsmulFn_x3f_4409_ = lean_ctor_get(v_v_4383_, 25);
v_nsmulFn_x3f_4410_ = lean_ctor_get(v_v_4383_, 26);
v_homomulFn_x3f_4411_ = lean_ctor_get(v_v_4383_, 27);
v_subFn_4412_ = lean_ctor_get(v_v_4383_, 28);
v_negFn_4413_ = lean_ctor_get(v_v_4383_, 29);
v_vars_4414_ = lean_ctor_get(v_v_4383_, 30);
v_varMap_4415_ = lean_ctor_get(v_v_4383_, 31);
v_lowers_4416_ = lean_ctor_get(v_v_4383_, 32);
v_uppers_4417_ = lean_ctor_get(v_v_4383_, 33);
v_diseqs_4418_ = lean_ctor_get(v_v_4383_, 34);
v_assignment_4419_ = lean_ctor_get(v_v_4383_, 35);
v_caseSplits_4420_ = lean_ctor_get_uint8(v_v_4383_, sizeof(void*)*42);
v_conflict_x3f_4421_ = lean_ctor_get(v_v_4383_, 36);
v_diseqSplits_4422_ = lean_ctor_get(v_v_4383_, 37);
v_elimEqs_4423_ = lean_ctor_get(v_v_4383_, 38);
v_elimStack_4424_ = lean_ctor_get(v_v_4383_, 39);
v_occurs_4425_ = lean_ctor_get(v_v_4383_, 40);
v_ignored_4426_ = lean_ctor_get(v_v_4383_, 41);
v_isSharedCheck_4442_ = !lean_is_exclusive(v_v_4383_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4428_ = v_v_4383_;
v_isShared_4429_ = v_isSharedCheck_4442_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_ignored_4426_);
lean_inc(v_occurs_4425_);
lean_inc(v_elimStack_4424_);
lean_inc(v_elimEqs_4423_);
lean_inc(v_diseqSplits_4422_);
lean_inc(v_conflict_x3f_4421_);
lean_inc(v_assignment_4419_);
lean_inc(v_diseqs_4418_);
lean_inc(v_uppers_4417_);
lean_inc(v_lowers_4416_);
lean_inc(v_varMap_4415_);
lean_inc(v_vars_4414_);
lean_inc(v_negFn_4413_);
lean_inc(v_subFn_4412_);
lean_inc(v_homomulFn_x3f_4411_);
lean_inc(v_nsmulFn_x3f_4410_);
lean_inc(v_zsmulFn_x3f_4409_);
lean_inc(v_nsmulFn_4408_);
lean_inc(v_zsmulFn_4407_);
lean_inc(v_addFn_4406_);
lean_inc(v_ltFn_x3f_4405_);
lean_inc(v_leFn_x3f_4404_);
lean_inc(v_one_x3f_4403_);
lean_inc(v_ofNatZero_4402_);
lean_inc(v_zero_4401_);
lean_inc(v_charInst_x3f_4400_);
lean_inc(v_fieldInst_x3f_4399_);
lean_inc(v_orderedRingInst_x3f_4398_);
lean_inc(v_commRingInst_x3f_4397_);
lean_inc(v_ringInst_x3f_4396_);
lean_inc(v_noNatDivInst_x3f_4395_);
lean_inc(v_isLinearInst_x3f_4394_);
lean_inc(v_orderedAddInst_x3f_4393_);
lean_inc(v_isPreorderInst_x3f_4392_);
lean_inc(v_lawfulOrderLTInst_x3f_4391_);
lean_inc(v_ltInst_x3f_4390_);
lean_inc(v_leInst_x3f_4389_);
lean_inc(v_intModuleInst_4388_);
lean_inc(v_u_4387_);
lean_inc(v_type_4386_);
lean_inc(v_ringId_x3f_4385_);
lean_inc(v_id_4384_);
lean_dec(v_v_4383_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4442_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4430_; lean_object* v_xs_x27_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4436_; 
v___x_4430_ = lean_box(0);
v_xs_x27_4431_ = lean_array_fset(v_structs_4370_, v___y_4366_, v___x_4430_);
v___x_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4432_, 0, v_snd_4367_);
v___x_4433_ = l_Lean_PersistentArray_set___redArg(v_elimEqs_4423_, v_fst_4368_, v___x_4432_);
v___x_4434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4434_, 0, v_fst_4368_);
lean_ctor_set(v___x_4434_, 1, v_elimStack_4424_);
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 39, v___x_4434_);
lean_ctor_set(v___x_4428_, 38, v___x_4433_);
v___x_4436_ = v___x_4428_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_id_4384_);
lean_ctor_set(v_reuseFailAlloc_4441_, 1, v_ringId_x3f_4385_);
lean_ctor_set(v_reuseFailAlloc_4441_, 2, v_type_4386_);
lean_ctor_set(v_reuseFailAlloc_4441_, 3, v_u_4387_);
lean_ctor_set(v_reuseFailAlloc_4441_, 4, v_intModuleInst_4388_);
lean_ctor_set(v_reuseFailAlloc_4441_, 5, v_leInst_x3f_4389_);
lean_ctor_set(v_reuseFailAlloc_4441_, 6, v_ltInst_x3f_4390_);
lean_ctor_set(v_reuseFailAlloc_4441_, 7, v_lawfulOrderLTInst_x3f_4391_);
lean_ctor_set(v_reuseFailAlloc_4441_, 8, v_isPreorderInst_x3f_4392_);
lean_ctor_set(v_reuseFailAlloc_4441_, 9, v_orderedAddInst_x3f_4393_);
lean_ctor_set(v_reuseFailAlloc_4441_, 10, v_isLinearInst_x3f_4394_);
lean_ctor_set(v_reuseFailAlloc_4441_, 11, v_noNatDivInst_x3f_4395_);
lean_ctor_set(v_reuseFailAlloc_4441_, 12, v_ringInst_x3f_4396_);
lean_ctor_set(v_reuseFailAlloc_4441_, 13, v_commRingInst_x3f_4397_);
lean_ctor_set(v_reuseFailAlloc_4441_, 14, v_orderedRingInst_x3f_4398_);
lean_ctor_set(v_reuseFailAlloc_4441_, 15, v_fieldInst_x3f_4399_);
lean_ctor_set(v_reuseFailAlloc_4441_, 16, v_charInst_x3f_4400_);
lean_ctor_set(v_reuseFailAlloc_4441_, 17, v_zero_4401_);
lean_ctor_set(v_reuseFailAlloc_4441_, 18, v_ofNatZero_4402_);
lean_ctor_set(v_reuseFailAlloc_4441_, 19, v_one_x3f_4403_);
lean_ctor_set(v_reuseFailAlloc_4441_, 20, v_leFn_x3f_4404_);
lean_ctor_set(v_reuseFailAlloc_4441_, 21, v_ltFn_x3f_4405_);
lean_ctor_set(v_reuseFailAlloc_4441_, 22, v_addFn_4406_);
lean_ctor_set(v_reuseFailAlloc_4441_, 23, v_zsmulFn_4407_);
lean_ctor_set(v_reuseFailAlloc_4441_, 24, v_nsmulFn_4408_);
lean_ctor_set(v_reuseFailAlloc_4441_, 25, v_zsmulFn_x3f_4409_);
lean_ctor_set(v_reuseFailAlloc_4441_, 26, v_nsmulFn_x3f_4410_);
lean_ctor_set(v_reuseFailAlloc_4441_, 27, v_homomulFn_x3f_4411_);
lean_ctor_set(v_reuseFailAlloc_4441_, 28, v_subFn_4412_);
lean_ctor_set(v_reuseFailAlloc_4441_, 29, v_negFn_4413_);
lean_ctor_set(v_reuseFailAlloc_4441_, 30, v_vars_4414_);
lean_ctor_set(v_reuseFailAlloc_4441_, 31, v_varMap_4415_);
lean_ctor_set(v_reuseFailAlloc_4441_, 32, v_lowers_4416_);
lean_ctor_set(v_reuseFailAlloc_4441_, 33, v_uppers_4417_);
lean_ctor_set(v_reuseFailAlloc_4441_, 34, v_diseqs_4418_);
lean_ctor_set(v_reuseFailAlloc_4441_, 35, v_assignment_4419_);
lean_ctor_set(v_reuseFailAlloc_4441_, 36, v_conflict_x3f_4421_);
lean_ctor_set(v_reuseFailAlloc_4441_, 37, v_diseqSplits_4422_);
lean_ctor_set(v_reuseFailAlloc_4441_, 38, v___x_4433_);
lean_ctor_set(v_reuseFailAlloc_4441_, 39, v___x_4434_);
lean_ctor_set(v_reuseFailAlloc_4441_, 40, v_occurs_4425_);
lean_ctor_set(v_reuseFailAlloc_4441_, 41, v_ignored_4426_);
lean_ctor_set_uint8(v_reuseFailAlloc_4441_, sizeof(void*)*42, v_caseSplits_4420_);
v___x_4436_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
lean_object* v___x_4437_; lean_object* v___x_4439_; 
v___x_4437_ = lean_array_fset(v_xs_x27_4431_, v___y_4366_, v___x_4436_);
if (v_isShared_4382_ == 0)
{
lean_ctor_set(v___x_4381_, 0, v___x_4437_);
v___x_4439_ = v___x_4381_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4437_);
lean_ctor_set(v_reuseFailAlloc_4440_, 1, v_typeIdOf_4371_);
lean_ctor_set(v_reuseFailAlloc_4440_, 2, v_exprToStructId_4372_);
lean_ctor_set(v_reuseFailAlloc_4440_, 3, v_exprToStructIdEntries_4373_);
lean_ctor_set(v_reuseFailAlloc_4440_, 4, v_forbiddenNatModules_4374_);
lean_ctor_set(v_reuseFailAlloc_4440_, 5, v_natStructs_4375_);
lean_ctor_set(v_reuseFailAlloc_4440_, 6, v_natTypeIdOf_4376_);
lean_ctor_set(v_reuseFailAlloc_4440_, 7, v_exprToNatStructId_4377_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed(lean_object* v___y_4452_, lean_object* v_snd_4453_, lean_object* v_fst_4454_, lean_object* v_s_4455_){
_start:
{
lean_object* v_res_4456_; 
v_res_4456_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(v___y_4452_, v_snd_4453_, v_fst_4454_, v_s_4455_);
lean_dec(v___y_4452_);
return v_res_4456_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1(void){
_start:
{
lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4458_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0));
v___x_4459_ = l_Lean_stringToMessageData(v___x_4458_);
return v___x_4459_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4(void){
_start:
{
lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; 
v___x_4465_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4466_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4467_ = l_Lean_Name_append(v___x_4466_, v___x_4465_);
return v___x_4467_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object* v_c_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_){
_start:
{
lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4492_; lean_object* v___y_4493_; lean_object* v___y_4494_; lean_object* v___y_4495_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; lean_object* v___y_4500_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4514_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4521_; lean_object* v_toCold_4547_; lean_object* v_options_4548_; lean_object* v_inheritedTraceOptions_4549_; uint8_t v_hasTrace_4550_; lean_object* v___y_4552_; lean_object* v___y_4553_; lean_object* v___y_4554_; lean_object* v___y_4555_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v_options_4567_; lean_object* v_inheritedTraceOptions_4568_; lean_object* v___y_4569_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v___y_4590_; lean_object* v___y_4591_; lean_object* v___y_4592_; lean_object* v___y_4593_; lean_object* v___y_4594_; lean_object* v___y_4595_; lean_object* v___y_4596_; 
v_toCold_4547_ = lean_ctor_get(v_a_4478_, 0);
v_options_4548_ = lean_ctor_get(v_toCold_4547_, 2);
v_inheritedTraceOptions_4549_ = lean_ctor_get(v_toCold_4547_, 11);
v_hasTrace_4550_ = lean_ctor_get_uint8(v_options_4548_, sizeof(void*)*1);
if (v_hasTrace_4550_ == 0)
{
v___y_4586_ = v_a_4469_;
v___y_4587_ = v_a_4470_;
v___y_4588_ = v_a_4471_;
v___y_4589_ = v_a_4472_;
v___y_4590_ = v_a_4473_;
v___y_4591_ = v_a_4474_;
v___y_4592_ = v_a_4475_;
v___y_4593_ = v_a_4476_;
v___y_4594_ = v_a_4477_;
v___y_4595_ = v_a_4478_;
v___y_4596_ = v_a_4479_;
goto v___jp_4585_;
}
else
{
lean_object* v_cls_4694_; lean_object* v___x_4695_; uint8_t v___x_4696_; 
v_cls_4694_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_4695_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_4696_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4549_, v_options_4548_, v___x_4695_);
if (v___x_4696_ == 0)
{
v___y_4586_ = v_a_4469_;
v___y_4587_ = v_a_4470_;
v___y_4588_ = v_a_4471_;
v___y_4589_ = v_a_4472_;
v___y_4590_ = v_a_4473_;
v___y_4591_ = v_a_4474_;
v___y_4592_ = v_a_4475_;
v___y_4593_ = v_a_4476_;
v___y_4594_ = v_a_4477_;
v___y_4595_ = v_a_4478_;
v___y_4596_ = v_a_4479_;
goto v___jp_4585_;
}
else
{
lean_object* v___x_4697_; 
v___x_4697_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_4468_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_, v_a_4473_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_);
if (lean_obj_tag(v___x_4697_) == 0)
{
lean_object* v_a_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; 
v_a_4698_ = lean_ctor_get(v___x_4697_, 0);
lean_inc(v_a_4698_);
lean_dec_ref_known(v___x_4697_, 1);
v___x_4699_ = l_Lean_MessageData_ofExpr(v_a_4698_);
v___x_4700_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4694_, v___x_4699_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_);
if (lean_obj_tag(v___x_4700_) == 0)
{
lean_dec_ref_known(v___x_4700_, 1);
v___y_4586_ = v_a_4469_;
v___y_4587_ = v_a_4470_;
v___y_4588_ = v_a_4471_;
v___y_4589_ = v_a_4472_;
v___y_4590_ = v_a_4473_;
v___y_4591_ = v_a_4474_;
v___y_4592_ = v_a_4475_;
v___y_4593_ = v_a_4476_;
v___y_4594_ = v_a_4477_;
v___y_4595_ = v_a_4478_;
v___y_4596_ = v_a_4479_;
goto v___jp_4585_;
}
else
{
lean_dec_ref(v_c_4468_);
return v___x_4700_;
}
}
else
{
lean_object* v_a_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4708_; 
lean_dec_ref(v_c_4468_);
v_a_4701_ = lean_ctor_get(v___x_4697_, 0);
v_isSharedCheck_4708_ = !lean_is_exclusive(v___x_4697_);
if (v_isSharedCheck_4708_ == 0)
{
v___x_4703_ = v___x_4697_;
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_a_4701_);
lean_dec(v___x_4697_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v___x_4706_; 
if (v_isShared_4704_ == 0)
{
v___x_4706_ = v___x_4703_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_a_4701_);
v___x_4706_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
return v___x_4706_;
}
}
}
}
}
v___jp_4481_:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; 
v___x_4482_ = lean_box(0);
v___x_4483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4483_, 0, v___x_4482_);
return v___x_4483_;
}
v___jp_4484_:
{
lean_object* v___f_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; 
lean_inc(v___y_4490_);
v___f_4501_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4501_, 0, v___y_4490_);
lean_closure_set(v___f_4501_, 1, v___y_4486_);
lean_closure_set(v___f_4501_, 2, v___y_4485_);
v___x_4502_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4503_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4502_, v___f_4501_, v___y_4491_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v___x_4504_; 
lean_dec_ref_known(v___x_4503_, 1);
v___x_4504_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v___y_4489_, v___y_4487_, v___y_4488_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_);
return v___x_4504_;
}
else
{
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
return v___x_4503_;
}
}
v___jp_4505_:
{
lean_object* v___x_4522_; 
v___x_4522_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
if (lean_obj_tag(v___x_4522_) == 0)
{
lean_object* v_a_4523_; uint8_t v_caseSplits_4524_; 
v_a_4523_ = lean_ctor_get(v___x_4522_, 0);
lean_inc(v_a_4523_);
lean_dec_ref_known(v___x_4522_, 1);
v_caseSplits_4524_ = lean_ctor_get_uint8(v_a_4523_, sizeof(void*)*42);
lean_dec(v_a_4523_);
if (v_caseSplits_4524_ == 0)
{
lean_object* v___x_4525_; 
v___x_4525_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v___y_4509_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
if (lean_obj_tag(v___x_4525_) == 0)
{
lean_object* v_a_4526_; uint8_t v___x_4527_; 
v_a_4526_ = lean_ctor_get(v___x_4525_, 0);
lean_inc(v_a_4526_);
lean_dec_ref_known(v___x_4525_, 1);
v___x_4527_ = lean_unbox(v_a_4526_);
lean_dec(v_a_4526_);
if (v___x_4527_ == 0)
{
v___y_4485_ = v___y_4506_;
v___y_4486_ = v___y_4507_;
v___y_4487_ = v___y_4508_;
v___y_4488_ = v___y_4509_;
v___y_4489_ = v___y_4510_;
v___y_4490_ = v___y_4511_;
v___y_4491_ = v___y_4512_;
v___y_4492_ = v___y_4513_;
v___y_4493_ = v___y_4514_;
v___y_4494_ = v___y_4515_;
v___y_4495_ = v___y_4516_;
v___y_4496_ = v___y_4517_;
v___y_4497_ = v___y_4518_;
v___y_4498_ = v___y_4519_;
v___y_4499_ = v___y_4520_;
v___y_4500_ = v___y_4521_;
goto v___jp_4484_;
}
else
{
lean_object* v___x_4528_; lean_object* v_a_4529_; lean_object* v___x_4530_; 
lean_inc_ref(v___y_4509_);
v___x_4528_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v___y_4509_);
v_a_4529_ = lean_ctor_get(v___x_4528_, 0);
lean_inc(v_a_4529_);
lean_dec_ref(v___x_4528_);
v___x_4530_ = l_Lean_Meta_Grind_Arith_Linear_propagateImpEq(v_a_4529_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
if (lean_obj_tag(v___x_4530_) == 0)
{
lean_dec_ref_known(v___x_4530_, 1);
v___y_4485_ = v___y_4506_;
v___y_4486_ = v___y_4507_;
v___y_4487_ = v___y_4508_;
v___y_4488_ = v___y_4509_;
v___y_4489_ = v___y_4510_;
v___y_4490_ = v___y_4511_;
v___y_4491_ = v___y_4512_;
v___y_4492_ = v___y_4513_;
v___y_4493_ = v___y_4514_;
v___y_4494_ = v___y_4515_;
v___y_4495_ = v___y_4516_;
v___y_4496_ = v___y_4517_;
v___y_4497_ = v___y_4518_;
v___y_4498_ = v___y_4519_;
v___y_4499_ = v___y_4520_;
v___y_4500_ = v___y_4521_;
goto v___jp_4484_;
}
else
{
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
lean_dec(v___y_4506_);
return v___x_4530_;
}
}
}
else
{
lean_object* v_a_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4538_; 
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
lean_dec(v___y_4506_);
v_a_4531_ = lean_ctor_get(v___x_4525_, 0);
v_isSharedCheck_4538_ = !lean_is_exclusive(v___x_4525_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4533_ = v___x_4525_;
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_a_4531_);
lean_dec(v___x_4525_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4536_; 
if (v_isShared_4534_ == 0)
{
v___x_4536_ = v___x_4533_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
}
}
else
{
v___y_4485_ = v___y_4506_;
v___y_4486_ = v___y_4507_;
v___y_4487_ = v___y_4508_;
v___y_4488_ = v___y_4509_;
v___y_4489_ = v___y_4510_;
v___y_4490_ = v___y_4511_;
v___y_4491_ = v___y_4512_;
v___y_4492_ = v___y_4513_;
v___y_4493_ = v___y_4514_;
v___y_4494_ = v___y_4515_;
v___y_4495_ = v___y_4516_;
v___y_4496_ = v___y_4517_;
v___y_4497_ = v___y_4518_;
v___y_4498_ = v___y_4519_;
v___y_4499_ = v___y_4520_;
v___y_4500_ = v___y_4521_;
goto v___jp_4484_;
}
}
else
{
lean_object* v_a_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4546_; 
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
lean_dec(v___y_4506_);
v_a_4539_ = lean_ctor_get(v___x_4522_, 0);
v_isSharedCheck_4546_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4546_ == 0)
{
v___x_4541_ = v___x_4522_;
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
else
{
lean_inc(v_a_4539_);
lean_dec(v___x_4522_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v___x_4544_; 
if (v_isShared_4542_ == 0)
{
v___x_4544_ = v___x_4541_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_a_4539_);
v___x_4544_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
return v___x_4544_;
}
}
}
}
v___jp_4551_:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; uint8_t v___x_4572_; 
v___x_4570_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_4571_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_4572_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4568_, v_options_4567_, v___x_4571_);
if (v___x_4572_ == 0)
{
v___y_4506_ = v___y_4552_;
v___y_4507_ = v___y_4553_;
v___y_4508_ = v___y_4554_;
v___y_4509_ = v___y_4555_;
v___y_4510_ = v___y_4556_;
v___y_4511_ = v___y_4557_;
v___y_4512_ = v___y_4558_;
v___y_4513_ = v___y_4559_;
v___y_4514_ = v___y_4560_;
v___y_4515_ = v___y_4561_;
v___y_4516_ = v___y_4562_;
v___y_4517_ = v___y_4563_;
v___y_4518_ = v___y_4564_;
v___y_4519_ = v___y_4565_;
v___y_4520_ = v___y_4566_;
v___y_4521_ = v___y_4569_;
goto v___jp_4505_;
}
else
{
lean_object* v___x_4573_; 
v___x_4573_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v___y_4555_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4569_);
if (lean_obj_tag(v___x_4573_) == 0)
{
lean_object* v_a_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; 
v_a_4574_ = lean_ctor_get(v___x_4573_, 0);
lean_inc(v_a_4574_);
lean_dec_ref_known(v___x_4573_, 1);
v___x_4575_ = l_Lean_MessageData_ofExpr(v_a_4574_);
v___x_4576_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4570_, v___x_4575_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4569_);
if (lean_obj_tag(v___x_4576_) == 0)
{
lean_dec_ref_known(v___x_4576_, 1);
v___y_4506_ = v___y_4552_;
v___y_4507_ = v___y_4553_;
v___y_4508_ = v___y_4554_;
v___y_4509_ = v___y_4555_;
v___y_4510_ = v___y_4556_;
v___y_4511_ = v___y_4557_;
v___y_4512_ = v___y_4558_;
v___y_4513_ = v___y_4559_;
v___y_4514_ = v___y_4560_;
v___y_4515_ = v___y_4561_;
v___y_4516_ = v___y_4562_;
v___y_4517_ = v___y_4563_;
v___y_4518_ = v___y_4564_;
v___y_4519_ = v___y_4565_;
v___y_4520_ = v___y_4566_;
v___y_4521_ = v___y_4569_;
goto v___jp_4505_;
}
else
{
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
return v___x_4576_;
}
}
else
{
lean_object* v_a_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4584_; 
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
v_a_4577_ = lean_ctor_get(v___x_4573_, 0);
v_isSharedCheck_4584_ = !lean_is_exclusive(v___x_4573_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4579_ = v___x_4573_;
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_a_4577_);
lean_dec(v___x_4573_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4582_; 
if (v_isShared_4580_ == 0)
{
v___x_4582_ = v___x_4579_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
}
}
}
v___jp_4585_:
{
lean_object* v___x_4597_; 
lean_inc_ref(v___y_4595_);
v___x_4597_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_4468_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
if (lean_obj_tag(v___x_4597_) == 0)
{
lean_object* v_a_4598_; lean_object* v_p_4599_; lean_object* v___x_4600_; uint8_t v___x_4601_; 
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
lean_inc(v_a_4598_);
lean_dec_ref_known(v___x_4597_, 1);
v_p_4599_ = lean_ctor_get(v_a_4598_, 0);
v___x_4600_ = lean_box(0);
v___x_4601_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_4599_, v___x_4600_);
if (v___x_4601_ == 0)
{
lean_object* v___x_4602_; 
v___x_4602_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_a_4598_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v_a_4603_; lean_object* v_snd_4604_; lean_object* v_toCold_4605_; lean_object* v_options_4606_; uint8_t v_hasTrace_4607_; 
v_a_4603_ = lean_ctor_get(v___x_4602_, 0);
lean_inc(v_a_4603_);
lean_dec_ref_known(v___x_4602_, 1);
v_snd_4604_ = lean_ctor_get(v_a_4603_, 1);
lean_inc(v_snd_4604_);
v_toCold_4605_ = lean_ctor_get(v___y_4595_, 0);
v_options_4606_ = lean_ctor_get(v_toCold_4605_, 2);
v_hasTrace_4607_ = lean_ctor_get_uint8(v_options_4606_, sizeof(void*)*1);
if (v_hasTrace_4607_ == 0)
{
lean_object* v_fst_4608_; lean_object* v_fst_4609_; lean_object* v_snd_4610_; 
v_fst_4608_ = lean_ctor_get(v_a_4603_, 0);
lean_inc(v_fst_4608_);
lean_dec(v_a_4603_);
v_fst_4609_ = lean_ctor_get(v_snd_4604_, 0);
lean_inc_n(v_fst_4609_, 2);
v_snd_4610_ = lean_ctor_get(v_snd_4604_, 1);
lean_inc_n(v_snd_4610_, 2);
lean_dec(v_snd_4604_);
v___y_4506_ = v_fst_4609_;
v___y_4507_ = v_snd_4610_;
v___y_4508_ = v_fst_4609_;
v___y_4509_ = v_snd_4610_;
v___y_4510_ = v_fst_4608_;
v___y_4511_ = v___y_4586_;
v___y_4512_ = v___y_4587_;
v___y_4513_ = v___y_4588_;
v___y_4514_ = v___y_4589_;
v___y_4515_ = v___y_4590_;
v___y_4516_ = v___y_4591_;
v___y_4517_ = v___y_4592_;
v___y_4518_ = v___y_4593_;
v___y_4519_ = v___y_4594_;
v___y_4520_ = v___y_4595_;
v___y_4521_ = v___y_4596_;
goto v___jp_4505_;
}
else
{
lean_object* v_fst_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4657_; 
v_fst_4611_ = lean_ctor_get(v_a_4603_, 0);
v_isSharedCheck_4657_ = !lean_is_exclusive(v_a_4603_);
if (v_isSharedCheck_4657_ == 0)
{
lean_object* v_unused_4658_; 
v_unused_4658_ = lean_ctor_get(v_a_4603_, 1);
lean_dec(v_unused_4658_);
v___x_4613_ = v_a_4603_;
v_isShared_4614_ = v_isSharedCheck_4657_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_fst_4611_);
lean_dec(v_a_4603_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4657_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v_fst_4615_; lean_object* v_snd_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4656_; 
v_fst_4615_ = lean_ctor_get(v_snd_4604_, 0);
v_snd_4616_ = lean_ctor_get(v_snd_4604_, 1);
v_isSharedCheck_4656_ = !lean_is_exclusive(v_snd_4604_);
if (v_isSharedCheck_4656_ == 0)
{
v___x_4618_ = v_snd_4604_;
v_isShared_4619_ = v_isSharedCheck_4656_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_snd_4616_);
lean_inc(v_fst_4615_);
lean_dec(v_snd_4604_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4656_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v_inheritedTraceOptions_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; uint8_t v___x_4623_; 
v_inheritedTraceOptions_4620_ = lean_ctor_get(v_toCold_4605_, 11);
v___x_4621_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_4622_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_4623_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4620_, v_options_4606_, v___x_4622_);
if (v___x_4623_ == 0)
{
lean_del_object(v___x_4618_);
lean_del_object(v___x_4613_);
lean_inc(v_snd_4616_);
lean_inc(v_fst_4615_);
v___y_4552_ = v_fst_4615_;
v___y_4553_ = v_snd_4616_;
v___y_4554_ = v_fst_4615_;
v___y_4555_ = v_snd_4616_;
v___y_4556_ = v_fst_4611_;
v___y_4557_ = v___y_4586_;
v___y_4558_ = v___y_4587_;
v___y_4559_ = v___y_4588_;
v___y_4560_ = v___y_4589_;
v___y_4561_ = v___y_4590_;
v___y_4562_ = v___y_4591_;
v___y_4563_ = v___y_4592_;
v___y_4564_ = v___y_4593_;
v___y_4565_ = v___y_4594_;
v___y_4566_ = v___y_4595_;
v_options_4567_ = v_options_4606_;
v_inheritedTraceOptions_4568_ = v_inheritedTraceOptions_4620_;
v___y_4569_ = v___y_4596_;
goto v___jp_4551_;
}
else
{
lean_object* v___x_4624_; 
v___x_4624_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_4615_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_object* v_a_4625_; lean_object* v___x_4626_; 
v_a_4625_ = lean_ctor_get(v___x_4624_, 0);
lean_inc(v_a_4625_);
lean_dec_ref_known(v___x_4624_, 1);
v___x_4626_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_4616_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
if (lean_obj_tag(v___x_4626_) == 0)
{
lean_object* v_a_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4631_; 
v_a_4627_ = lean_ctor_get(v___x_4626_, 0);
lean_inc(v_a_4627_);
lean_dec_ref_known(v___x_4626_, 1);
v___x_4628_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1);
v___x_4629_ = l_Lean_MessageData_ofExpr(v_a_4625_);
if (v_isShared_4619_ == 0)
{
lean_ctor_set_tag(v___x_4618_, 7);
lean_ctor_set(v___x_4618_, 1, v___x_4629_);
lean_ctor_set(v___x_4618_, 0, v___x_4628_);
v___x_4631_ = v___x_4618_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v___x_4628_);
lean_ctor_set(v_reuseFailAlloc_4639_, 1, v___x_4629_);
v___x_4631_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
lean_object* v___x_4632_; lean_object* v___x_4634_; 
v___x_4632_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_4614_ == 0)
{
lean_ctor_set_tag(v___x_4613_, 7);
lean_ctor_set(v___x_4613_, 1, v___x_4632_);
lean_ctor_set(v___x_4613_, 0, v___x_4631_);
v___x_4634_ = v___x_4613_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4631_);
lean_ctor_set(v_reuseFailAlloc_4638_, 1, v___x_4632_);
v___x_4634_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4635_ = l_Lean_MessageData_ofExpr(v_a_4627_);
v___x_4636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4636_, 0, v___x_4634_);
lean_ctor_set(v___x_4636_, 1, v___x_4635_);
v___x_4637_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4621_, v___x_4636_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
if (lean_obj_tag(v___x_4637_) == 0)
{
lean_dec_ref_known(v___x_4637_, 1);
lean_inc(v_snd_4616_);
lean_inc(v_fst_4615_);
v___y_4552_ = v_fst_4615_;
v___y_4553_ = v_snd_4616_;
v___y_4554_ = v_fst_4615_;
v___y_4555_ = v_snd_4616_;
v___y_4556_ = v_fst_4611_;
v___y_4557_ = v___y_4586_;
v___y_4558_ = v___y_4587_;
v___y_4559_ = v___y_4588_;
v___y_4560_ = v___y_4589_;
v___y_4561_ = v___y_4590_;
v___y_4562_ = v___y_4591_;
v___y_4563_ = v___y_4592_;
v___y_4564_ = v___y_4593_;
v___y_4565_ = v___y_4594_;
v___y_4566_ = v___y_4595_;
v_options_4567_ = v_options_4606_;
v_inheritedTraceOptions_4568_ = v_inheritedTraceOptions_4620_;
v___y_4569_ = v___y_4596_;
goto v___jp_4551_;
}
else
{
lean_dec(v_snd_4616_);
lean_dec(v_fst_4615_);
lean_dec(v_fst_4611_);
return v___x_4637_;
}
}
}
}
else
{
lean_object* v_a_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4647_; 
lean_dec(v_a_4625_);
lean_del_object(v___x_4618_);
lean_dec(v_snd_4616_);
lean_dec(v_fst_4615_);
lean_del_object(v___x_4613_);
lean_dec(v_fst_4611_);
v_a_4640_ = lean_ctor_get(v___x_4626_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4642_ = v___x_4626_;
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_a_4640_);
lean_dec(v___x_4626_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v___x_4645_; 
if (v_isShared_4643_ == 0)
{
v___x_4645_ = v___x_4642_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_a_4640_);
v___x_4645_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
return v___x_4645_;
}
}
}
}
else
{
lean_object* v_a_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4655_; 
lean_del_object(v___x_4618_);
lean_dec(v_snd_4616_);
lean_dec(v_fst_4615_);
lean_del_object(v___x_4613_);
lean_dec(v_fst_4611_);
v_a_4648_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4655_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4650_ = v___x_4624_;
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_a_4648_);
lean_dec(v___x_4624_);
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
}
}
}
else
{
lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4666_; 
v_a_4659_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4666_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4661_ = v___x_4602_;
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_a_4659_);
lean_dec(v___x_4602_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v___x_4664_; 
if (v_isShared_4662_ == 0)
{
v___x_4664_ = v___x_4661_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v_a_4659_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
return v___x_4664_;
}
}
}
}
else
{
lean_object* v_toCold_4667_; lean_object* v_options_4668_; uint8_t v_hasTrace_4669_; 
v_toCold_4667_ = lean_ctor_get(v___y_4595_, 0);
v_options_4668_ = lean_ctor_get(v_toCold_4667_, 2);
v_hasTrace_4669_ = lean_ctor_get_uint8(v_options_4668_, sizeof(void*)*1);
if (v_hasTrace_4669_ == 0)
{
lean_dec(v_a_4598_);
goto v___jp_4481_;
}
else
{
lean_object* v_inheritedTraceOptions_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; uint8_t v___x_4673_; 
v_inheritedTraceOptions_4670_ = lean_ctor_get(v_toCold_4667_, 11);
v___x_4671_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4672_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4);
v___x_4673_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4670_, v_options_4668_, v___x_4672_);
if (v___x_4673_ == 0)
{
lean_dec(v_a_4598_);
goto v___jp_4481_;
}
else
{
lean_object* v___x_4674_; 
v___x_4674_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_a_4598_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
lean_dec(v_a_4598_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v_a_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v_a_4675_ = lean_ctor_get(v___x_4674_, 0);
lean_inc(v_a_4675_);
lean_dec_ref_known(v___x_4674_, 1);
v___x_4676_ = l_Lean_MessageData_ofExpr(v_a_4675_);
v___x_4677_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4671_, v___x_4676_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_dec_ref_known(v___x_4677_, 1);
goto v___jp_4481_;
}
else
{
return v___x_4677_;
}
}
else
{
lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4685_; 
v_a_4678_ = lean_ctor_get(v___x_4674_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4674_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4680_ = v___x_4674_;
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_dec(v___x_4674_);
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
}
}
}
else
{
lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4693_; 
v_a_4686_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4688_ = v___x_4597_;
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_a_4686_);
lean_dec(v___x_4597_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4691_; 
if (v_isShared_4689_ == 0)
{
v___x_4691_ = v___x_4688_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4686_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
return v___x_4691_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_4468_ = stack[0].m_obj;
lean_object* v_a_4469_ = stack[1].m_obj;
lean_object* v_a_4470_ = stack[2].m_obj;
lean_object* v_a_4471_ = stack[3].m_obj;
lean_object* v_a_4472_ = stack[4].m_obj;
lean_object* v_a_4473_ = stack[5].m_obj;
lean_object* v_a_4474_ = stack[6].m_obj;
lean_object* v_a_4475_ = stack[7].m_obj;
lean_object* v_a_4476_ = stack[8].m_obj;
lean_object* v_a_4477_ = stack[9].m_obj;
lean_object* v_a_4478_ = stack[10].m_obj;
lean_object* v_a_4479_ = stack[11].m_obj;
lean_object* v_res_4709_;
v_res_4709_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v_c_4468_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_, v_a_4473_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_);
stack->m_obj
 = v_res_4709_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object* v_c_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_){
_start:
{
lean_object* v_res_4723_; 
v_res_4723_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v_c_4710_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_);
lean_dec(v_a_4721_);
lean_dec_ref(v_a_4720_);
lean_dec(v_a_4719_);
lean_dec_ref(v_a_4718_);
lean_dec(v_a_4717_);
lean_dec_ref(v_a_4716_);
lean_dec(v_a_4715_);
lean_dec_ref(v_a_4714_);
lean_dec(v_a_4713_);
lean_dec(v_a_4712_);
lean_dec(v_a_4711_);
return v_res_4723_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2(void){
_start:
{
lean_object* v_cls_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; 
v_cls_4728_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4729_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4730_ = l_Lean_Name_append(v___x_4729_, v_cls_4728_);
return v___x_4730_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object* v_a_4731_, lean_object* v_b_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_){
_start:
{
lean_object* v_toCold_4741_; lean_object* v_options_4742_; uint8_t v_hasTrace_4743_; 
v_toCold_4741_ = lean_ctor_get(v_a_4735_, 0);
v_options_4742_ = lean_ctor_get(v_toCold_4741_, 2);
v_hasTrace_4743_ = lean_ctor_get_uint8(v_options_4742_, sizeof(void*)*1);
if (v_hasTrace_4743_ == 0)
{
lean_dec_ref(v_b_4732_);
lean_dec_ref(v_a_4731_);
goto v___jp_4738_;
}
else
{
lean_object* v_inheritedTraceOptions_4744_; lean_object* v_cls_4745_; lean_object* v___x_4746_; uint8_t v___x_4747_; 
v_inheritedTraceOptions_4744_ = lean_ctor_get(v_toCold_4741_, 11);
v_cls_4745_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4746_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2);
v___x_4747_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4744_, v_options_4742_, v___x_4746_);
if (v___x_4747_ == 0)
{
lean_dec_ref(v_b_4732_);
lean_dec_ref(v_a_4731_);
goto v___jp_4738_;
}
else
{
lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4748_ = l_Lean_MessageData_ofExpr(v_a_4731_);
v___x_4749_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_4750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4748_);
lean_ctor_set(v___x_4750_, 1, v___x_4749_);
v___x_4751_ = l_Lean_MessageData_ofExpr(v_b_4732_);
v___x_4752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4752_, 0, v___x_4750_);
lean_ctor_set(v___x_4752_, 1, v___x_4751_);
v___x_4753_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4745_, v___x_4752_, v_a_4733_, v_a_4734_, v_a_4735_, v_a_4736_);
return v___x_4753_;
}
}
v___jp_4738_:
{
lean_object* v___x_4739_; lean_object* v___x_4740_; 
v___x_4739_ = lean_box(0);
v___x_4740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4740_, 0, v___x_4739_);
return v___x_4740_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4731_ = stack[0].m_obj;
lean_object* v_b_4732_ = stack[1].m_obj;
lean_object* v_a_4733_ = stack[2].m_obj;
lean_object* v_a_4734_ = stack[3].m_obj;
lean_object* v_a_4735_ = stack[4].m_obj;
lean_object* v_a_4736_ = stack[5].m_obj;
lean_object* v_res_4754_;
v_res_4754_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4731_, v_b_4732_, v_a_4733_, v_a_4734_, v_a_4735_, v_a_4736_);
stack->m_obj
 = v_res_4754_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object* v_a_4755_, lean_object* v_b_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4755_, v_b_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_);
lean_dec(v_a_4760_);
lean_dec_ref(v_a_4759_);
lean_dec(v_a_4758_);
lean_dec_ref(v_a_4757_);
return v_res_4762_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object* v_a_4763_, lean_object* v_b_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_){
_start:
{
lean_object* v___x_4777_; 
v___x_4777_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4763_, v_b_4764_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_);
return v___x_4777_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4763_ = stack[0].m_obj;
lean_object* v_b_4764_ = stack[1].m_obj;
lean_object* v_a_4765_ = stack[2].m_obj;
lean_object* v_a_4766_ = stack[3].m_obj;
lean_object* v_a_4767_ = stack[4].m_obj;
lean_object* v_a_4768_ = stack[5].m_obj;
lean_object* v_a_4769_ = stack[6].m_obj;
lean_object* v_a_4770_ = stack[7].m_obj;
lean_object* v_a_4771_ = stack[8].m_obj;
lean_object* v_a_4772_ = stack[9].m_obj;
lean_object* v_a_4773_ = stack[10].m_obj;
lean_object* v_a_4774_ = stack[11].m_obj;
lean_object* v_a_4775_ = stack[12].m_obj;
lean_object* v_res_4778_;
v_res_4778_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(v_a_4763_, v_b_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_);
stack->m_obj
 = v_res_4778_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object* v_a_4779_, lean_object* v_b_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_){
_start:
{
lean_object* v_res_4793_; 
v_res_4793_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(v_a_4779_, v_b_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_);
lean_dec(v_a_4791_);
lean_dec_ref(v_a_4790_);
lean_dec(v_a_4789_);
lean_dec_ref(v_a_4788_);
lean_dec(v_a_4787_);
lean_dec_ref(v_a_4786_);
lean_dec(v_a_4785_);
lean_dec_ref(v_a_4784_);
lean_dec(v_a_4783_);
lean_dec(v_a_4782_);
lean_dec(v_a_4781_);
return v_res_4793_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object* v_a_4794_, lean_object* v_b_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_){
_start:
{
uint8_t v___x_4808_; lean_object* v___x_4809_; 
v___x_4808_ = 0;
lean_inc_ref(v_a_4794_);
v___x_4809_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_4794_, v___x_4808_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_);
if (lean_obj_tag(v___x_4809_) == 0)
{
lean_object* v_a_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4849_; 
v_a_4810_ = lean_ctor_get(v___x_4809_, 0);
v_isSharedCheck_4849_ = !lean_is_exclusive(v___x_4809_);
if (v_isSharedCheck_4849_ == 0)
{
v___x_4812_ = v___x_4809_;
v_isShared_4813_ = v_isSharedCheck_4849_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_a_4810_);
lean_dec(v___x_4809_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4849_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
if (lean_obj_tag(v_a_4810_) == 1)
{
lean_object* v_val_4814_; lean_object* v___x_4815_; 
lean_del_object(v___x_4812_);
v_val_4814_ = lean_ctor_get(v_a_4810_, 0);
lean_inc(v_val_4814_);
lean_dec_ref_known(v_a_4810_, 1);
lean_inc_ref(v_b_4795_);
v___x_4815_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_4795_, v___x_4808_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_);
if (lean_obj_tag(v___x_4815_) == 0)
{
lean_object* v_a_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4836_; 
v_a_4816_ = lean_ctor_get(v___x_4815_, 0);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4818_ = v___x_4815_;
v_isShared_4819_ = v_isSharedCheck_4836_;
goto v_resetjp_4817_;
}
else
{
lean_inc(v_a_4816_);
lean_dec(v___x_4815_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4836_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
if (lean_obj_tag(v_a_4816_) == 1)
{
lean_object* v_val_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; uint8_t v___x_4824_; 
v_val_4820_ = lean_ctor_get(v_a_4816_, 0);
lean_inc_n(v_val_4820_, 2);
lean_dec_ref_known(v_a_4816_, 1);
lean_inc(v_val_4814_);
v___x_4821_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4821_, 0, v_val_4814_);
lean_ctor_set(v___x_4821_, 1, v_val_4820_);
v___x_4822_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4821_);
v___x_4823_ = lean_box(0);
v___x_4824_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4822_, v___x_4823_);
if (v___x_4824_ == 0)
{
lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; 
lean_del_object(v___x_4818_);
v___x_4825_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4825_, 0, v_a_4794_);
lean_ctor_set(v___x_4825_, 1, v_b_4795_);
lean_ctor_set(v___x_4825_, 2, v_val_4814_);
lean_ctor_set(v___x_4825_, 3, v_val_4820_);
v___x_4826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4822_);
lean_ctor_set(v___x_4826_, 1, v___x_4825_);
v___x_4827_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_4826_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_);
return v___x_4827_;
}
else
{
lean_object* v___x_4828_; lean_object* v___x_4830_; 
lean_dec(v___x_4822_);
lean_dec(v_val_4820_);
lean_dec(v_val_4814_);
lean_dec_ref(v_b_4795_);
lean_dec_ref(v_a_4794_);
v___x_4828_ = lean_box(0);
if (v_isShared_4819_ == 0)
{
lean_ctor_set(v___x_4818_, 0, v___x_4828_);
v___x_4830_ = v___x_4818_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v___x_4828_);
v___x_4830_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
return v___x_4830_;
}
}
}
else
{
lean_object* v___x_4832_; lean_object* v___x_4834_; 
lean_dec(v_a_4816_);
lean_dec(v_val_4814_);
lean_dec_ref(v_b_4795_);
lean_dec_ref(v_a_4794_);
v___x_4832_ = lean_box(0);
if (v_isShared_4819_ == 0)
{
lean_ctor_set(v___x_4818_, 0, v___x_4832_);
v___x_4834_ = v___x_4818_;
goto v_reusejp_4833_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v___x_4832_);
v___x_4834_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4833_;
}
v_reusejp_4833_:
{
return v___x_4834_;
}
}
}
}
else
{
lean_object* v_a_4837_; lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4844_; 
lean_dec(v_val_4814_);
lean_dec_ref(v_b_4795_);
lean_dec_ref(v_a_4794_);
v_a_4837_ = lean_ctor_get(v___x_4815_, 0);
v_isSharedCheck_4844_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4839_ = v___x_4815_;
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
else
{
lean_inc(v_a_4837_);
lean_dec(v___x_4815_);
v___x_4839_ = lean_box(0);
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
v_resetjp_4838_:
{
lean_object* v___x_4842_; 
if (v_isShared_4840_ == 0)
{
v___x_4842_ = v___x_4839_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v_a_4837_);
v___x_4842_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
return v___x_4842_;
}
}
}
}
else
{
lean_object* v___x_4845_; lean_object* v___x_4847_; 
lean_dec(v_a_4810_);
lean_dec_ref(v_b_4795_);
lean_dec_ref(v_a_4794_);
v___x_4845_ = lean_box(0);
if (v_isShared_4813_ == 0)
{
lean_ctor_set(v___x_4812_, 0, v___x_4845_);
v___x_4847_ = v___x_4812_;
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
}
else
{
lean_object* v_a_4850_; lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4857_; 
lean_dec_ref(v_b_4795_);
lean_dec_ref(v_a_4794_);
v_a_4850_ = lean_ctor_get(v___x_4809_, 0);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4809_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4852_ = v___x_4809_;
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
else
{
lean_inc(v_a_4850_);
lean_dec(v___x_4809_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v___x_4855_; 
if (v_isShared_4853_ == 0)
{
v___x_4855_ = v___x_4852_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4794_ = stack[0].m_obj;
lean_object* v_b_4795_ = stack[1].m_obj;
lean_object* v_a_4796_ = stack[2].m_obj;
lean_object* v_a_4797_ = stack[3].m_obj;
lean_object* v_a_4798_ = stack[4].m_obj;
lean_object* v_a_4799_ = stack[5].m_obj;
lean_object* v_a_4800_ = stack[6].m_obj;
lean_object* v_a_4801_ = stack[7].m_obj;
lean_object* v_a_4802_ = stack[8].m_obj;
lean_object* v_a_4803_ = stack[9].m_obj;
lean_object* v_a_4804_ = stack[10].m_obj;
lean_object* v_a_4805_ = stack[11].m_obj;
lean_object* v_a_4806_ = stack[12].m_obj;
lean_object* v_res_4858_;
v_res_4858_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_4794_, v_b_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_);
stack->m_obj
 = v_res_4858_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___boxed(lean_object* v_a_4859_, lean_object* v_b_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_){
_start:
{
lean_object* v_res_4873_; 
v_res_4873_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_4859_, v_b_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_);
lean_dec(v_a_4871_);
lean_dec_ref(v_a_4870_);
lean_dec(v_a_4869_);
lean_dec_ref(v_a_4868_);
lean_dec(v_a_4867_);
lean_dec_ref(v_a_4866_);
lean_dec(v_a_4865_);
lean_dec_ref(v_a_4864_);
lean_dec(v_a_4863_);
lean_dec(v_a_4862_);
lean_dec(v_a_4861_);
return v_res_4873_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(lean_object* v_a_4874_, lean_object* v_b_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_){
_start:
{
lean_object* v___x_4888_; 
v___x_4888_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
if (lean_obj_tag(v___x_4888_) == 0)
{
lean_object* v_a_4889_; lean_object* v___x_4890_; 
v_a_4889_ = lean_ctor_get(v___x_4888_, 0);
lean_inc(v_a_4889_);
lean_dec_ref_known(v___x_4888_, 1);
lean_inc_ref(v_a_4874_);
v___x_4890_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_4874_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
if (lean_obj_tag(v___x_4890_) == 0)
{
lean_object* v_a_4891_; lean_object* v_fst_4892_; lean_object* v___x_4893_; 
v_a_4891_ = lean_ctor_get(v___x_4890_, 0);
lean_inc(v_a_4891_);
lean_dec_ref_known(v___x_4890_, 1);
v_fst_4892_ = lean_ctor_get(v_a_4891_, 0);
lean_inc(v_fst_4892_);
lean_dec(v_a_4891_);
lean_inc_ref(v_b_4875_);
v___x_4893_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
if (lean_obj_tag(v___x_4893_) == 0)
{
lean_object* v_a_4894_; lean_object* v_fst_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4958_; 
v_a_4894_ = lean_ctor_get(v___x_4893_, 0);
lean_inc(v_a_4894_);
lean_dec_ref_known(v___x_4893_, 1);
v_fst_4895_ = lean_ctor_get(v_a_4894_, 0);
v_isSharedCheck_4958_ = !lean_is_exclusive(v_a_4894_);
if (v_isSharedCheck_4958_ == 0)
{
lean_object* v_unused_4959_; 
v_unused_4959_ = lean_ctor_get(v_a_4894_, 1);
lean_dec(v_unused_4959_);
v___x_4897_ = v_a_4894_;
v_isShared_4898_ = v_isSharedCheck_4958_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_fst_4895_);
lean_dec(v_a_4894_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4958_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v_id_4899_; lean_object* v_structId_4900_; uint8_t v___x_4901_; lean_object* v___x_4902_; 
v_id_4899_ = lean_ctor_get(v_a_4889_, 0);
lean_inc(v_id_4899_);
v_structId_4900_ = lean_ctor_get(v_a_4889_, 1);
lean_inc(v_structId_4900_);
lean_dec(v_a_4889_);
v___x_4901_ = 0;
v___x_4902_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4892_, v___x_4901_, v_structId_4900_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
if (lean_obj_tag(v___x_4902_) == 0)
{
lean_object* v_a_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4949_; 
v_a_4903_ = lean_ctor_get(v___x_4902_, 0);
v_isSharedCheck_4949_ = !lean_is_exclusive(v___x_4902_);
if (v_isSharedCheck_4949_ == 0)
{
v___x_4905_ = v___x_4902_;
v_isShared_4906_ = v_isSharedCheck_4949_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_a_4903_);
lean_dec(v___x_4902_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4949_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
if (lean_obj_tag(v_a_4903_) == 1)
{
lean_object* v_val_4907_; lean_object* v___x_4908_; 
lean_del_object(v___x_4905_);
v_val_4907_ = lean_ctor_get(v_a_4903_, 0);
lean_inc(v_val_4907_);
lean_dec_ref_known(v_a_4903_, 1);
v___x_4908_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4895_, v___x_4901_, v_structId_4900_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
if (lean_obj_tag(v___x_4908_) == 0)
{
lean_object* v_a_4909_; lean_object* v___x_4911_; uint8_t v_isShared_4912_; uint8_t v_isSharedCheck_4936_; 
v_a_4909_ = lean_ctor_get(v___x_4908_, 0);
v_isSharedCheck_4936_ = !lean_is_exclusive(v___x_4908_);
if (v_isSharedCheck_4936_ == 0)
{
v___x_4911_ = v___x_4908_;
v_isShared_4912_ = v_isSharedCheck_4936_;
goto v_resetjp_4910_;
}
else
{
lean_inc(v_a_4909_);
lean_dec(v___x_4908_);
v___x_4911_ = lean_box(0);
v_isShared_4912_ = v_isSharedCheck_4936_;
goto v_resetjp_4910_;
}
v_resetjp_4910_:
{
if (lean_obj_tag(v_a_4909_) == 1)
{
lean_object* v_val_4913_; lean_object* v___x_4915_; 
v_val_4913_ = lean_ctor_get(v_a_4909_, 0);
lean_inc_n(v_val_4913_, 2);
lean_dec_ref_known(v_a_4909_, 1);
lean_inc(v_val_4907_);
if (v_isShared_4898_ == 0)
{
lean_ctor_set_tag(v___x_4897_, 3);
lean_ctor_set(v___x_4897_, 1, v_val_4913_);
lean_ctor_set(v___x_4897_, 0, v_val_4907_);
v___x_4915_ = v___x_4897_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_val_4907_);
lean_ctor_set(v_reuseFailAlloc_4931_, 1, v_val_4913_);
v___x_4915_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
lean_object* v___x_4916_; lean_object* v___x_4917_; uint8_t v___x_4918_; 
v___x_4916_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4915_);
v___x_4917_ = lean_box(0);
v___x_4918_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4916_, v___x_4917_);
if (v___x_4918_ == 0)
{
lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; 
lean_del_object(v___x_4911_);
lean_inc(v_val_4913_);
lean_inc(v_val_4907_);
lean_inc(v_id_4899_);
lean_inc_ref(v_b_4875_);
lean_inc_ref(v_a_4874_);
v___x_4919_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4919_, 0, v_a_4874_);
lean_ctor_set(v___x_4919_, 1, v_b_4875_);
lean_ctor_set(v___x_4919_, 2, v_id_4899_);
lean_ctor_set(v___x_4919_, 3, v_val_4907_);
lean_ctor_set(v___x_4919_, 4, v_val_4913_);
lean_inc(v___x_4916_);
v___x_4920_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4920_, 0, v___x_4916_);
lean_ctor_set(v___x_4920_, 1, v___x_4919_);
lean_ctor_set_uint8(v___x_4920_, sizeof(void*)*2, v___x_4901_);
v___x_4921_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4920_, v_structId_4900_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
if (lean_obj_tag(v___x_4921_) == 0)
{
lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; 
lean_dec_ref_known(v___x_4921_, 1);
v___x_4922_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4923_ = l_Lean_Grind_Linarith_Poly_mul(v___x_4916_, v___x_4922_);
v___x_4924_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4924_, 0, v_b_4875_);
lean_ctor_set(v___x_4924_, 1, v_a_4874_);
lean_ctor_set(v___x_4924_, 2, v_id_4899_);
lean_ctor_set(v___x_4924_, 3, v_val_4913_);
lean_ctor_set(v___x_4924_, 4, v_val_4907_);
v___x_4925_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4925_, 0, v___x_4923_);
lean_ctor_set(v___x_4925_, 1, v___x_4924_);
lean_ctor_set_uint8(v___x_4925_, sizeof(void*)*2, v___x_4901_);
v___x_4926_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4925_, v_structId_4900_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
lean_dec(v_structId_4900_);
return v___x_4926_;
}
else
{
lean_dec(v___x_4916_);
lean_dec(v_val_4913_);
lean_dec(v_val_4907_);
lean_dec(v_structId_4900_);
lean_dec(v_id_4899_);
lean_dec_ref(v_b_4875_);
lean_dec_ref(v_a_4874_);
return v___x_4921_;
}
}
else
{
lean_object* v___x_4927_; lean_object* v___x_4929_; 
lean_dec(v___x_4916_);
lean_dec(v_val_4913_);
lean_dec(v_val_4907_);
lean_dec(v_structId_4900_);
lean_dec(v_id_4899_);
lean_dec_ref(v_b_4875_);
lean_dec_ref(v_a_4874_);
v___x_4927_ = lean_box(0);
if (v_isShared_4912_ == 0)
{
lean_ctor_set(v___x_4911_, 0, v___x_4927_);
v___x_4929_ = v___x_4911_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v___x_4927_);
v___x_4929_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
return v___x_4929_;
}
}
}
}
else
{
lean_object* v___x_4932_; lean_object* v___x_4934_; 
lean_dec(v_a_4909_);
lean_dec(v_val_4907_);
lean_dec(v_structId_4900_);
lean_dec(v_id_4899_);
lean_del_object(v___x_4897_);
lean_dec_ref(v_b_4875_);
lean_dec_ref(v_a_4874_);
v___x_4932_ = lean_box(0);
if (v_isShared_4912_ == 0)
{
lean_ctor_set(v___x_4911_, 0, v___x_4932_);
v___x_4934_ = v___x_4911_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v___x_4932_);
v___x_4934_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
return v___x_4934_;
}
}
}
}
else
{
lean_object* v_a_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4944_; 
lean_dec(v_val_4907_);
lean_dec(v_structId_4900_);
lean_dec(v_id_4899_);
lean_del_object(v___x_4897_);
lean_dec_ref(v_b_4875_);
lean_dec_ref(v_a_4874_);
v_a_4937_ = lean_ctor_get(v___x_4908_, 0);
v_isSharedCheck_4944_ = !lean_is_exclusive(v___x_4908_);
if (v_isSharedCheck_4944_ == 0)
{
v___x_4939_ = v___x_4908_;
v_isShared_4940_ = v_isSharedCheck_4944_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_a_4937_);
lean_dec(v___x_4908_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4944_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v___x_4942_; 
if (v_isShared_4940_ == 0)
{
v___x_4942_ = v___x_4939_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v_a_4937_);
v___x_4942_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
return v___x_4942_;
}
}
}
}
else
{
lean_object* v___x_4945_; lean_object* v___x_4947_; 
lean_dec(v_a_4903_);
lean_dec(v_structId_4900_);
lean_dec(v_id_4899_);
lean_del_object(v___x_4897_);
lean_dec(v_fst_4895_);
lean_dec_ref(v_b_4875_);
lean_dec_ref(v_a_4874_);
v___x_4945_ = lean_box(0);
if (v_isShared_4906_ == 0)
{
lean_ctor_set(v___x_4905_, 0, v___x_4945_);
v___x_4947_ = v___x_4905_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4948_; 
v_reuseFailAlloc_4948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4948_, 0, v___x_4945_);
v___x_4947_ = v_reuseFailAlloc_4948_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
return v___x_4947_;
}
}
}
}
else
{
lean_object* v_a_4950_; lean_object* v___x_4952_; uint8_t v_isShared_4953_; uint8_t v_isSharedCheck_4957_; 
lean_dec(v_structId_4900_);
lean_dec(v_id_4899_);
lean_del_object(v___x_4897_);
lean_dec(v_fst_4895_);
lean_dec_ref(v_b_4875_);
lean_dec_ref(v_a_4874_);
v_a_4950_ = lean_ctor_get(v___x_4902_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4902_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4952_ = v___x_4902_;
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
else
{
lean_inc(v_a_4950_);
lean_dec(v___x_4902_);
v___x_4952_ = lean_box(0);
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
v_resetjp_4951_:
{
lean_object* v___x_4955_; 
if (v_isShared_4953_ == 0)
{
v___x_4955_ = v___x_4952_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_a_4950_);
v___x_4955_ = v_reuseFailAlloc_4956_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
return v___x_4955_;
}
}
}
}
}
else
{
lean_object* v_a_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_4967_; 
lean_dec(v_fst_4892_);
lean_dec(v_a_4889_);
lean_dec_ref(v_b_4875_);
lean_dec_ref(v_a_4874_);
v_a_4960_ = lean_ctor_get(v___x_4893_, 0);
v_isSharedCheck_4967_ = !lean_is_exclusive(v___x_4893_);
if (v_isSharedCheck_4967_ == 0)
{
v___x_4962_ = v___x_4893_;
v_isShared_4963_ = v_isSharedCheck_4967_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_a_4960_);
lean_dec(v___x_4893_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_4967_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
lean_object* v___x_4965_; 
if (v_isShared_4963_ == 0)
{
v___x_4965_ = v___x_4962_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v_a_4960_);
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
lean_object* v_a_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_4975_; 
lean_dec(v_a_4889_);
lean_dec_ref(v_b_4875_);
lean_dec_ref(v_a_4874_);
v_a_4968_ = lean_ctor_get(v___x_4890_, 0);
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4975_ == 0)
{
v___x_4970_ = v___x_4890_;
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_a_4968_);
lean_dec(v___x_4890_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v___x_4973_; 
if (v_isShared_4971_ == 0)
{
v___x_4973_ = v___x_4970_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_a_4968_);
v___x_4973_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
return v___x_4973_;
}
}
}
}
else
{
lean_object* v_a_4976_; lean_object* v___x_4978_; uint8_t v_isShared_4979_; uint8_t v_isSharedCheck_4983_; 
lean_dec_ref(v_b_4875_);
lean_dec_ref(v_a_4874_);
v_a_4976_ = lean_ctor_get(v___x_4888_, 0);
v_isSharedCheck_4983_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4983_ == 0)
{
v___x_4978_ = v___x_4888_;
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
else
{
lean_inc(v_a_4976_);
lean_dec(v___x_4888_);
v___x_4978_ = lean_box(0);
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
v_resetjp_4977_:
{
lean_object* v___x_4981_; 
if (v_isShared_4979_ == 0)
{
v___x_4981_ = v___x_4978_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v_a_4976_);
v___x_4981_ = v_reuseFailAlloc_4982_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
return v___x_4981_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4874_ = stack[0].m_obj;
lean_object* v_b_4875_ = stack[1].m_obj;
lean_object* v_a_4876_ = stack[2].m_obj;
lean_object* v_a_4877_ = stack[3].m_obj;
lean_object* v_a_4878_ = stack[4].m_obj;
lean_object* v_a_4879_ = stack[5].m_obj;
lean_object* v_a_4880_ = stack[6].m_obj;
lean_object* v_a_4881_ = stack[7].m_obj;
lean_object* v_a_4882_ = stack[8].m_obj;
lean_object* v_a_4883_ = stack[9].m_obj;
lean_object* v_a_4884_ = stack[10].m_obj;
lean_object* v_a_4885_ = stack[11].m_obj;
lean_object* v_a_4886_ = stack[12].m_obj;
lean_object* v_res_4984_;
v_res_4984_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_4874_, v_b_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
stack->m_obj
 = v_res_4984_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27___boxed(lean_object* v_a_4985_, lean_object* v_b_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_){
_start:
{
lean_object* v_res_4999_; 
v_res_4999_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_4985_, v_b_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_);
lean_dec(v_a_4997_);
lean_dec_ref(v_a_4996_);
lean_dec(v_a_4995_);
lean_dec_ref(v_a_4994_);
lean_dec(v_a_4993_);
lean_dec_ref(v_a_4992_);
lean_dec(v_a_4991_);
lean_dec_ref(v_a_4990_);
lean_dec(v_a_4989_);
lean_dec(v_a_4988_);
lean_dec(v_a_4987_);
return v_res_4999_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(lean_object* v_a_5000_, lean_object* v_b_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_){
_start:
{
lean_object* v___x_5014_; 
v___x_5014_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
if (lean_obj_tag(v___x_5014_) == 0)
{
lean_object* v_a_5015_; lean_object* v___x_5016_; 
v_a_5015_ = lean_ctor_get(v___x_5014_, 0);
lean_inc(v_a_5015_);
lean_dec_ref_known(v___x_5014_, 1);
lean_inc_ref(v_a_5000_);
v___x_5016_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5000_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
if (lean_obj_tag(v___x_5016_) == 0)
{
lean_object* v_a_5017_; lean_object* v_fst_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5094_; 
v_a_5017_ = lean_ctor_get(v___x_5016_, 0);
lean_inc(v_a_5017_);
lean_dec_ref_known(v___x_5016_, 1);
v_fst_5018_ = lean_ctor_get(v_a_5017_, 0);
v_isSharedCheck_5094_ = !lean_is_exclusive(v_a_5017_);
if (v_isSharedCheck_5094_ == 0)
{
lean_object* v_unused_5095_; 
v_unused_5095_ = lean_ctor_get(v_a_5017_, 1);
lean_dec(v_unused_5095_);
v___x_5020_ = v_a_5017_;
v_isShared_5021_ = v_isSharedCheck_5094_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_fst_5018_);
lean_dec(v_a_5017_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5094_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5022_; 
lean_inc_ref(v_b_5001_);
v___x_5022_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
if (lean_obj_tag(v___x_5022_) == 0)
{
lean_object* v_a_5023_; lean_object* v_fst_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5084_; 
v_a_5023_ = lean_ctor_get(v___x_5022_, 0);
lean_inc(v_a_5023_);
lean_dec_ref_known(v___x_5022_, 1);
v_fst_5024_ = lean_ctor_get(v_a_5023_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v_a_5023_);
if (v_isSharedCheck_5084_ == 0)
{
lean_object* v_unused_5085_; 
v_unused_5085_ = lean_ctor_get(v_a_5023_, 1);
lean_dec(v_unused_5085_);
v___x_5026_ = v_a_5023_;
v_isShared_5027_ = v_isSharedCheck_5084_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_fst_5024_);
lean_dec(v_a_5023_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5084_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v_id_5028_; lean_object* v_structId_5029_; uint8_t v___x_5030_; lean_object* v___x_5031_; 
v_id_5028_ = lean_ctor_get(v_a_5015_, 0);
lean_inc(v_id_5028_);
v_structId_5029_ = lean_ctor_get(v_a_5015_, 1);
lean_inc(v_structId_5029_);
lean_dec(v_a_5015_);
v___x_5030_ = 0;
v___x_5031_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5018_, v___x_5030_, v_structId_5029_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
if (lean_obj_tag(v___x_5031_) == 0)
{
lean_object* v_a_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5075_; 
v_a_5032_ = lean_ctor_get(v___x_5031_, 0);
v_isSharedCheck_5075_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5075_ == 0)
{
v___x_5034_ = v___x_5031_;
v_isShared_5035_ = v_isSharedCheck_5075_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_a_5032_);
lean_dec(v___x_5031_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5075_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
if (lean_obj_tag(v_a_5032_) == 1)
{
lean_object* v_val_5036_; lean_object* v___x_5037_; 
lean_del_object(v___x_5034_);
v_val_5036_ = lean_ctor_get(v_a_5032_, 0);
lean_inc(v_val_5036_);
lean_dec_ref_known(v_a_5032_, 1);
v___x_5037_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5024_, v___x_5030_, v_structId_5029_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
if (lean_obj_tag(v___x_5037_) == 0)
{
lean_object* v_a_5038_; lean_object* v___x_5040_; uint8_t v_isShared_5041_; uint8_t v_isSharedCheck_5062_; 
v_a_5038_ = lean_ctor_get(v___x_5037_, 0);
v_isSharedCheck_5062_ = !lean_is_exclusive(v___x_5037_);
if (v_isSharedCheck_5062_ == 0)
{
v___x_5040_ = v___x_5037_;
v_isShared_5041_ = v_isSharedCheck_5062_;
goto v_resetjp_5039_;
}
else
{
lean_inc(v_a_5038_);
lean_dec(v___x_5037_);
v___x_5040_ = lean_box(0);
v_isShared_5041_ = v_isSharedCheck_5062_;
goto v_resetjp_5039_;
}
v_resetjp_5039_:
{
if (lean_obj_tag(v_a_5038_) == 1)
{
lean_object* v_val_5042_; lean_object* v___x_5044_; 
v_val_5042_ = lean_ctor_get(v_a_5038_, 0);
lean_inc_n(v_val_5042_, 2);
lean_dec_ref_known(v_a_5038_, 1);
lean_inc(v_val_5036_);
if (v_isShared_5027_ == 0)
{
lean_ctor_set_tag(v___x_5026_, 3);
lean_ctor_set(v___x_5026_, 1, v_val_5042_);
lean_ctor_set(v___x_5026_, 0, v_val_5036_);
v___x_5044_ = v___x_5026_;
goto v_reusejp_5043_;
}
else
{
lean_object* v_reuseFailAlloc_5057_; 
v_reuseFailAlloc_5057_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5057_, 0, v_val_5036_);
lean_ctor_set(v_reuseFailAlloc_5057_, 1, v_val_5042_);
v___x_5044_ = v_reuseFailAlloc_5057_;
goto v_reusejp_5043_;
}
v_reusejp_5043_:
{
lean_object* v___x_5045_; lean_object* v___x_5046_; uint8_t v___x_5047_; 
v___x_5045_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5044_);
v___x_5046_ = lean_box(0);
v___x_5047_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_5045_, v___x_5046_);
if (v___x_5047_ == 0)
{
lean_object* v___x_5048_; lean_object* v___x_5050_; 
lean_del_object(v___x_5040_);
v___x_5048_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5048_, 0, v_a_5000_);
lean_ctor_set(v___x_5048_, 1, v_b_5001_);
lean_ctor_set(v___x_5048_, 2, v_id_5028_);
lean_ctor_set(v___x_5048_, 3, v_val_5036_);
lean_ctor_set(v___x_5048_, 4, v_val_5042_);
if (v_isShared_5021_ == 0)
{
lean_ctor_set(v___x_5020_, 1, v___x_5048_);
lean_ctor_set(v___x_5020_, 0, v___x_5045_);
v___x_5050_ = v___x_5020_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5052_; 
v_reuseFailAlloc_5052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5052_, 0, v___x_5045_);
lean_ctor_set(v_reuseFailAlloc_5052_, 1, v___x_5048_);
v___x_5050_ = v_reuseFailAlloc_5052_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
lean_object* v___x_5051_; 
v___x_5051_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_5050_, v_structId_5029_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
lean_dec(v_structId_5029_);
return v___x_5051_;
}
}
else
{
lean_object* v___x_5053_; lean_object* v___x_5055_; 
lean_dec(v___x_5045_);
lean_dec(v_val_5042_);
lean_dec(v_val_5036_);
lean_dec(v_structId_5029_);
lean_dec(v_id_5028_);
lean_del_object(v___x_5020_);
lean_dec_ref(v_b_5001_);
lean_dec_ref(v_a_5000_);
v___x_5053_ = lean_box(0);
if (v_isShared_5041_ == 0)
{
lean_ctor_set(v___x_5040_, 0, v___x_5053_);
v___x_5055_ = v___x_5040_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v___x_5053_);
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
lean_object* v___x_5058_; lean_object* v___x_5060_; 
lean_dec(v_a_5038_);
lean_dec(v_val_5036_);
lean_dec(v_structId_5029_);
lean_dec(v_id_5028_);
lean_del_object(v___x_5026_);
lean_del_object(v___x_5020_);
lean_dec_ref(v_b_5001_);
lean_dec_ref(v_a_5000_);
v___x_5058_ = lean_box(0);
if (v_isShared_5041_ == 0)
{
lean_ctor_set(v___x_5040_, 0, v___x_5058_);
v___x_5060_ = v___x_5040_;
goto v_reusejp_5059_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v___x_5058_);
v___x_5060_ = v_reuseFailAlloc_5061_;
goto v_reusejp_5059_;
}
v_reusejp_5059_:
{
return v___x_5060_;
}
}
}
}
else
{
lean_object* v_a_5063_; lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5070_; 
lean_dec(v_val_5036_);
lean_dec(v_structId_5029_);
lean_dec(v_id_5028_);
lean_del_object(v___x_5026_);
lean_del_object(v___x_5020_);
lean_dec_ref(v_b_5001_);
lean_dec_ref(v_a_5000_);
v_a_5063_ = lean_ctor_get(v___x_5037_, 0);
v_isSharedCheck_5070_ = !lean_is_exclusive(v___x_5037_);
if (v_isSharedCheck_5070_ == 0)
{
v___x_5065_ = v___x_5037_;
v_isShared_5066_ = v_isSharedCheck_5070_;
goto v_resetjp_5064_;
}
else
{
lean_inc(v_a_5063_);
lean_dec(v___x_5037_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5070_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
lean_object* v___x_5068_; 
if (v_isShared_5066_ == 0)
{
v___x_5068_ = v___x_5065_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5069_; 
v_reuseFailAlloc_5069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5069_, 0, v_a_5063_);
v___x_5068_ = v_reuseFailAlloc_5069_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
return v___x_5068_;
}
}
}
}
else
{
lean_object* v___x_5071_; lean_object* v___x_5073_; 
lean_dec(v_a_5032_);
lean_dec(v_structId_5029_);
lean_dec(v_id_5028_);
lean_del_object(v___x_5026_);
lean_dec(v_fst_5024_);
lean_del_object(v___x_5020_);
lean_dec_ref(v_b_5001_);
lean_dec_ref(v_a_5000_);
v___x_5071_ = lean_box(0);
if (v_isShared_5035_ == 0)
{
lean_ctor_set(v___x_5034_, 0, v___x_5071_);
v___x_5073_ = v___x_5034_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v___x_5071_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
return v___x_5073_;
}
}
}
}
else
{
lean_object* v_a_5076_; lean_object* v___x_5078_; uint8_t v_isShared_5079_; uint8_t v_isSharedCheck_5083_; 
lean_dec(v_structId_5029_);
lean_dec(v_id_5028_);
lean_del_object(v___x_5026_);
lean_dec(v_fst_5024_);
lean_del_object(v___x_5020_);
lean_dec_ref(v_b_5001_);
lean_dec_ref(v_a_5000_);
v_a_5076_ = lean_ctor_get(v___x_5031_, 0);
v_isSharedCheck_5083_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5083_ == 0)
{
v___x_5078_ = v___x_5031_;
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
else
{
lean_inc(v_a_5076_);
lean_dec(v___x_5031_);
v___x_5078_ = lean_box(0);
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
v_resetjp_5077_:
{
lean_object* v___x_5081_; 
if (v_isShared_5079_ == 0)
{
v___x_5081_ = v___x_5078_;
goto v_reusejp_5080_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v_a_5076_);
v___x_5081_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5080_;
}
v_reusejp_5080_:
{
return v___x_5081_;
}
}
}
}
}
else
{
lean_object* v_a_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5093_; 
lean_del_object(v___x_5020_);
lean_dec(v_fst_5018_);
lean_dec(v_a_5015_);
lean_dec_ref(v_b_5001_);
lean_dec_ref(v_a_5000_);
v_a_5086_ = lean_ctor_get(v___x_5022_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_5022_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5088_ = v___x_5022_;
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_a_5086_);
lean_dec(v___x_5022_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v___x_5091_; 
if (v_isShared_5089_ == 0)
{
v___x_5091_ = v___x_5088_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v_a_5086_);
v___x_5091_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
return v___x_5091_;
}
}
}
}
}
else
{
lean_object* v_a_5096_; lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5103_; 
lean_dec(v_a_5015_);
lean_dec_ref(v_b_5001_);
lean_dec_ref(v_a_5000_);
v_a_5096_ = lean_ctor_get(v___x_5016_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_5016_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5098_ = v___x_5016_;
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_a_5096_);
lean_dec(v___x_5016_);
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
lean_object* v_a_5104_; lean_object* v___x_5106_; uint8_t v_isShared_5107_; uint8_t v_isSharedCheck_5111_; 
lean_dec_ref(v_b_5001_);
lean_dec_ref(v_a_5000_);
v_a_5104_ = lean_ctor_get(v___x_5014_, 0);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_5014_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5106_ = v___x_5014_;
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
else
{
lean_inc(v_a_5104_);
lean_dec(v___x_5014_);
v___x_5106_ = lean_box(0);
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
v_resetjp_5105_:
{
lean_object* v___x_5109_; 
if (v_isShared_5107_ == 0)
{
v___x_5109_ = v___x_5106_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_a_5104_);
v___x_5109_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
return v___x_5109_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5000_ = stack[0].m_obj;
lean_object* v_b_5001_ = stack[1].m_obj;
lean_object* v_a_5002_ = stack[2].m_obj;
lean_object* v_a_5003_ = stack[3].m_obj;
lean_object* v_a_5004_ = stack[4].m_obj;
lean_object* v_a_5005_ = stack[5].m_obj;
lean_object* v_a_5006_ = stack[6].m_obj;
lean_object* v_a_5007_ = stack[7].m_obj;
lean_object* v_a_5008_ = stack[8].m_obj;
lean_object* v_a_5009_ = stack[9].m_obj;
lean_object* v_a_5010_ = stack[10].m_obj;
lean_object* v_a_5011_ = stack[11].m_obj;
lean_object* v_a_5012_ = stack[12].m_obj;
lean_object* v_res_5112_;
v_res_5112_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5000_, v_b_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
stack->m_obj
 = v_res_5112_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq___boxed(lean_object* v_a_5113_, lean_object* v_b_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_){
_start:
{
lean_object* v_res_5127_; 
v_res_5127_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5113_, v_b_5114_, v_a_5115_, v_a_5116_, v_a_5117_, v_a_5118_, v_a_5119_, v_a_5120_, v_a_5121_, v_a_5122_, v_a_5123_, v_a_5124_, v_a_5125_);
lean_dec(v_a_5125_);
lean_dec_ref(v_a_5124_);
lean_dec(v_a_5123_);
lean_dec_ref(v_a_5122_);
lean_dec(v_a_5121_);
lean_dec_ref(v_a_5120_);
lean_dec(v_a_5119_);
lean_dec_ref(v_a_5118_);
lean_dec(v_a_5117_);
lean_dec(v_a_5116_);
lean_dec(v_a_5115_);
return v_res_5127_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq(lean_object* v_a_5128_, lean_object* v_b_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_){
_start:
{
size_t v___x_5141_; size_t v___x_5142_; uint8_t v___x_5143_; 
v___x_5141_ = lean_ptr_addr(v_a_5128_);
v___x_5142_ = lean_ptr_addr(v_b_5129_);
v___x_5143_ = lean_usize_dec_eq(v___x_5141_, v___x_5142_);
if (v___x_5143_ == 0)
{
lean_object* v___x_5144_; 
v___x_5144_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5128_, v_b_5129_, v_a_5130_, v_a_5138_);
if (lean_obj_tag(v___x_5144_) == 0)
{
lean_object* v_a_5145_; 
v_a_5145_ = lean_ctor_get(v___x_5144_, 0);
lean_inc(v_a_5145_);
lean_dec_ref_known(v___x_5144_, 1);
if (lean_obj_tag(v_a_5145_) == 1)
{
lean_object* v_val_5146_; lean_object* v___x_5147_; 
v_val_5146_ = lean_ctor_get(v_a_5145_, 0);
lean_inc(v_val_5146_);
lean_dec_ref_known(v_a_5145_, 1);
v___x_5147_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_val_5146_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_);
if (lean_obj_tag(v___x_5147_) == 0)
{
lean_object* v_a_5148_; uint8_t v___x_5149_; 
v_a_5148_ = lean_ctor_get(v___x_5147_, 0);
lean_inc(v_a_5148_);
lean_dec_ref_known(v___x_5147_, 1);
v___x_5149_ = lean_unbox(v_a_5148_);
lean_dec(v_a_5148_);
if (v___x_5149_ == 0)
{
lean_object* v___x_5150_; 
v___x_5150_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5146_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_);
if (lean_obj_tag(v___x_5150_) == 0)
{
lean_object* v_a_5151_; uint8_t v___x_5152_; 
v_a_5151_ = lean_ctor_get(v___x_5150_, 0);
lean_inc(v_a_5151_);
lean_dec_ref_known(v___x_5150_, 1);
v___x_5152_ = lean_unbox(v_a_5151_);
lean_dec(v_a_5151_);
if (v___x_5152_ == 0)
{
lean_object* v___x_5153_; 
v___x_5153_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_5128_, v_b_5129_, v_val_5146_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_);
lean_dec(v_val_5146_);
return v___x_5153_;
}
else
{
lean_object* v___x_5154_; 
lean_dec(v_val_5146_);
v___x_5154_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_5128_, v_b_5129_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_);
return v___x_5154_;
}
}
else
{
lean_object* v_a_5155_; lean_object* v___x_5157_; uint8_t v_isShared_5158_; uint8_t v_isSharedCheck_5162_; 
lean_dec(v_val_5146_);
lean_dec_ref(v_b_5129_);
lean_dec_ref(v_a_5128_);
v_a_5155_ = lean_ctor_get(v___x_5150_, 0);
v_isSharedCheck_5162_ = !lean_is_exclusive(v___x_5150_);
if (v_isSharedCheck_5162_ == 0)
{
v___x_5157_ = v___x_5150_;
v_isShared_5158_ = v_isSharedCheck_5162_;
goto v_resetjp_5156_;
}
else
{
lean_inc(v_a_5155_);
lean_dec(v___x_5150_);
v___x_5157_ = lean_box(0);
v_isShared_5158_ = v_isSharedCheck_5162_;
goto v_resetjp_5156_;
}
v_resetjp_5156_:
{
lean_object* v___x_5160_; 
if (v_isShared_5158_ == 0)
{
v___x_5160_ = v___x_5157_;
goto v_reusejp_5159_;
}
else
{
lean_object* v_reuseFailAlloc_5161_; 
v_reuseFailAlloc_5161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5161_, 0, v_a_5155_);
v___x_5160_ = v_reuseFailAlloc_5161_;
goto v_reusejp_5159_;
}
v_reusejp_5159_:
{
return v___x_5160_;
}
}
}
}
else
{
lean_object* v___x_5163_; 
v___x_5163_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5146_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_);
if (lean_obj_tag(v___x_5163_) == 0)
{
lean_object* v_a_5164_; uint8_t v___x_5165_; 
v_a_5164_ = lean_ctor_get(v___x_5163_, 0);
lean_inc(v_a_5164_);
lean_dec_ref_known(v___x_5163_, 1);
v___x_5165_ = lean_unbox(v_a_5164_);
lean_dec(v_a_5164_);
if (v___x_5165_ == 0)
{
lean_object* v___x_5166_; 
v___x_5166_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_5128_, v_b_5129_, v_val_5146_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_);
lean_dec(v_val_5146_);
return v___x_5166_;
}
else
{
lean_object* v___x_5167_; 
v___x_5167_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_5128_, v_b_5129_, v_val_5146_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_);
lean_dec(v_val_5146_);
return v___x_5167_;
}
}
else
{
lean_object* v_a_5168_; lean_object* v___x_5170_; uint8_t v_isShared_5171_; uint8_t v_isSharedCheck_5175_; 
lean_dec(v_val_5146_);
lean_dec_ref(v_b_5129_);
lean_dec_ref(v_a_5128_);
v_a_5168_ = lean_ctor_get(v___x_5163_, 0);
v_isSharedCheck_5175_ = !lean_is_exclusive(v___x_5163_);
if (v_isSharedCheck_5175_ == 0)
{
v___x_5170_ = v___x_5163_;
v_isShared_5171_ = v_isSharedCheck_5175_;
goto v_resetjp_5169_;
}
else
{
lean_inc(v_a_5168_);
lean_dec(v___x_5163_);
v___x_5170_ = lean_box(0);
v_isShared_5171_ = v_isSharedCheck_5175_;
goto v_resetjp_5169_;
}
v_resetjp_5169_:
{
lean_object* v___x_5173_; 
if (v_isShared_5171_ == 0)
{
v___x_5173_ = v___x_5170_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v_a_5168_);
v___x_5173_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
return v___x_5173_;
}
}
}
}
}
else
{
lean_object* v_a_5176_; lean_object* v___x_5178_; uint8_t v_isShared_5179_; uint8_t v_isSharedCheck_5183_; 
lean_dec(v_val_5146_);
lean_dec_ref(v_b_5129_);
lean_dec_ref(v_a_5128_);
v_a_5176_ = lean_ctor_get(v___x_5147_, 0);
v_isSharedCheck_5183_ = !lean_is_exclusive(v___x_5147_);
if (v_isSharedCheck_5183_ == 0)
{
v___x_5178_ = v___x_5147_;
v_isShared_5179_ = v_isSharedCheck_5183_;
goto v_resetjp_5177_;
}
else
{
lean_inc(v_a_5176_);
lean_dec(v___x_5147_);
v___x_5178_ = lean_box(0);
v_isShared_5179_ = v_isSharedCheck_5183_;
goto v_resetjp_5177_;
}
v_resetjp_5177_:
{
lean_object* v___x_5181_; 
if (v_isShared_5179_ == 0)
{
v___x_5181_ = v___x_5178_;
goto v_reusejp_5180_;
}
else
{
lean_object* v_reuseFailAlloc_5182_; 
v_reuseFailAlloc_5182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5182_, 0, v_a_5176_);
v___x_5181_ = v_reuseFailAlloc_5182_;
goto v_reusejp_5180_;
}
v_reusejp_5180_:
{
return v___x_5181_;
}
}
}
}
else
{
lean_object* v___x_5184_; 
lean_dec(v_a_5145_);
v___x_5184_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5128_, v_b_5129_, v_a_5130_, v_a_5138_);
if (lean_obj_tag(v___x_5184_) == 0)
{
lean_object* v_a_5185_; lean_object* v___x_5187_; uint8_t v_isShared_5188_; uint8_t v_isSharedCheck_5207_; 
v_a_5185_ = lean_ctor_get(v___x_5184_, 0);
v_isSharedCheck_5207_ = !lean_is_exclusive(v___x_5184_);
if (v_isSharedCheck_5207_ == 0)
{
v___x_5187_ = v___x_5184_;
v_isShared_5188_ = v_isSharedCheck_5207_;
goto v_resetjp_5186_;
}
else
{
lean_inc(v_a_5185_);
lean_dec(v___x_5184_);
v___x_5187_ = lean_box(0);
v_isShared_5188_ = v_isSharedCheck_5207_;
goto v_resetjp_5186_;
}
v_resetjp_5186_:
{
if (lean_obj_tag(v_a_5185_) == 1)
{
lean_object* v_val_5189_; lean_object* v___x_5190_; 
lean_del_object(v___x_5187_);
v_val_5189_ = lean_ctor_get(v_a_5185_, 0);
lean_inc(v_val_5189_);
lean_dec_ref_known(v_a_5185_, 1);
v___x_5190_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_5189_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_);
if (lean_obj_tag(v___x_5190_) == 0)
{
lean_object* v_a_5191_; lean_object* v_orderedAddInst_x3f_5192_; 
v_a_5191_ = lean_ctor_get(v___x_5190_, 0);
lean_inc(v_a_5191_);
lean_dec_ref_known(v___x_5190_, 1);
v_orderedAddInst_x3f_5192_ = lean_ctor_get(v_a_5191_, 9);
lean_inc(v_orderedAddInst_x3f_5192_);
lean_dec(v_a_5191_);
if (lean_obj_tag(v_orderedAddInst_x3f_5192_) == 0)
{
lean_object* v___x_5193_; 
v___x_5193_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5128_, v_b_5129_, v_val_5189_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_);
lean_dec(v_val_5189_);
return v___x_5193_;
}
else
{
lean_object* v___x_5194_; 
lean_dec_ref_known(v_orderedAddInst_x3f_5192_, 1);
v___x_5194_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5128_, v_b_5129_, v_val_5189_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_);
lean_dec(v_val_5189_);
return v___x_5194_;
}
}
else
{
lean_object* v_a_5195_; lean_object* v___x_5197_; uint8_t v_isShared_5198_; uint8_t v_isSharedCheck_5202_; 
lean_dec(v_val_5189_);
lean_dec_ref(v_b_5129_);
lean_dec_ref(v_a_5128_);
v_a_5195_ = lean_ctor_get(v___x_5190_, 0);
v_isSharedCheck_5202_ = !lean_is_exclusive(v___x_5190_);
if (v_isSharedCheck_5202_ == 0)
{
v___x_5197_ = v___x_5190_;
v_isShared_5198_ = v_isSharedCheck_5202_;
goto v_resetjp_5196_;
}
else
{
lean_inc(v_a_5195_);
lean_dec(v___x_5190_);
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
else
{
lean_object* v___x_5203_; lean_object* v___x_5205_; 
lean_dec(v_a_5185_);
lean_dec_ref(v_b_5129_);
lean_dec_ref(v_a_5128_);
v___x_5203_ = lean_box(0);
if (v_isShared_5188_ == 0)
{
lean_ctor_set(v___x_5187_, 0, v___x_5203_);
v___x_5205_ = v___x_5187_;
goto v_reusejp_5204_;
}
else
{
lean_object* v_reuseFailAlloc_5206_; 
v_reuseFailAlloc_5206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5206_, 0, v___x_5203_);
v___x_5205_ = v_reuseFailAlloc_5206_;
goto v_reusejp_5204_;
}
v_reusejp_5204_:
{
return v___x_5205_;
}
}
}
}
else
{
lean_object* v_a_5208_; lean_object* v___x_5210_; uint8_t v_isShared_5211_; uint8_t v_isSharedCheck_5215_; 
lean_dec_ref(v_b_5129_);
lean_dec_ref(v_a_5128_);
v_a_5208_ = lean_ctor_get(v___x_5184_, 0);
v_isSharedCheck_5215_ = !lean_is_exclusive(v___x_5184_);
if (v_isSharedCheck_5215_ == 0)
{
v___x_5210_ = v___x_5184_;
v_isShared_5211_ = v_isSharedCheck_5215_;
goto v_resetjp_5209_;
}
else
{
lean_inc(v_a_5208_);
lean_dec(v___x_5184_);
v___x_5210_ = lean_box(0);
v_isShared_5211_ = v_isSharedCheck_5215_;
goto v_resetjp_5209_;
}
v_resetjp_5209_:
{
lean_object* v___x_5213_; 
if (v_isShared_5211_ == 0)
{
v___x_5213_ = v___x_5210_;
goto v_reusejp_5212_;
}
else
{
lean_object* v_reuseFailAlloc_5214_; 
v_reuseFailAlloc_5214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_a_5208_);
v___x_5213_ = v_reuseFailAlloc_5214_;
goto v_reusejp_5212_;
}
v_reusejp_5212_:
{
return v___x_5213_;
}
}
}
}
}
else
{
lean_object* v_a_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5223_; 
lean_dec_ref(v_b_5129_);
lean_dec_ref(v_a_5128_);
v_a_5216_ = lean_ctor_get(v___x_5144_, 0);
v_isSharedCheck_5223_ = !lean_is_exclusive(v___x_5144_);
if (v_isSharedCheck_5223_ == 0)
{
v___x_5218_ = v___x_5144_;
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_a_5216_);
lean_dec(v___x_5144_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v___x_5221_; 
if (v_isShared_5219_ == 0)
{
v___x_5221_ = v___x_5218_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5222_; 
v_reuseFailAlloc_5222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5222_, 0, v_a_5216_);
v___x_5221_ = v_reuseFailAlloc_5222_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
return v___x_5221_;
}
}
}
}
else
{
lean_object* v___x_5224_; lean_object* v___x_5225_; 
lean_dec_ref(v_b_5129_);
lean_dec_ref(v_a_5128_);
v___x_5224_ = lean_box(0);
v___x_5225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5225_, 0, v___x_5224_);
return v___x_5225_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_processNewEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5128_ = stack[0].m_obj;
lean_object* v_b_5129_ = stack[1].m_obj;
lean_object* v_a_5130_ = stack[2].m_obj;
lean_object* v_a_5131_ = stack[3].m_obj;
lean_object* v_a_5132_ = stack[4].m_obj;
lean_object* v_a_5133_ = stack[5].m_obj;
lean_object* v_a_5134_ = stack[6].m_obj;
lean_object* v_a_5135_ = stack[7].m_obj;
lean_object* v_a_5136_ = stack[8].m_obj;
lean_object* v_a_5137_ = stack[9].m_obj;
lean_object* v_a_5138_ = stack[10].m_obj;
lean_object* v_a_5139_ = stack[11].m_obj;
lean_object* v_res_5226_;
v_res_5226_ = l_Lean_Meta_Grind_Arith_Linear_processNewEq(v_a_5128_, v_b_5129_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_);
stack->m_obj
 = v_res_5226_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed(lean_object* v_a_5227_, lean_object* v_b_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_, lean_object* v_a_5235_, lean_object* v_a_5236_, lean_object* v_a_5237_, lean_object* v_a_5238_, lean_object* v_a_5239_){
_start:
{
lean_object* v_res_5240_; 
v_res_5240_ = l_Lean_Meta_Grind_Arith_Linear_processNewEq(v_a_5227_, v_b_5228_, v_a_5229_, v_a_5230_, v_a_5231_, v_a_5232_, v_a_5233_, v_a_5234_, v_a_5235_, v_a_5236_, v_a_5237_, v_a_5238_);
lean_dec(v_a_5238_);
lean_dec_ref(v_a_5237_);
lean_dec(v_a_5236_);
lean_dec_ref(v_a_5235_);
lean_dec(v_a_5234_);
lean_dec_ref(v_a_5233_);
lean_dec(v_a_5232_);
lean_dec_ref(v_a_5231_);
lean_dec(v_a_5230_);
lean_dec(v_a_5229_);
return v_res_5240_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object* v_a_5241_, lean_object* v_b_5242_, lean_object* v_a_5243_, lean_object* v_a_5244_, lean_object* v_a_5245_, lean_object* v_a_5246_, lean_object* v_a_5247_, lean_object* v_a_5248_, lean_object* v_a_5249_, lean_object* v_a_5250_, lean_object* v_a_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_){
_start:
{
uint8_t v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; 
v___x_5255_ = 0;
v___x_5256_ = lean_box(v___x_5255_);
lean_inc_ref(v_a_5241_);
v___x_5257_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 2);
lean_closure_set(v___x_5257_, 0, v_a_5241_);
lean_closure_set(v___x_5257_, 1, v___x_5256_);
v___x_5258_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5257_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_, v_a_5248_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_);
if (lean_obj_tag(v___x_5258_) == 0)
{
lean_object* v_a_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5360_; 
v_a_5259_ = lean_ctor_get(v___x_5258_, 0);
v_isSharedCheck_5360_ = !lean_is_exclusive(v___x_5258_);
if (v_isSharedCheck_5360_ == 0)
{
v___x_5261_ = v___x_5258_;
v_isShared_5262_ = v_isSharedCheck_5360_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_a_5259_);
lean_dec(v___x_5258_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5360_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
if (lean_obj_tag(v_a_5259_) == 1)
{
lean_object* v_val_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; 
lean_del_object(v___x_5261_);
v_val_5263_ = lean_ctor_get(v_a_5259_, 0);
lean_inc(v_val_5263_);
lean_dec_ref_known(v_a_5259_, 1);
v___x_5264_ = lean_box(v___x_5255_);
lean_inc_ref(v_b_5242_);
v___x_5265_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 2);
lean_closure_set(v___x_5265_, 0, v_b_5242_);
lean_closure_set(v___x_5265_, 1, v___x_5264_);
v___x_5266_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5265_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_, v_a_5248_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_);
if (lean_obj_tag(v___x_5266_) == 0)
{
lean_object* v_a_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5347_; 
v_a_5267_ = lean_ctor_get(v___x_5266_, 0);
v_isSharedCheck_5347_ = !lean_is_exclusive(v___x_5266_);
if (v_isSharedCheck_5347_ == 0)
{
v___x_5269_ = v___x_5266_;
v_isShared_5270_ = v_isSharedCheck_5347_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_a_5267_);
lean_dec(v___x_5266_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5347_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
if (lean_obj_tag(v_a_5267_) == 1)
{
lean_object* v_val_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; 
lean_del_object(v___x_5269_);
v_val_5271_ = lean_ctor_get(v_a_5267_, 0);
lean_inc_n(v_val_5271_, 2);
lean_dec_ref_known(v_a_5267_, 1);
lean_inc(v_val_5263_);
v___x_5272_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_5272_, 0, v_val_5263_);
lean_ctor_set(v___x_5272_, 1, v_val_5271_);
v___x_5273_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_5272_);
lean_inc_ref(v_b_5242_);
lean_inc_ref(v_a_5241_);
v___x_5274_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5274_, 0, v_a_5241_);
lean_ctor_set(v___x_5274_, 1, v_b_5242_);
lean_ctor_set(v___x_5274_, 2, v_val_5263_);
lean_ctor_set(v___x_5274_, 3, v_val_5271_);
v___x_5275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5275_, 0, v___x_5273_);
lean_ctor_set(v___x_5275_, 1, v___x_5274_);
v___x_5276_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(v___x_5275_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_, v_a_5248_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_);
if (lean_obj_tag(v___x_5276_) == 0)
{
lean_object* v_a_5277_; lean_object* v_p_5278_; lean_object* v___x_5279_; 
v_a_5277_ = lean_ctor_get(v___x_5276_, 0);
lean_inc(v_a_5277_);
lean_dec_ref_known(v___x_5276_, 1);
v_p_5278_ = lean_ctor_get(v_a_5277_, 0);
v___x_5279_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5241_, v_a_5244_);
lean_dec_ref(v_a_5241_);
if (lean_obj_tag(v___x_5279_) == 0)
{
lean_object* v_a_5280_; lean_object* v___x_5281_; 
v_a_5280_ = lean_ctor_get(v___x_5279_, 0);
lean_inc(v_a_5280_);
lean_dec_ref_known(v___x_5279_, 1);
v___x_5281_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5242_, v_a_5244_);
lean_dec_ref(v_b_5242_);
if (lean_obj_tag(v___x_5281_) == 0)
{
lean_object* v_a_5282_; lean_object* v___y_5284_; uint8_t v___x_5318_; 
v_a_5282_ = lean_ctor_get(v___x_5281_, 0);
lean_inc(v_a_5282_);
lean_dec_ref_known(v___x_5281_, 1);
v___x_5318_ = lean_nat_dec_le(v_a_5280_, v_a_5282_);
if (v___x_5318_ == 0)
{
lean_dec(v_a_5282_);
v___y_5284_ = v_a_5280_;
goto v___jp_5283_;
}
else
{
lean_dec(v_a_5280_);
v___y_5284_ = v_a_5282_;
goto v___jp_5283_;
}
v___jp_5283_:
{
lean_object* v___x_5285_; 
lean_inc_ref(v_p_5278_);
v___x_5285_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_5278_, v___y_5284_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_, v_a_5248_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_);
if (lean_obj_tag(v___x_5285_) == 0)
{
lean_object* v_a_5286_; lean_object* v___x_5287_; 
v_a_5286_ = lean_ctor_get(v___x_5285_, 0);
lean_inc(v_a_5286_);
lean_dec_ref_known(v___x_5285_, 1);
v___x_5287_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5286_, v___x_5255_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_, v_a_5248_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_);
if (lean_obj_tag(v___x_5287_) == 0)
{
lean_object* v_a_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5301_; 
v_a_5288_ = lean_ctor_get(v___x_5287_, 0);
v_isSharedCheck_5301_ = !lean_is_exclusive(v___x_5287_);
if (v_isSharedCheck_5301_ == 0)
{
v___x_5290_ = v___x_5287_;
v_isShared_5291_ = v_isSharedCheck_5301_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_a_5288_);
lean_dec(v___x_5287_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5301_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
if (lean_obj_tag(v_a_5288_) == 1)
{
lean_object* v_val_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; 
lean_del_object(v___x_5290_);
v_val_5292_ = lean_ctor_get(v_a_5288_, 0);
lean_inc_n(v_val_5292_, 2);
lean_dec_ref_known(v_a_5288_, 1);
v___x_5293_ = l_Lean_Grind_Linarith_Expr_norm(v_val_5292_);
v___x_5294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5294_, 0, v_a_5277_);
lean_ctor_set(v___x_5294_, 1, v_val_5292_);
v___x_5295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5295_, 0, v___x_5293_);
lean_ctor_set(v___x_5295_, 1, v___x_5294_);
v___x_5296_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5295_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_, v_a_5248_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_);
return v___x_5296_;
}
else
{
lean_object* v___x_5297_; lean_object* v___x_5299_; 
lean_dec(v_a_5288_);
lean_dec(v_a_5277_);
v___x_5297_ = lean_box(0);
if (v_isShared_5291_ == 0)
{
lean_ctor_set(v___x_5290_, 0, v___x_5297_);
v___x_5299_ = v___x_5290_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5300_; 
v_reuseFailAlloc_5300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5300_, 0, v___x_5297_);
v___x_5299_ = v_reuseFailAlloc_5300_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
return v___x_5299_;
}
}
}
}
else
{
lean_object* v_a_5302_; lean_object* v___x_5304_; uint8_t v_isShared_5305_; uint8_t v_isSharedCheck_5309_; 
lean_dec(v_a_5277_);
v_a_5302_ = lean_ctor_get(v___x_5287_, 0);
v_isSharedCheck_5309_ = !lean_is_exclusive(v___x_5287_);
if (v_isSharedCheck_5309_ == 0)
{
v___x_5304_ = v___x_5287_;
v_isShared_5305_ = v_isSharedCheck_5309_;
goto v_resetjp_5303_;
}
else
{
lean_inc(v_a_5302_);
lean_dec(v___x_5287_);
v___x_5304_ = lean_box(0);
v_isShared_5305_ = v_isSharedCheck_5309_;
goto v_resetjp_5303_;
}
v_resetjp_5303_:
{
lean_object* v___x_5307_; 
if (v_isShared_5305_ == 0)
{
v___x_5307_ = v___x_5304_;
goto v_reusejp_5306_;
}
else
{
lean_object* v_reuseFailAlloc_5308_; 
v_reuseFailAlloc_5308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5308_, 0, v_a_5302_);
v___x_5307_ = v_reuseFailAlloc_5308_;
goto v_reusejp_5306_;
}
v_reusejp_5306_:
{
return v___x_5307_;
}
}
}
}
else
{
lean_object* v_a_5310_; lean_object* v___x_5312_; uint8_t v_isShared_5313_; uint8_t v_isSharedCheck_5317_; 
lean_dec(v_a_5277_);
v_a_5310_ = lean_ctor_get(v___x_5285_, 0);
v_isSharedCheck_5317_ = !lean_is_exclusive(v___x_5285_);
if (v_isSharedCheck_5317_ == 0)
{
v___x_5312_ = v___x_5285_;
v_isShared_5313_ = v_isSharedCheck_5317_;
goto v_resetjp_5311_;
}
else
{
lean_inc(v_a_5310_);
lean_dec(v___x_5285_);
v___x_5312_ = lean_box(0);
v_isShared_5313_ = v_isSharedCheck_5317_;
goto v_resetjp_5311_;
}
v_resetjp_5311_:
{
lean_object* v___x_5315_; 
if (v_isShared_5313_ == 0)
{
v___x_5315_ = v___x_5312_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5316_; 
v_reuseFailAlloc_5316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5316_, 0, v_a_5310_);
v___x_5315_ = v_reuseFailAlloc_5316_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
return v___x_5315_;
}
}
}
}
}
else
{
lean_object* v_a_5319_; lean_object* v___x_5321_; uint8_t v_isShared_5322_; uint8_t v_isSharedCheck_5326_; 
lean_dec(v_a_5280_);
lean_dec(v_a_5277_);
v_a_5319_ = lean_ctor_get(v___x_5281_, 0);
v_isSharedCheck_5326_ = !lean_is_exclusive(v___x_5281_);
if (v_isSharedCheck_5326_ == 0)
{
v___x_5321_ = v___x_5281_;
v_isShared_5322_ = v_isSharedCheck_5326_;
goto v_resetjp_5320_;
}
else
{
lean_inc(v_a_5319_);
lean_dec(v___x_5281_);
v___x_5321_ = lean_box(0);
v_isShared_5322_ = v_isSharedCheck_5326_;
goto v_resetjp_5320_;
}
v_resetjp_5320_:
{
lean_object* v___x_5324_; 
if (v_isShared_5322_ == 0)
{
v___x_5324_ = v___x_5321_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5325_; 
v_reuseFailAlloc_5325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_a_5319_);
v___x_5324_ = v_reuseFailAlloc_5325_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
return v___x_5324_;
}
}
}
}
else
{
lean_object* v_a_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5334_; 
lean_dec(v_a_5277_);
lean_dec_ref(v_b_5242_);
v_a_5327_ = lean_ctor_get(v___x_5279_, 0);
v_isSharedCheck_5334_ = !lean_is_exclusive(v___x_5279_);
if (v_isSharedCheck_5334_ == 0)
{
v___x_5329_ = v___x_5279_;
v_isShared_5330_ = v_isSharedCheck_5334_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_a_5327_);
lean_dec(v___x_5279_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5334_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
lean_object* v___x_5332_; 
if (v_isShared_5330_ == 0)
{
v___x_5332_ = v___x_5329_;
goto v_reusejp_5331_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v_a_5327_);
v___x_5332_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5331_;
}
v_reusejp_5331_:
{
return v___x_5332_;
}
}
}
}
else
{
lean_object* v_a_5335_; lean_object* v___x_5337_; uint8_t v_isShared_5338_; uint8_t v_isSharedCheck_5342_; 
lean_dec_ref(v_b_5242_);
lean_dec_ref(v_a_5241_);
v_a_5335_ = lean_ctor_get(v___x_5276_, 0);
v_isSharedCheck_5342_ = !lean_is_exclusive(v___x_5276_);
if (v_isSharedCheck_5342_ == 0)
{
v___x_5337_ = v___x_5276_;
v_isShared_5338_ = v_isSharedCheck_5342_;
goto v_resetjp_5336_;
}
else
{
lean_inc(v_a_5335_);
lean_dec(v___x_5276_);
v___x_5337_ = lean_box(0);
v_isShared_5338_ = v_isSharedCheck_5342_;
goto v_resetjp_5336_;
}
v_resetjp_5336_:
{
lean_object* v___x_5340_; 
if (v_isShared_5338_ == 0)
{
v___x_5340_ = v___x_5337_;
goto v_reusejp_5339_;
}
else
{
lean_object* v_reuseFailAlloc_5341_; 
v_reuseFailAlloc_5341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5341_, 0, v_a_5335_);
v___x_5340_ = v_reuseFailAlloc_5341_;
goto v_reusejp_5339_;
}
v_reusejp_5339_:
{
return v___x_5340_;
}
}
}
}
else
{
lean_object* v___x_5343_; lean_object* v___x_5345_; 
lean_dec(v_a_5267_);
lean_dec(v_val_5263_);
lean_dec_ref(v_b_5242_);
lean_dec_ref(v_a_5241_);
v___x_5343_ = lean_box(0);
if (v_isShared_5270_ == 0)
{
lean_ctor_set(v___x_5269_, 0, v___x_5343_);
v___x_5345_ = v___x_5269_;
goto v_reusejp_5344_;
}
else
{
lean_object* v_reuseFailAlloc_5346_; 
v_reuseFailAlloc_5346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5346_, 0, v___x_5343_);
v___x_5345_ = v_reuseFailAlloc_5346_;
goto v_reusejp_5344_;
}
v_reusejp_5344_:
{
return v___x_5345_;
}
}
}
}
else
{
lean_object* v_a_5348_; lean_object* v___x_5350_; uint8_t v_isShared_5351_; uint8_t v_isSharedCheck_5355_; 
lean_dec(v_val_5263_);
lean_dec_ref(v_b_5242_);
lean_dec_ref(v_a_5241_);
v_a_5348_ = lean_ctor_get(v___x_5266_, 0);
v_isSharedCheck_5355_ = !lean_is_exclusive(v___x_5266_);
if (v_isSharedCheck_5355_ == 0)
{
v___x_5350_ = v___x_5266_;
v_isShared_5351_ = v_isSharedCheck_5355_;
goto v_resetjp_5349_;
}
else
{
lean_inc(v_a_5348_);
lean_dec(v___x_5266_);
v___x_5350_ = lean_box(0);
v_isShared_5351_ = v_isSharedCheck_5355_;
goto v_resetjp_5349_;
}
v_resetjp_5349_:
{
lean_object* v___x_5353_; 
if (v_isShared_5351_ == 0)
{
v___x_5353_ = v___x_5350_;
goto v_reusejp_5352_;
}
else
{
lean_object* v_reuseFailAlloc_5354_; 
v_reuseFailAlloc_5354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5354_, 0, v_a_5348_);
v___x_5353_ = v_reuseFailAlloc_5354_;
goto v_reusejp_5352_;
}
v_reusejp_5352_:
{
return v___x_5353_;
}
}
}
}
else
{
lean_object* v___x_5356_; lean_object* v___x_5358_; 
lean_dec(v_a_5259_);
lean_dec_ref(v_b_5242_);
lean_dec_ref(v_a_5241_);
v___x_5356_ = lean_box(0);
if (v_isShared_5262_ == 0)
{
lean_ctor_set(v___x_5261_, 0, v___x_5356_);
v___x_5358_ = v___x_5261_;
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
lean_dec_ref(v_b_5242_);
lean_dec_ref(v_a_5241_);
v_a_5361_ = lean_ctor_get(v___x_5258_, 0);
v_isSharedCheck_5368_ = !lean_is_exclusive(v___x_5258_);
if (v_isSharedCheck_5368_ == 0)
{
v___x_5363_ = v___x_5258_;
v_isShared_5364_ = v_isSharedCheck_5368_;
goto v_resetjp_5362_;
}
else
{
lean_inc(v_a_5361_);
lean_dec(v___x_5258_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5241_ = stack[0].m_obj;
lean_object* v_b_5242_ = stack[1].m_obj;
lean_object* v_a_5243_ = stack[2].m_obj;
lean_object* v_a_5244_ = stack[3].m_obj;
lean_object* v_a_5245_ = stack[4].m_obj;
lean_object* v_a_5246_ = stack[5].m_obj;
lean_object* v_a_5247_ = stack[6].m_obj;
lean_object* v_a_5248_ = stack[7].m_obj;
lean_object* v_a_5249_ = stack[8].m_obj;
lean_object* v_a_5250_ = stack[9].m_obj;
lean_object* v_a_5251_ = stack[10].m_obj;
lean_object* v_a_5252_ = stack[11].m_obj;
lean_object* v_a_5253_ = stack[12].m_obj;
lean_object* v_res_5369_;
v_res_5369_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5241_, v_b_5242_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_, v_a_5248_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_);
stack->m_obj
 = v_res_5369_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq___boxed(lean_object* v_a_5370_, lean_object* v_b_5371_, lean_object* v_a_5372_, lean_object* v_a_5373_, lean_object* v_a_5374_, lean_object* v_a_5375_, lean_object* v_a_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_, lean_object* v_a_5381_, lean_object* v_a_5382_, lean_object* v_a_5383_){
_start:
{
lean_object* v_res_5384_; 
v_res_5384_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5370_, v_b_5371_, v_a_5372_, v_a_5373_, v_a_5374_, v_a_5375_, v_a_5376_, v_a_5377_, v_a_5378_, v_a_5379_, v_a_5380_, v_a_5381_, v_a_5382_);
lean_dec(v_a_5382_);
lean_dec_ref(v_a_5381_);
lean_dec(v_a_5380_);
lean_dec_ref(v_a_5379_);
lean_dec(v_a_5378_);
lean_dec_ref(v_a_5377_);
lean_dec(v_a_5376_);
lean_dec_ref(v_a_5375_);
lean_dec(v_a_5374_);
lean_dec(v_a_5373_);
lean_dec(v_a_5372_);
return v_res_5384_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(lean_object* v_a_5385_, lean_object* v_b_5386_, lean_object* v_a_5387_, lean_object* v_a_5388_, lean_object* v_a_5389_, lean_object* v_a_5390_, lean_object* v_a_5391_, lean_object* v_a_5392_, lean_object* v_a_5393_, lean_object* v_a_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_){
_start:
{
uint8_t v___x_5399_; lean_object* v___x_5400_; 
v___x_5399_ = 0;
lean_inc_ref(v_a_5385_);
v___x_5400_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5385_, v___x_5399_, v_a_5387_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_, v_a_5392_, v_a_5393_, v_a_5394_, v_a_5395_, v_a_5396_, v_a_5397_);
if (lean_obj_tag(v___x_5400_) == 0)
{
lean_object* v_a_5401_; lean_object* v___x_5403_; uint8_t v_isShared_5404_; uint8_t v_isSharedCheck_5434_; 
v_a_5401_ = lean_ctor_get(v___x_5400_, 0);
v_isSharedCheck_5434_ = !lean_is_exclusive(v___x_5400_);
if (v_isSharedCheck_5434_ == 0)
{
v___x_5403_ = v___x_5400_;
v_isShared_5404_ = v_isSharedCheck_5434_;
goto v_resetjp_5402_;
}
else
{
lean_inc(v_a_5401_);
lean_dec(v___x_5400_);
v___x_5403_ = lean_box(0);
v_isShared_5404_ = v_isSharedCheck_5434_;
goto v_resetjp_5402_;
}
v_resetjp_5402_:
{
if (lean_obj_tag(v_a_5401_) == 1)
{
lean_object* v_val_5405_; lean_object* v___x_5406_; 
lean_del_object(v___x_5403_);
v_val_5405_ = lean_ctor_get(v_a_5401_, 0);
lean_inc(v_val_5405_);
lean_dec_ref_known(v_a_5401_, 1);
lean_inc_ref(v_b_5386_);
v___x_5406_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_5386_, v___x_5399_, v_a_5387_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_, v_a_5392_, v_a_5393_, v_a_5394_, v_a_5395_, v_a_5396_, v_a_5397_);
if (lean_obj_tag(v___x_5406_) == 0)
{
lean_object* v_a_5407_; lean_object* v___x_5409_; uint8_t v_isShared_5410_; uint8_t v_isSharedCheck_5421_; 
v_a_5407_ = lean_ctor_get(v___x_5406_, 0);
v_isSharedCheck_5421_ = !lean_is_exclusive(v___x_5406_);
if (v_isSharedCheck_5421_ == 0)
{
v___x_5409_ = v___x_5406_;
v_isShared_5410_ = v_isSharedCheck_5421_;
goto v_resetjp_5408_;
}
else
{
lean_inc(v_a_5407_);
lean_dec(v___x_5406_);
v___x_5409_ = lean_box(0);
v_isShared_5410_ = v_isSharedCheck_5421_;
goto v_resetjp_5408_;
}
v_resetjp_5408_:
{
if (lean_obj_tag(v_a_5407_) == 1)
{
lean_object* v_val_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; 
lean_del_object(v___x_5409_);
v_val_5411_ = lean_ctor_get(v_a_5407_, 0);
lean_inc_n(v_val_5411_, 2);
lean_dec_ref_known(v_a_5407_, 1);
lean_inc(v_val_5405_);
v___x_5412_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5412_, 0, v_val_5405_);
lean_ctor_set(v___x_5412_, 1, v_val_5411_);
v___x_5413_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5412_);
v___x_5414_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5414_, 0, v_a_5385_);
lean_ctor_set(v___x_5414_, 1, v_b_5386_);
lean_ctor_set(v___x_5414_, 2, v_val_5405_);
lean_ctor_set(v___x_5414_, 3, v_val_5411_);
v___x_5415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5415_, 0, v___x_5413_);
lean_ctor_set(v___x_5415_, 1, v___x_5414_);
v___x_5416_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5415_, v_a_5387_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_, v_a_5392_, v_a_5393_, v_a_5394_, v_a_5395_, v_a_5396_, v_a_5397_);
return v___x_5416_;
}
else
{
lean_object* v___x_5417_; lean_object* v___x_5419_; 
lean_dec(v_a_5407_);
lean_dec(v_val_5405_);
lean_dec_ref(v_b_5386_);
lean_dec_ref(v_a_5385_);
v___x_5417_ = lean_box(0);
if (v_isShared_5410_ == 0)
{
lean_ctor_set(v___x_5409_, 0, v___x_5417_);
v___x_5419_ = v___x_5409_;
goto v_reusejp_5418_;
}
else
{
lean_object* v_reuseFailAlloc_5420_; 
v_reuseFailAlloc_5420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5420_, 0, v___x_5417_);
v___x_5419_ = v_reuseFailAlloc_5420_;
goto v_reusejp_5418_;
}
v_reusejp_5418_:
{
return v___x_5419_;
}
}
}
}
else
{
lean_object* v_a_5422_; lean_object* v___x_5424_; uint8_t v_isShared_5425_; uint8_t v_isSharedCheck_5429_; 
lean_dec(v_val_5405_);
lean_dec_ref(v_b_5386_);
lean_dec_ref(v_a_5385_);
v_a_5422_ = lean_ctor_get(v___x_5406_, 0);
v_isSharedCheck_5429_ = !lean_is_exclusive(v___x_5406_);
if (v_isSharedCheck_5429_ == 0)
{
v___x_5424_ = v___x_5406_;
v_isShared_5425_ = v_isSharedCheck_5429_;
goto v_resetjp_5423_;
}
else
{
lean_inc(v_a_5422_);
lean_dec(v___x_5406_);
v___x_5424_ = lean_box(0);
v_isShared_5425_ = v_isSharedCheck_5429_;
goto v_resetjp_5423_;
}
v_resetjp_5423_:
{
lean_object* v___x_5427_; 
if (v_isShared_5425_ == 0)
{
v___x_5427_ = v___x_5424_;
goto v_reusejp_5426_;
}
else
{
lean_object* v_reuseFailAlloc_5428_; 
v_reuseFailAlloc_5428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5428_, 0, v_a_5422_);
v___x_5427_ = v_reuseFailAlloc_5428_;
goto v_reusejp_5426_;
}
v_reusejp_5426_:
{
return v___x_5427_;
}
}
}
}
else
{
lean_object* v___x_5430_; lean_object* v___x_5432_; 
lean_dec(v_a_5401_);
lean_dec_ref(v_b_5386_);
lean_dec_ref(v_a_5385_);
v___x_5430_ = lean_box(0);
if (v_isShared_5404_ == 0)
{
lean_ctor_set(v___x_5403_, 0, v___x_5430_);
v___x_5432_ = v___x_5403_;
goto v_reusejp_5431_;
}
else
{
lean_object* v_reuseFailAlloc_5433_; 
v_reuseFailAlloc_5433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5433_, 0, v___x_5430_);
v___x_5432_ = v_reuseFailAlloc_5433_;
goto v_reusejp_5431_;
}
v_reusejp_5431_:
{
return v___x_5432_;
}
}
}
}
else
{
lean_object* v_a_5435_; lean_object* v___x_5437_; uint8_t v_isShared_5438_; uint8_t v_isSharedCheck_5442_; 
lean_dec_ref(v_b_5386_);
lean_dec_ref(v_a_5385_);
v_a_5435_ = lean_ctor_get(v___x_5400_, 0);
v_isSharedCheck_5442_ = !lean_is_exclusive(v___x_5400_);
if (v_isSharedCheck_5442_ == 0)
{
v___x_5437_ = v___x_5400_;
v_isShared_5438_ = v_isSharedCheck_5442_;
goto v_resetjp_5436_;
}
else
{
lean_inc(v_a_5435_);
lean_dec(v___x_5400_);
v___x_5437_ = lean_box(0);
v_isShared_5438_ = v_isSharedCheck_5442_;
goto v_resetjp_5436_;
}
v_resetjp_5436_:
{
lean_object* v___x_5440_; 
if (v_isShared_5438_ == 0)
{
v___x_5440_ = v___x_5437_;
goto v_reusejp_5439_;
}
else
{
lean_object* v_reuseFailAlloc_5441_; 
v_reuseFailAlloc_5441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5441_, 0, v_a_5435_);
v___x_5440_ = v_reuseFailAlloc_5441_;
goto v_reusejp_5439_;
}
v_reusejp_5439_:
{
return v___x_5440_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5385_ = stack[0].m_obj;
lean_object* v_b_5386_ = stack[1].m_obj;
lean_object* v_a_5387_ = stack[2].m_obj;
lean_object* v_a_5388_ = stack[3].m_obj;
lean_object* v_a_5389_ = stack[4].m_obj;
lean_object* v_a_5390_ = stack[5].m_obj;
lean_object* v_a_5391_ = stack[6].m_obj;
lean_object* v_a_5392_ = stack[7].m_obj;
lean_object* v_a_5393_ = stack[8].m_obj;
lean_object* v_a_5394_ = stack[9].m_obj;
lean_object* v_a_5395_ = stack[10].m_obj;
lean_object* v_a_5396_ = stack[11].m_obj;
lean_object* v_a_5397_ = stack[12].m_obj;
lean_object* v_res_5443_;
v_res_5443_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5385_, v_b_5386_, v_a_5387_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_, v_a_5392_, v_a_5393_, v_a_5394_, v_a_5395_, v_a_5396_, v_a_5397_);
stack->m_obj
 = v_res_5443_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq___boxed(lean_object* v_a_5444_, lean_object* v_b_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_, lean_object* v_a_5452_, lean_object* v_a_5453_, lean_object* v_a_5454_, lean_object* v_a_5455_, lean_object* v_a_5456_, lean_object* v_a_5457_){
_start:
{
lean_object* v_res_5458_; 
v_res_5458_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5444_, v_b_5445_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_, v_a_5450_, v_a_5451_, v_a_5452_, v_a_5453_, v_a_5454_, v_a_5455_, v_a_5456_);
lean_dec(v_a_5456_);
lean_dec_ref(v_a_5455_);
lean_dec(v_a_5454_);
lean_dec_ref(v_a_5453_);
lean_dec(v_a_5452_);
lean_dec_ref(v_a_5451_);
lean_dec(v_a_5450_);
lean_dec_ref(v_a_5449_);
lean_dec(v_a_5448_);
lean_dec(v_a_5447_);
lean_dec(v_a_5446_);
return v_res_5458_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(lean_object* v_a_5459_, lean_object* v_b_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_, lean_object* v_a_5469_, lean_object* v_a_5470_, lean_object* v_a_5471_){
_start:
{
lean_object* v___x_5473_; 
v___x_5473_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5461_, v_a_5462_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_);
if (lean_obj_tag(v___x_5473_) == 0)
{
lean_object* v_a_5474_; lean_object* v_addRightCancelInst_x3f_5475_; 
v_a_5474_ = lean_ctor_get(v___x_5473_, 0);
lean_inc(v_a_5474_);
lean_dec_ref_known(v___x_5473_, 1);
v_addRightCancelInst_x3f_5475_ = lean_ctor_get(v_a_5474_, 11);
if (lean_obj_tag(v_addRightCancelInst_x3f_5475_) == 0)
{
lean_object* v___x_5476_; 
lean_dec(v_a_5474_);
v___x_5476_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(v_a_5459_, v_b_5460_, v_a_5461_, v_a_5462_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_);
return v___x_5476_;
}
else
{
lean_object* v_id_5477_; lean_object* v_structId_5478_; lean_object* v___x_5479_; 
v_id_5477_ = lean_ctor_get(v_a_5474_, 0);
lean_inc(v_id_5477_);
v_structId_5478_ = lean_ctor_get(v_a_5474_, 1);
lean_inc(v_structId_5478_);
lean_dec(v_a_5474_);
lean_inc_ref(v_a_5459_);
v___x_5479_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5459_, v_a_5461_, v_a_5462_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_);
if (lean_obj_tag(v___x_5479_) == 0)
{
lean_object* v_a_5480_; lean_object* v_fst_5481_; lean_object* v___x_5483_; uint8_t v_isShared_5484_; uint8_t v_isSharedCheck_5549_; 
v_a_5480_ = lean_ctor_get(v___x_5479_, 0);
lean_inc(v_a_5480_);
lean_dec_ref_known(v___x_5479_, 1);
v_fst_5481_ = lean_ctor_get(v_a_5480_, 0);
v_isSharedCheck_5549_ = !lean_is_exclusive(v_a_5480_);
if (v_isSharedCheck_5549_ == 0)
{
lean_object* v_unused_5550_; 
v_unused_5550_ = lean_ctor_get(v_a_5480_, 1);
lean_dec(v_unused_5550_);
v___x_5483_ = v_a_5480_;
v_isShared_5484_ = v_isSharedCheck_5549_;
goto v_resetjp_5482_;
}
else
{
lean_inc(v_fst_5481_);
lean_dec(v_a_5480_);
v___x_5483_ = lean_box(0);
v_isShared_5484_ = v_isSharedCheck_5549_;
goto v_resetjp_5482_;
}
v_resetjp_5482_:
{
lean_object* v___x_5485_; 
lean_inc_ref(v_b_5460_);
v___x_5485_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5460_, v_a_5461_, v_a_5462_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_);
if (lean_obj_tag(v___x_5485_) == 0)
{
lean_object* v_a_5486_; lean_object* v_fst_5487_; lean_object* v___x_5489_; uint8_t v_isShared_5490_; uint8_t v_isSharedCheck_5539_; 
v_a_5486_ = lean_ctor_get(v___x_5485_, 0);
lean_inc(v_a_5486_);
lean_dec_ref_known(v___x_5485_, 1);
v_fst_5487_ = lean_ctor_get(v_a_5486_, 0);
v_isSharedCheck_5539_ = !lean_is_exclusive(v_a_5486_);
if (v_isSharedCheck_5539_ == 0)
{
lean_object* v_unused_5540_; 
v_unused_5540_ = lean_ctor_get(v_a_5486_, 1);
lean_dec(v_unused_5540_);
v___x_5489_ = v_a_5486_;
v_isShared_5490_ = v_isSharedCheck_5539_;
goto v_resetjp_5488_;
}
else
{
lean_inc(v_fst_5487_);
lean_dec(v_a_5486_);
v___x_5489_ = lean_box(0);
v_isShared_5490_ = v_isSharedCheck_5539_;
goto v_resetjp_5488_;
}
v_resetjp_5488_:
{
uint8_t v___x_5491_; lean_object* v___x_5492_; 
v___x_5491_ = 0;
v___x_5492_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5481_, v___x_5491_, v_structId_5478_, v_a_5462_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_);
if (lean_obj_tag(v___x_5492_) == 0)
{
lean_object* v_a_5493_; lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5530_; 
v_a_5493_ = lean_ctor_get(v___x_5492_, 0);
v_isSharedCheck_5530_ = !lean_is_exclusive(v___x_5492_);
if (v_isSharedCheck_5530_ == 0)
{
v___x_5495_ = v___x_5492_;
v_isShared_5496_ = v_isSharedCheck_5530_;
goto v_resetjp_5494_;
}
else
{
lean_inc(v_a_5493_);
lean_dec(v___x_5492_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5530_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
if (lean_obj_tag(v_a_5493_) == 1)
{
lean_object* v_val_5497_; lean_object* v___x_5498_; 
lean_del_object(v___x_5495_);
v_val_5497_ = lean_ctor_get(v_a_5493_, 0);
lean_inc(v_val_5497_);
lean_dec_ref_known(v_a_5493_, 1);
v___x_5498_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5487_, v___x_5491_, v_structId_5478_, v_a_5462_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_);
if (lean_obj_tag(v___x_5498_) == 0)
{
lean_object* v_a_5499_; lean_object* v___x_5501_; uint8_t v_isShared_5502_; uint8_t v_isSharedCheck_5517_; 
v_a_5499_ = lean_ctor_get(v___x_5498_, 0);
v_isSharedCheck_5517_ = !lean_is_exclusive(v___x_5498_);
if (v_isSharedCheck_5517_ == 0)
{
v___x_5501_ = v___x_5498_;
v_isShared_5502_ = v_isSharedCheck_5517_;
goto v_resetjp_5500_;
}
else
{
lean_inc(v_a_5499_);
lean_dec(v___x_5498_);
v___x_5501_ = lean_box(0);
v_isShared_5502_ = v_isSharedCheck_5517_;
goto v_resetjp_5500_;
}
v_resetjp_5500_:
{
if (lean_obj_tag(v_a_5499_) == 1)
{
lean_object* v_val_5503_; lean_object* v___x_5505_; 
lean_del_object(v___x_5501_);
v_val_5503_ = lean_ctor_get(v_a_5499_, 0);
lean_inc_n(v_val_5503_, 2);
lean_dec_ref_known(v_a_5499_, 1);
lean_inc(v_val_5497_);
if (v_isShared_5490_ == 0)
{
lean_ctor_set_tag(v___x_5489_, 3);
lean_ctor_set(v___x_5489_, 1, v_val_5503_);
lean_ctor_set(v___x_5489_, 0, v_val_5497_);
v___x_5505_ = v___x_5489_;
goto v_reusejp_5504_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v_val_5497_);
lean_ctor_set(v_reuseFailAlloc_5512_, 1, v_val_5503_);
v___x_5505_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5504_;
}
v_reusejp_5504_:
{
lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5509_; 
v___x_5506_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5505_);
v___x_5507_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5507_, 0, v_a_5459_);
lean_ctor_set(v___x_5507_, 1, v_b_5460_);
lean_ctor_set(v___x_5507_, 2, v_id_5477_);
lean_ctor_set(v___x_5507_, 3, v_val_5497_);
lean_ctor_set(v___x_5507_, 4, v_val_5503_);
if (v_isShared_5484_ == 0)
{
lean_ctor_set(v___x_5483_, 1, v___x_5507_);
lean_ctor_set(v___x_5483_, 0, v___x_5506_);
v___x_5509_ = v___x_5483_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5511_; 
v_reuseFailAlloc_5511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5511_, 0, v___x_5506_);
lean_ctor_set(v_reuseFailAlloc_5511_, 1, v___x_5507_);
v___x_5509_ = v_reuseFailAlloc_5511_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
lean_object* v___x_5510_; 
v___x_5510_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5509_, v_structId_5478_, v_a_5462_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_);
lean_dec(v_structId_5478_);
return v___x_5510_;
}
}
}
else
{
lean_object* v___x_5513_; lean_object* v___x_5515_; 
lean_dec(v_a_5499_);
lean_dec(v_val_5497_);
lean_del_object(v___x_5489_);
lean_del_object(v___x_5483_);
lean_dec(v_structId_5478_);
lean_dec(v_id_5477_);
lean_dec_ref(v_b_5460_);
lean_dec_ref(v_a_5459_);
v___x_5513_ = lean_box(0);
if (v_isShared_5502_ == 0)
{
lean_ctor_set(v___x_5501_, 0, v___x_5513_);
v___x_5515_ = v___x_5501_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v___x_5513_);
v___x_5515_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
return v___x_5515_;
}
}
}
}
else
{
lean_object* v_a_5518_; lean_object* v___x_5520_; uint8_t v_isShared_5521_; uint8_t v_isSharedCheck_5525_; 
lean_dec(v_val_5497_);
lean_del_object(v___x_5489_);
lean_del_object(v___x_5483_);
lean_dec(v_structId_5478_);
lean_dec(v_id_5477_);
lean_dec_ref(v_b_5460_);
lean_dec_ref(v_a_5459_);
v_a_5518_ = lean_ctor_get(v___x_5498_, 0);
v_isSharedCheck_5525_ = !lean_is_exclusive(v___x_5498_);
if (v_isSharedCheck_5525_ == 0)
{
v___x_5520_ = v___x_5498_;
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
else
{
lean_inc(v_a_5518_);
lean_dec(v___x_5498_);
v___x_5520_ = lean_box(0);
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
v_resetjp_5519_:
{
lean_object* v___x_5523_; 
if (v_isShared_5521_ == 0)
{
v___x_5523_ = v___x_5520_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v_a_5518_);
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
lean_object* v___x_5526_; lean_object* v___x_5528_; 
lean_dec(v_a_5493_);
lean_del_object(v___x_5489_);
lean_dec(v_fst_5487_);
lean_del_object(v___x_5483_);
lean_dec(v_structId_5478_);
lean_dec(v_id_5477_);
lean_dec_ref(v_b_5460_);
lean_dec_ref(v_a_5459_);
v___x_5526_ = lean_box(0);
if (v_isShared_5496_ == 0)
{
lean_ctor_set(v___x_5495_, 0, v___x_5526_);
v___x_5528_ = v___x_5495_;
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
lean_del_object(v___x_5489_);
lean_dec(v_fst_5487_);
lean_del_object(v___x_5483_);
lean_dec(v_structId_5478_);
lean_dec(v_id_5477_);
lean_dec_ref(v_b_5460_);
lean_dec_ref(v_a_5459_);
v_a_5531_ = lean_ctor_get(v___x_5492_, 0);
v_isSharedCheck_5538_ = !lean_is_exclusive(v___x_5492_);
if (v_isSharedCheck_5538_ == 0)
{
v___x_5533_ = v___x_5492_;
v_isShared_5534_ = v_isSharedCheck_5538_;
goto v_resetjp_5532_;
}
else
{
lean_inc(v_a_5531_);
lean_dec(v___x_5492_);
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
}
else
{
lean_object* v_a_5541_; lean_object* v___x_5543_; uint8_t v_isShared_5544_; uint8_t v_isSharedCheck_5548_; 
lean_del_object(v___x_5483_);
lean_dec(v_fst_5481_);
lean_dec(v_structId_5478_);
lean_dec(v_id_5477_);
lean_dec_ref(v_b_5460_);
lean_dec_ref(v_a_5459_);
v_a_5541_ = lean_ctor_get(v___x_5485_, 0);
v_isSharedCheck_5548_ = !lean_is_exclusive(v___x_5485_);
if (v_isSharedCheck_5548_ == 0)
{
v___x_5543_ = v___x_5485_;
v_isShared_5544_ = v_isSharedCheck_5548_;
goto v_resetjp_5542_;
}
else
{
lean_inc(v_a_5541_);
lean_dec(v___x_5485_);
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
}
else
{
lean_object* v_a_5551_; lean_object* v___x_5553_; uint8_t v_isShared_5554_; uint8_t v_isSharedCheck_5558_; 
lean_dec(v_structId_5478_);
lean_dec(v_id_5477_);
lean_dec_ref(v_b_5460_);
lean_dec_ref(v_a_5459_);
v_a_5551_ = lean_ctor_get(v___x_5479_, 0);
v_isSharedCheck_5558_ = !lean_is_exclusive(v___x_5479_);
if (v_isSharedCheck_5558_ == 0)
{
v___x_5553_ = v___x_5479_;
v_isShared_5554_ = v_isSharedCheck_5558_;
goto v_resetjp_5552_;
}
else
{
lean_inc(v_a_5551_);
lean_dec(v___x_5479_);
v___x_5553_ = lean_box(0);
v_isShared_5554_ = v_isSharedCheck_5558_;
goto v_resetjp_5552_;
}
v_resetjp_5552_:
{
lean_object* v___x_5556_; 
if (v_isShared_5554_ == 0)
{
v___x_5556_ = v___x_5553_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v_a_5551_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
return v___x_5556_;
}
}
}
}
}
else
{
lean_object* v_a_5559_; lean_object* v___x_5561_; uint8_t v_isShared_5562_; uint8_t v_isSharedCheck_5566_; 
lean_dec_ref(v_b_5460_);
lean_dec_ref(v_a_5459_);
v_a_5559_ = lean_ctor_get(v___x_5473_, 0);
v_isSharedCheck_5566_ = !lean_is_exclusive(v___x_5473_);
if (v_isSharedCheck_5566_ == 0)
{
v___x_5561_ = v___x_5473_;
v_isShared_5562_ = v_isSharedCheck_5566_;
goto v_resetjp_5560_;
}
else
{
lean_inc(v_a_5559_);
lean_dec(v___x_5473_);
v___x_5561_ = lean_box(0);
v_isShared_5562_ = v_isSharedCheck_5566_;
goto v_resetjp_5560_;
}
v_resetjp_5560_:
{
lean_object* v___x_5564_; 
if (v_isShared_5562_ == 0)
{
v___x_5564_ = v___x_5561_;
goto v_reusejp_5563_;
}
else
{
lean_object* v_reuseFailAlloc_5565_; 
v_reuseFailAlloc_5565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_a_5559_);
v___x_5564_ = v_reuseFailAlloc_5565_;
goto v_reusejp_5563_;
}
v_reusejp_5563_:
{
return v___x_5564_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5459_ = stack[0].m_obj;
lean_object* v_b_5460_ = stack[1].m_obj;
lean_object* v_a_5461_ = stack[2].m_obj;
lean_object* v_a_5462_ = stack[3].m_obj;
lean_object* v_a_5463_ = stack[4].m_obj;
lean_object* v_a_5464_ = stack[5].m_obj;
lean_object* v_a_5465_ = stack[6].m_obj;
lean_object* v_a_5466_ = stack[7].m_obj;
lean_object* v_a_5467_ = stack[8].m_obj;
lean_object* v_a_5468_ = stack[9].m_obj;
lean_object* v_a_5469_ = stack[10].m_obj;
lean_object* v_a_5470_ = stack[11].m_obj;
lean_object* v_a_5471_ = stack[12].m_obj;
lean_object* v_res_5567_;
v_res_5567_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5459_, v_b_5460_, v_a_5461_, v_a_5462_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_);
stack->m_obj
 = v_res_5567_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq___boxed(lean_object* v_a_5568_, lean_object* v_b_5569_, lean_object* v_a_5570_, lean_object* v_a_5571_, lean_object* v_a_5572_, lean_object* v_a_5573_, lean_object* v_a_5574_, lean_object* v_a_5575_, lean_object* v_a_5576_, lean_object* v_a_5577_, lean_object* v_a_5578_, lean_object* v_a_5579_, lean_object* v_a_5580_, lean_object* v_a_5581_){
_start:
{
lean_object* v_res_5582_; 
v_res_5582_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5568_, v_b_5569_, v_a_5570_, v_a_5571_, v_a_5572_, v_a_5573_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_, v_a_5579_, v_a_5580_);
lean_dec(v_a_5580_);
lean_dec_ref(v_a_5579_);
lean_dec(v_a_5578_);
lean_dec_ref(v_a_5577_);
lean_dec(v_a_5576_);
lean_dec_ref(v_a_5575_);
lean_dec(v_a_5574_);
lean_dec_ref(v_a_5573_);
lean_dec(v_a_5572_);
lean_dec(v_a_5571_);
lean_dec(v_a_5570_);
return v_res_5582_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(lean_object* v_a_5583_, lean_object* v_b_5584_, lean_object* v_a_5585_, lean_object* v_a_5586_, lean_object* v_a_5587_, lean_object* v_a_5588_, lean_object* v_a_5589_, lean_object* v_a_5590_, lean_object* v_a_5591_, lean_object* v_a_5592_, lean_object* v_a_5593_, lean_object* v_a_5594_){
_start:
{
lean_object* v___x_5596_; 
v___x_5596_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5583_, v_b_5584_, v_a_5585_, v_a_5593_);
if (lean_obj_tag(v___x_5596_) == 0)
{
lean_object* v_a_5597_; 
v_a_5597_ = lean_ctor_get(v___x_5596_, 0);
lean_inc(v_a_5597_);
lean_dec_ref_known(v___x_5596_, 1);
if (lean_obj_tag(v_a_5597_) == 1)
{
lean_object* v_val_5598_; lean_object* v___x_5599_; 
v_val_5598_ = lean_ctor_get(v_a_5597_, 0);
lean_inc(v_val_5598_);
lean_dec_ref_known(v_a_5597_, 1);
v___x_5599_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5598_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_);
if (lean_obj_tag(v___x_5599_) == 0)
{
lean_object* v_a_5600_; uint8_t v___x_5601_; 
v_a_5600_ = lean_ctor_get(v___x_5599_, 0);
lean_inc(v_a_5600_);
lean_dec_ref_known(v___x_5599_, 1);
v___x_5601_ = lean_unbox(v_a_5600_);
lean_dec(v_a_5600_);
if (v___x_5601_ == 0)
{
lean_object* v___x_5602_; 
v___x_5602_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5583_, v_b_5584_, v_val_5598_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_);
lean_dec(v_val_5598_);
return v___x_5602_;
}
else
{
lean_object* v___x_5603_; 
v___x_5603_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5583_, v_b_5584_, v_val_5598_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_);
lean_dec(v_val_5598_);
return v___x_5603_;
}
}
else
{
lean_object* v_a_5604_; lean_object* v___x_5606_; uint8_t v_isShared_5607_; uint8_t v_isSharedCheck_5611_; 
lean_dec(v_val_5598_);
lean_dec_ref(v_b_5584_);
lean_dec_ref(v_a_5583_);
v_a_5604_ = lean_ctor_get(v___x_5599_, 0);
v_isSharedCheck_5611_ = !lean_is_exclusive(v___x_5599_);
if (v_isSharedCheck_5611_ == 0)
{
v___x_5606_ = v___x_5599_;
v_isShared_5607_ = v_isSharedCheck_5611_;
goto v_resetjp_5605_;
}
else
{
lean_inc(v_a_5604_);
lean_dec(v___x_5599_);
v___x_5606_ = lean_box(0);
v_isShared_5607_ = v_isSharedCheck_5611_;
goto v_resetjp_5605_;
}
v_resetjp_5605_:
{
lean_object* v___x_5609_; 
if (v_isShared_5607_ == 0)
{
v___x_5609_ = v___x_5606_;
goto v_reusejp_5608_;
}
else
{
lean_object* v_reuseFailAlloc_5610_; 
v_reuseFailAlloc_5610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5610_, 0, v_a_5604_);
v___x_5609_ = v_reuseFailAlloc_5610_;
goto v_reusejp_5608_;
}
v_reusejp_5608_:
{
return v___x_5609_;
}
}
}
}
else
{
lean_object* v___x_5612_; 
lean_dec(v_a_5597_);
v___x_5612_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5583_, v_b_5584_, v_a_5585_, v_a_5593_);
if (lean_obj_tag(v___x_5612_) == 0)
{
lean_object* v_a_5613_; lean_object* v___x_5615_; uint8_t v_isShared_5616_; uint8_t v_isSharedCheck_5623_; 
v_a_5613_ = lean_ctor_get(v___x_5612_, 0);
v_isSharedCheck_5623_ = !lean_is_exclusive(v___x_5612_);
if (v_isSharedCheck_5623_ == 0)
{
v___x_5615_ = v___x_5612_;
v_isShared_5616_ = v_isSharedCheck_5623_;
goto v_resetjp_5614_;
}
else
{
lean_inc(v_a_5613_);
lean_dec(v___x_5612_);
v___x_5615_ = lean_box(0);
v_isShared_5616_ = v_isSharedCheck_5623_;
goto v_resetjp_5614_;
}
v_resetjp_5614_:
{
if (lean_obj_tag(v_a_5613_) == 1)
{
lean_object* v_val_5617_; lean_object* v___x_5618_; 
lean_del_object(v___x_5615_);
v_val_5617_ = lean_ctor_get(v_a_5613_, 0);
lean_inc(v_val_5617_);
lean_dec_ref_known(v_a_5613_, 1);
v___x_5618_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5583_, v_b_5584_, v_val_5617_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_);
lean_dec(v_val_5617_);
return v___x_5618_;
}
else
{
lean_object* v___x_5619_; lean_object* v___x_5621_; 
lean_dec(v_a_5613_);
lean_dec_ref(v_b_5584_);
lean_dec_ref(v_a_5583_);
v___x_5619_ = lean_box(0);
if (v_isShared_5616_ == 0)
{
lean_ctor_set(v___x_5615_, 0, v___x_5619_);
v___x_5621_ = v___x_5615_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v___x_5619_);
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
lean_object* v_a_5624_; lean_object* v___x_5626_; uint8_t v_isShared_5627_; uint8_t v_isSharedCheck_5631_; 
lean_dec_ref(v_b_5584_);
lean_dec_ref(v_a_5583_);
v_a_5624_ = lean_ctor_get(v___x_5612_, 0);
v_isSharedCheck_5631_ = !lean_is_exclusive(v___x_5612_);
if (v_isSharedCheck_5631_ == 0)
{
v___x_5626_ = v___x_5612_;
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
else
{
lean_inc(v_a_5624_);
lean_dec(v___x_5612_);
v___x_5626_ = lean_box(0);
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
v_resetjp_5625_:
{
lean_object* v___x_5629_; 
if (v_isShared_5627_ == 0)
{
v___x_5629_ = v___x_5626_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v_a_5624_);
v___x_5629_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
return v___x_5629_;
}
}
}
}
}
else
{
lean_object* v_a_5632_; lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5639_; 
lean_dec_ref(v_b_5584_);
lean_dec_ref(v_a_5583_);
v_a_5632_ = lean_ctor_get(v___x_5596_, 0);
v_isSharedCheck_5639_ = !lean_is_exclusive(v___x_5596_);
if (v_isSharedCheck_5639_ == 0)
{
v___x_5634_ = v___x_5596_;
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
else
{
lean_inc(v_a_5632_);
lean_dec(v___x_5596_);
v___x_5634_ = lean_box(0);
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
v_resetjp_5633_:
{
lean_object* v___x_5637_; 
if (v_isShared_5635_ == 0)
{
v___x_5637_ = v___x_5634_;
goto v_reusejp_5636_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v_a_5632_);
v___x_5637_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5636_;
}
v_reusejp_5636_:
{
return v___x_5637_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_processNewDiseq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5583_ = stack[0].m_obj;
lean_object* v_b_5584_ = stack[1].m_obj;
lean_object* v_a_5585_ = stack[2].m_obj;
lean_object* v_a_5586_ = stack[3].m_obj;
lean_object* v_a_5587_ = stack[4].m_obj;
lean_object* v_a_5588_ = stack[5].m_obj;
lean_object* v_a_5589_ = stack[6].m_obj;
lean_object* v_a_5590_ = stack[7].m_obj;
lean_object* v_a_5591_ = stack[8].m_obj;
lean_object* v_a_5592_ = stack[9].m_obj;
lean_object* v_a_5593_ = stack[10].m_obj;
lean_object* v_a_5594_ = stack[11].m_obj;
lean_object* v_res_5640_;
v_res_5640_ = l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(v_a_5583_, v_b_5584_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_);
stack->m_obj
 = v_res_5640_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed(lean_object* v_a_5641_, lean_object* v_b_5642_, lean_object* v_a_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_){
_start:
{
lean_object* v_res_5654_; 
v_res_5654_ = l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(v_a_5641_, v_b_5642_, v_a_5643_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_);
lean_dec(v_a_5652_);
lean_dec_ref(v_a_5651_);
lean_dec(v_a_5650_);
lean_dec_ref(v_a_5649_);
lean_dec(v_a_5648_);
lean_dec_ref(v_a_5647_);
lean_dec(v_a_5646_);
lean_dec_ref(v_a_5645_);
lean_dec(v_a_5644_);
lean_dec(v_a_5643_);
return v_res_5654_;
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
