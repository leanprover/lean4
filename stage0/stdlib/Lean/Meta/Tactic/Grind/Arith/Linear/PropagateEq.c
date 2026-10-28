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
lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v_toCold_1364_; lean_object* v_p_1365_; lean_object* v_currRecDepth_1366_; lean_object* v_ref_1367_; uint16_t v_optionFlags_1368_; uint8_t v_suppressElabErrors_1369_; uint8_t v_checkDeprecated_1370_; uint8_t v_isRecordingDeps_1371_; lean_object* v_options_1372_; lean_object* v_maxRecDepth_1373_; lean_object* v_inheritedTraceOptions_1374_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v_toCold_1364_ = lean_ctor_get(v_a_1343_, 0);
lean_inc_ref(v_toCold_1364_);
v_p_1365_ = lean_ctor_get(v_c_1333_, 0);
v_currRecDepth_1366_ = lean_ctor_get(v_a_1343_, 1);
lean_inc(v_currRecDepth_1366_);
v_ref_1367_ = lean_ctor_get(v_a_1343_, 2);
lean_inc(v_ref_1367_);
v_optionFlags_1368_ = lean_ctor_get_uint16(v_a_1343_, sizeof(void*)*3);
v_suppressElabErrors_1369_ = lean_ctor_get_uint8(v_a_1343_, sizeof(void*)*3 + 2);
v_checkDeprecated_1370_ = lean_ctor_get_uint8(v_a_1343_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1371_ = lean_ctor_get_uint8(v_a_1343_, sizeof(void*)*3 + 4);
lean_dec_ref(v_a_1343_);
v_options_1372_ = lean_ctor_get(v_toCold_1364_, 2);
lean_inc_ref(v_options_1372_);
v_maxRecDepth_1373_ = lean_ctor_get(v_toCold_1364_, 3);
v_inheritedTraceOptions_1374_ = lean_ctor_get(v_toCold_1364_, 11);
lean_inc_ref(v_inheritedTraceOptions_1374_);
v___x_1468_ = lean_unsigned_to_nat(0u);
v___x_1469_ = lean_nat_dec_eq(v_maxRecDepth_1373_, v___x_1468_);
if (v___x_1469_ == 0)
{
uint8_t v___x_1470_; 
v___x_1470_ = lean_nat_dec_eq(v_currRecDepth_1366_, v_maxRecDepth_1373_);
if (v___x_1470_ == 0)
{
goto v___jp_1375_;
}
else
{
lean_object* v___x_1471_; 
lean_dec_ref(v_inheritedTraceOptions_1374_);
lean_dec_ref(v_options_1372_);
lean_dec(v_currRecDepth_1366_);
lean_dec_ref(v_toCold_1364_);
lean_dec_ref(v_c_1333_);
v___x_1471_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1367_);
return v___x_1471_;
}
}
else
{
goto v___jp_1375_;
}
v___jp_1346_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_1361_, 0, v___y_1348_);
lean_ctor_set(v___x_1361_, 1, v___y_1347_);
lean_ctor_set(v___x_1361_, 2, v_c_1333_);
v___x_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___y_1349_);
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
v___jp_1375_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1376_ = lean_unsigned_to_nat(1u);
v___x_1377_ = lean_nat_add(v_currRecDepth_1366_, v___x_1376_);
lean_dec(v_currRecDepth_1366_);
v___x_1378_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1378_, 0, v_toCold_1364_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
lean_ctor_set(v___x_1378_, 2, v_ref_1367_);
lean_ctor_set_uint16(v___x_1378_, sizeof(void*)*3, v_optionFlags_1368_);
lean_ctor_set_uint8(v___x_1378_, sizeof(void*)*3 + 2, v_suppressElabErrors_1369_);
lean_ctor_set_uint8(v___x_1378_, sizeof(void*)*3 + 3, v_checkDeprecated_1370_);
lean_ctor_set_uint8(v___x_1378_, sizeof(void*)*3 + 4, v_isRecordingDeps_1371_);
lean_inc(v_p_1365_);
v___x_1379_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_1365_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v___x_1378_, v_a_1344_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1459_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1459_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1459_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
if (lean_obj_tag(v_a_1380_) == 1)
{
lean_object* v_val_1384_; lean_object* v_snd_1385_; uint8_t v_hasTrace_1386_; 
lean_del_object(v___x_1382_);
v_val_1384_ = lean_ctor_get(v_a_1380_, 0);
lean_inc(v_val_1384_);
lean_dec_ref_known(v_a_1380_, 1);
v_snd_1385_ = lean_ctor_get(v_val_1384_, 1);
lean_inc(v_snd_1385_);
v_hasTrace_1386_ = lean_ctor_get_uint8(v_options_1372_, sizeof(void*)*1);
if (v_hasTrace_1386_ == 0)
{
lean_object* v_fst_1387_; lean_object* v_fst_1388_; lean_object* v_snd_1389_; 
lean_dec_ref(v_inheritedTraceOptions_1374_);
lean_dec_ref(v_options_1372_);
v_fst_1387_ = lean_ctor_get(v_val_1384_, 0);
lean_inc(v_fst_1387_);
lean_dec(v_val_1384_);
v_fst_1388_ = lean_ctor_get(v_snd_1385_, 0);
lean_inc(v_fst_1388_);
v_snd_1389_ = lean_ctor_get(v_snd_1385_, 1);
lean_inc(v_snd_1389_);
lean_dec(v_snd_1385_);
v___y_1347_ = v_fst_1388_;
v___y_1348_ = v_fst_1387_;
v___y_1349_ = v_snd_1389_;
v___y_1350_ = v_a_1334_;
v___y_1351_ = v_a_1335_;
v___y_1352_ = v_a_1336_;
v___y_1353_ = v_a_1337_;
v___y_1354_ = v_a_1338_;
v___y_1355_ = v_a_1339_;
v___y_1356_ = v_a_1340_;
v___y_1357_ = v_a_1341_;
v___y_1358_ = v_a_1342_;
v___y_1359_ = v___x_1378_;
v___y_1360_ = v_a_1344_;
goto v___jp_1346_;
}
else
{
lean_object* v_fst_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1454_; 
v_fst_1390_ = lean_ctor_get(v_val_1384_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_val_1384_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; 
v_unused_1455_ = lean_ctor_get(v_val_1384_, 1);
lean_dec(v_unused_1455_);
v___x_1392_ = v_val_1384_;
v_isShared_1393_ = v_isSharedCheck_1454_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_fst_1390_);
lean_dec(v_val_1384_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1454_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_fst_1394_; lean_object* v_snd_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1453_; 
v_fst_1394_ = lean_ctor_get(v_snd_1385_, 0);
v_snd_1395_ = lean_ctor_get(v_snd_1385_, 1);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_snd_1385_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1397_ = v_snd_1385_;
v_isShared_1398_ = v_isSharedCheck_1453_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_snd_1395_);
lean_inc(v_fst_1394_);
lean_dec(v_snd_1385_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1453_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; 
v___x_1399_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_1400_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_1401_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1374_, v_options_1372_, v___x_1400_);
lean_dec_ref(v_options_1372_);
lean_dec_ref(v_inheritedTraceOptions_1374_);
if (v___x_1401_ == 0)
{
lean_del_object(v___x_1397_);
lean_del_object(v___x_1392_);
v___y_1347_ = v_fst_1394_;
v___y_1348_ = v_fst_1390_;
v___y_1349_ = v_snd_1395_;
v___y_1350_ = v_a_1334_;
v___y_1351_ = v_a_1335_;
v___y_1352_ = v_a_1336_;
v___y_1353_ = v_a_1337_;
v___y_1354_ = v_a_1338_;
v___y_1355_ = v_a_1339_;
v___y_1356_ = v_a_1340_;
v___y_1357_ = v_a_1341_;
v___y_1358_ = v_a_1342_;
v___y_1359_ = v___x_1378_;
v___y_1360_ = v_a_1344_;
goto v___jp_1346_;
}
else
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_1390_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v___x_1378_, v_a_1344_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1404_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___x_1402_, 1);
v___x_1404_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v___x_1378_, v_a_1344_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1406_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 1);
v___x_1406_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_fst_1394_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v___x_1378_, v_a_1344_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1411_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___x_1406_, 1);
v___x_1408_ = l_Lean_MessageData_ofExpr(v_a_1403_);
v___x_1409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_1398_ == 0)
{
lean_ctor_set_tag(v___x_1397_, 7);
lean_ctor_set(v___x_1397_, 1, v___x_1409_);
lean_ctor_set(v___x_1397_, 0, v___x_1408_);
v___x_1411_ = v___x_1397_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = l_Lean_MessageData_ofExpr(v_a_1405_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set_tag(v___x_1392_, 7);
lean_ctor_set(v___x_1392_, 1, v___x_1412_);
lean_ctor_set(v___x_1392_, 0, v___x_1411_);
v___x_1414_ = v___x_1392_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
lean_ctor_set(v___x_1415_, 1, v___x_1409_);
v___x_1416_ = l_Lean_MessageData_ofExpr(v_a_1407_);
v___x_1417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1415_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
v___x_1418_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_1399_, v___x_1417_, v_a_1341_, v_a_1342_, v___x_1378_, v_a_1344_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_dec_ref_known(v___x_1418_, 1);
v___y_1347_ = v_fst_1394_;
v___y_1348_ = v_fst_1390_;
v___y_1349_ = v_snd_1395_;
v___y_1350_ = v_a_1334_;
v___y_1351_ = v_a_1335_;
v___y_1352_ = v_a_1336_;
v___y_1353_ = v_a_1337_;
v___y_1354_ = v_a_1338_;
v___y_1355_ = v_a_1339_;
v___y_1356_ = v_a_1340_;
v___y_1357_ = v_a_1341_;
v___y_1358_ = v_a_1342_;
v___y_1359_ = v___x_1378_;
v___y_1360_ = v_a_1344_;
goto v___jp_1346_;
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec(v_snd_1395_);
lean_dec(v_fst_1394_);
lean_dec(v_fst_1390_);
lean_dec_ref_known(v___x_1378_, 3);
lean_dec_ref(v_c_1333_);
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1418_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1418_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec(v_a_1405_);
lean_dec(v_a_1403_);
lean_del_object(v___x_1397_);
lean_dec(v_snd_1395_);
lean_dec(v_fst_1394_);
lean_del_object(v___x_1392_);
lean_dec(v_fst_1390_);
lean_dec_ref_known(v___x_1378_, 3);
lean_dec_ref(v_c_1333_);
v_a_1429_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1406_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1406_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec(v_a_1403_);
lean_del_object(v___x_1397_);
lean_dec(v_snd_1395_);
lean_dec(v_fst_1394_);
lean_del_object(v___x_1392_);
lean_dec(v_fst_1390_);
lean_dec_ref_known(v___x_1378_, 3);
lean_dec_ref(v_c_1333_);
v_a_1437_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1404_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1404_);
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
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_del_object(v___x_1397_);
lean_dec(v_snd_1395_);
lean_dec(v_fst_1394_);
lean_del_object(v___x_1392_);
lean_dec(v_fst_1390_);
lean_dec_ref_known(v___x_1378_, 3);
lean_dec_ref(v_c_1333_);
v_a_1445_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1402_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1402_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
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
lean_object* v___x_1457_; 
lean_dec(v_a_1380_);
lean_dec_ref_known(v___x_1378_, 3);
lean_dec_ref(v_inheritedTraceOptions_1374_);
lean_dec_ref(v_options_1372_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v_c_1333_);
v___x_1457_ = v___x_1382_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_c_1333_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec_ref_known(v___x_1378_, 3);
lean_dec_ref(v_inheritedTraceOptions_1374_);
lean_dec_ref(v_options_1372_);
lean_dec_ref(v_c_1333_);
v_a_1460_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1379_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1379_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object* v_c_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_);
lean_dec(v_a_1483_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
lean_dec(v_a_1479_);
lean_dec_ref(v_a_1478_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
lean_dec(v_a_1475_);
lean_dec(v_a_1474_);
lean_dec(v_a_1473_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_ref_1492_; lean_object* v___x_1493_; lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1502_; 
v_ref_1492_ = lean_ctor_get(v___y_1489_, 2);
v___x_1493_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msg_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1502_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1502_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1500_; 
lean_inc(v_ref_1492_);
v___x_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1498_, 0, v_ref_1492_);
lean_ctor_set(v___x_1498_, 1, v_a_1494_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set_tag(v___x_1496_, 1);
lean_ctor_set(v___x_1496_, 0, v___x_1498_);
v___x_1500_ = v___x_1496_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
return v_res_1509_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0));
v___x_1512_ = l_Lean_stringToMessageData(v___x_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1537_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1528_ = v___x_1525_;
v_isShared_1529_ = v_isSharedCheck_1537_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1525_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1537_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v_leFn_x3f_1530_; 
v_leFn_x3f_1530_ = lean_ctor_get(v_a_1526_, 20);
lean_inc(v_leFn_x3f_1530_);
lean_dec(v_a_1526_);
if (lean_obj_tag(v_leFn_x3f_1530_) == 1)
{
lean_object* v_val_1531_; lean_object* v___x_1533_; 
v_val_1531_ = lean_ctor_get(v_leFn_x3f_1530_, 0);
lean_inc(v_val_1531_);
lean_dec_ref_known(v_leFn_x3f_1530_, 1);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v_val_1531_);
v___x_1533_ = v___x_1528_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_val_1531_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec(v_leFn_x3f_1530_);
lean_del_object(v___x_1528_);
v___x_1535_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1);
v___x_1536_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1535_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
return v___x_1536_;
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
v_a_1538_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1525_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1525_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___boxed(lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec(v___y_1546_);
return v_res_1558_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0));
v___x_1561_ = l_Lean_stringToMessageData(v___x_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1586_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1577_ = v___x_1574_;
v_isShared_1578_ = v_isSharedCheck_1586_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1574_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1586_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v_ltFn_x3f_1579_; 
v_ltFn_x3f_1579_ = lean_ctor_get(v_a_1575_, 21);
lean_inc(v_ltFn_x3f_1579_);
lean_dec(v_a_1575_);
if (lean_obj_tag(v_ltFn_x3f_1579_) == 1)
{
lean_object* v_val_1580_; lean_object* v___x_1582_; 
v_val_1580_ = lean_ctor_get(v_ltFn_x3f_1579_, 0);
lean_inc(v_val_1580_);
lean_dec_ref_known(v_ltFn_x3f_1579_, 1);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v_val_1580_);
v___x_1582_ = v___x_1577_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_val_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_dec(v_ltFn_x3f_1579_);
lean_del_object(v___x_1577_);
v___x_1584_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1);
v___x_1585_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1584_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
return v___x_1585_;
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
v_a_1587_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1574_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1574_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___boxed(lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec(v___y_1595_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(lean_object* v_p_1608_, uint8_t v_strict_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
if (v_strict_1609_ == 0)
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1624_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v___x_1622_, 1);
v___x_1624_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1608_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1626_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v___x_1626_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1636_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1629_ = v___x_1626_;
v_isShared_1630_ = v_isSharedCheck_1636_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1626_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1636_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v_ofNatZero_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
v_ofNatZero_1631_ = lean_ctor_get(v_a_1627_, 18);
lean_inc_ref(v_ofNatZero_1631_);
lean_dec(v_a_1627_);
v___x_1632_ = l_Lean_mkAppB(v_a_1623_, v_a_1625_, v_ofNatZero_1631_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v___x_1632_);
v___x_1634_ = v___x_1629_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1632_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec(v_a_1625_);
lean_dec(v_a_1623_);
v_a_1637_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1626_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1626_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
else
{
lean_dec(v_a_1623_);
return v___x_1624_;
}
}
else
{
return v___x_1622_;
}
}
else
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
v___x_1647_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1608_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1649_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v___x_1649_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1659_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1659_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1659_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v_ofNatZero_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
v_ofNatZero_1654_ = lean_ctor_get(v_a_1650_, 18);
lean_inc_ref(v_ofNatZero_1654_);
lean_dec(v_a_1650_);
v___x_1655_ = l_Lean_mkAppB(v_a_1646_, v_a_1648_, v_ofNatZero_1654_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v___x_1655_);
v___x_1657_ = v___x_1652_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec(v_a_1648_);
lean_dec(v_a_1646_);
v_a_1660_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1649_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1649_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
else
{
lean_dec(v_a_1646_);
return v___x_1647_;
}
}
else
{
return v___x_1645_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_p_1668_, lean_object* v_strict_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
uint8_t v_strict_boxed_1682_; lean_object* v_res_1683_; 
v_strict_boxed_1682_ = lean_unbox(v_strict_1669_);
v_res_1683_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1668_, v_strict_boxed_1682_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec(v_p_1668_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(lean_object* v_c_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_p_1697_; uint8_t v_strict_1698_; lean_object* v___x_1699_; 
v_p_1697_ = lean_ctor_get(v_c_1684_, 0);
v_strict_1698_ = lean_ctor_get_uint8(v_c_1684_, sizeof(void*)*2);
v___x_1699_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1697_, v_strict_1698_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0___boxed(lean_object* v_c_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v_c_1700_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object* v_a_1714_, lean_object* v_x_1715_, lean_object* v_c_u2081_1716_, lean_object* v_b_1717_, lean_object* v_c_u2082_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_toCold_1731_; lean_object* v_options_1732_; lean_object* v_p_1733_; lean_object* v_p_1734_; uint8_t v_strict_1735_; lean_object* v_inheritedTraceOptions_1736_; uint8_t v_hasTrace_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v_p_1742_; 
v_toCold_1731_ = lean_ctor_get(v_a_1728_, 0);
v_options_1732_ = lean_ctor_get(v_toCold_1731_, 2);
v_p_1733_ = lean_ctor_get(v_c_u2081_1716_, 0);
v_p_1734_ = lean_ctor_get(v_c_u2082_1718_, 0);
v_strict_1735_ = lean_ctor_get_uint8(v_c_u2082_1718_, sizeof(void*)*2);
v_inheritedTraceOptions_1736_ = lean_ctor_get(v_toCold_1731_, 11);
v_hasTrace_1737_ = lean_ctor_get_uint8(v_options_1732_, sizeof(void*)*1);
v___x_1738_ = lean_nat_to_int(v_a_1714_);
lean_inc(v_p_1734_);
v___x_1739_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1734_, v___x_1738_);
lean_dec(v___x_1738_);
v___x_1740_ = lean_int_neg(v_b_1717_);
lean_inc(v_p_1733_);
v___x_1741_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1733_, v___x_1740_);
lean_dec(v___x_1740_);
v_p_1742_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1739_, v___x_1741_);
if (v_hasTrace_1737_ == 0)
{
goto v___jp_1743_;
}
else
{
lean_object* v_cls_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v_cls_1747_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_1748_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2);
v___x_1749_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1736_, v_options_1732_, v___x_1748_);
if (v___x_1749_ == 0)
{
goto v___jp_1743_;
}
else
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1715_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1752_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1750_, 1);
v___x_1752_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_1716_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1754_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
v___x_1754_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_u2082_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
v___x_1756_ = l_Lean_MessageData_ofExpr(v_a_1751_);
v___x_1757_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_1758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1756_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = l_Lean_MessageData_ofExpr(v_a_1753_);
v___x_1760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1758_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
v___x_1761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
lean_ctor_set(v___x_1761_, 1, v___x_1757_);
v___x_1762_ = l_Lean_MessageData_ofExpr(v_a_1755_);
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_1747_, v___x_1763_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_dec_ref_known(v___x_1764_, 1);
goto v___jp_1743_;
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec(v_p_1742_);
lean_dec_ref(v_c_u2082_1718_);
lean_dec_ref(v_c_u2081_1716_);
lean_dec(v_x_1715_);
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1764_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v_a_1753_);
lean_dec(v_a_1751_);
lean_dec(v_p_1742_);
lean_dec_ref(v_c_u2082_1718_);
lean_dec_ref(v_c_u2081_1716_);
lean_dec(v_x_1715_);
v_a_1773_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1754_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1754_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec(v_a_1751_);
lean_dec(v_p_1742_);
lean_dec_ref(v_c_u2082_1718_);
lean_dec_ref(v_c_u2081_1716_);
lean_dec(v_x_1715_);
v_a_1781_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1752_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1752_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec(v_p_1742_);
lean_dec_ref(v_c_u2082_1718_);
lean_dec_ref(v_c_u2081_1716_);
lean_dec(v_x_1715_);
v_a_1789_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1750_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1750_);
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
}
v___jp_1743_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = lean_alloc_ctor(13, 3, 0);
lean_ctor_set(v___x_1744_, 0, v_x_1715_);
lean_ctor_set(v___x_1744_, 1, v_c_u2081_1716_);
lean_ctor_set(v___x_1744_, 2, v_c_u2082_1718_);
v___x_1745_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1745_, 0, v_p_1742_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
lean_ctor_set_uint8(v___x_1745_, sizeof(void*)*2, v_strict_1735_);
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object** _args){
lean_object* v_a_1797_ = _args[0];
lean_object* v_x_1798_ = _args[1];
lean_object* v_c_u2081_1799_ = _args[2];
lean_object* v_b_1800_ = _args[3];
lean_object* v_c_u2082_1801_ = _args[4];
lean_object* v_a_1802_ = _args[5];
lean_object* v_a_1803_ = _args[6];
lean_object* v_a_1804_ = _args[7];
lean_object* v_a_1805_ = _args[8];
lean_object* v_a_1806_ = _args[9];
lean_object* v_a_1807_ = _args[10];
lean_object* v_a_1808_ = _args[11];
lean_object* v_a_1809_ = _args[12];
lean_object* v_a_1810_ = _args[13];
lean_object* v_a_1811_ = _args[14];
lean_object* v_a_1812_ = _args[15];
lean_object* v_a_1813_ = _args[16];
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1797_, v_x_1798_, v_c_u2081_1799_, v_b_1800_, v_c_u2082_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
lean_dec(v_a_1806_);
lean_dec_ref(v_a_1805_);
lean_dec(v_a_1804_);
lean_dec(v_a_1803_);
lean_dec(v_a_1802_);
lean_dec(v_b_1800_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1815_, lean_object* v_msg_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1816_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1830_, lean_object* v_msg_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1830_, v_msg_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec(v___y_1832_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(lean_object* v_a_1853_, lean_object* v_x_1854_, lean_object* v_c_u2081_1855_, lean_object* v_as_1856_, size_t v_sz_1857_, size_t v_i_1858_, lean_object* v_b_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
uint8_t v___x_1872_; 
v___x_1872_ = lean_usize_dec_lt(v_i_1858_, v_sz_1857_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; 
lean_dec_ref(v_c_u2081_1855_);
lean_dec(v_x_1854_);
lean_dec(v_a_1853_);
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v_b_1859_);
return v___x_1873_;
}
else
{
lean_object* v_a_1874_; lean_object* v_fst_1875_; lean_object* v_snd_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
lean_dec_ref(v_b_1859_);
v_a_1874_ = lean_array_uget_borrowed(v_as_1856_, v_i_1858_);
v_fst_1875_ = lean_ctor_get(v_a_1874_, 0);
v_snd_1876_ = lean_ctor_get(v_a_1874_, 1);
v___x_1877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
lean_inc(v_snd_1876_);
lean_inc_ref(v_c_u2081_1855_);
lean_inc(v_x_1854_);
lean_inc(v_a_1853_);
v___x_1878_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1853_, v_x_1854_, v_c_u2081_1855_, v_fst_1875_, v_snd_1876_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1880_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref_known(v___x_1878_, 1);
v___x_1880_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_a_1879_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v___x_1881_; 
lean_dec_ref_known(v___x_1880_, 1);
v___x_1881_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1894_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1884_ = v___x_1881_;
v_isShared_1885_ = v_isSharedCheck_1894_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1881_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1894_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
uint8_t v___x_1886_; 
v___x_1886_ = lean_unbox(v_a_1882_);
lean_dec(v_a_1882_);
if (v___x_1886_ == 0)
{
size_t v___x_1887_; size_t v___x_1888_; 
lean_del_object(v___x_1884_);
v___x_1887_ = ((size_t)1ULL);
v___x_1888_ = lean_usize_add(v_i_1858_, v___x_1887_);
v_i_1858_ = v___x_1888_;
v_b_1859_ = v___x_1877_;
goto _start;
}
else
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
lean_dec_ref(v_c_u2081_1855_);
lean_dec(v_x_1854_);
lean_dec(v_a_1853_);
v___x_1890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___x_1890_);
v___x_1892_ = v___x_1884_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_dec_ref(v_c_u2081_1855_);
lean_dec(v_x_1854_);
lean_dec(v_a_1853_);
v_a_1895_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1881_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1881_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_dec_ref(v_c_u2081_1855_);
lean_dec(v_x_1854_);
lean_dec(v_a_1853_);
v_a_1903_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1880_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1880_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec_ref(v_c_u2081_1855_);
lean_dec(v_x_1854_);
lean_dec(v_a_1853_);
v_a_1911_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1878_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1878_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___boxed(lean_object** _args){
lean_object* v_a_1919_ = _args[0];
lean_object* v_x_1920_ = _args[1];
lean_object* v_c_u2081_1921_ = _args[2];
lean_object* v_as_1922_ = _args[3];
lean_object* v_sz_1923_ = _args[4];
lean_object* v_i_1924_ = _args[5];
lean_object* v_b_1925_ = _args[6];
lean_object* v___y_1926_ = _args[7];
lean_object* v___y_1927_ = _args[8];
lean_object* v___y_1928_ = _args[9];
lean_object* v___y_1929_ = _args[10];
lean_object* v___y_1930_ = _args[11];
lean_object* v___y_1931_ = _args[12];
lean_object* v___y_1932_ = _args[13];
lean_object* v___y_1933_ = _args[14];
lean_object* v___y_1934_ = _args[15];
lean_object* v___y_1935_ = _args[16];
lean_object* v___y_1936_ = _args[17];
lean_object* v___y_1937_ = _args[18];
_start:
{
size_t v_sz_boxed_1938_; size_t v_i_boxed_1939_; lean_object* v_res_1940_; 
v_sz_boxed_1938_ = lean_unbox_usize(v_sz_1923_);
lean_dec(v_sz_1923_);
v_i_boxed_1939_ = lean_unbox_usize(v_i_1924_);
lean_dec(v_i_1924_);
v_res_1940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1919_, v_x_1920_, v_c_u2081_1921_, v_as_1922_, v_sz_boxed_1938_, v_i_boxed_1939_, v_b_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
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
lean_dec_ref(v_as_1922_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(lean_object* v_a_1941_, lean_object* v_x_1942_, lean_object* v_c_u2081_1943_, lean_object* v_todo_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; size_t v_sz_1959_; size_t v___x_1960_; lean_object* v___x_1961_; 
v___x_1957_ = lean_box(0);
v___x_1958_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_1959_ = lean_array_size(v_todo_1944_);
v___x_1960_ = ((size_t)0ULL);
v___x_1961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1941_, v_x_1942_, v_c_u2081_1943_, v_todo_1944_, v_sz_1959_, v___x_1960_, v___x_1958_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1974_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_1974_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1974_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v_fst_1966_; 
v_fst_1966_ = lean_ctor_get(v_a_1962_, 0);
lean_inc(v_fst_1966_);
lean_dec(v_a_1962_);
if (lean_obj_tag(v_fst_1966_) == 0)
{
lean_object* v___x_1968_; 
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v___x_1957_);
v___x_1968_ = v___x_1964_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1957_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
else
{
lean_object* v_val_1970_; lean_object* v___x_1972_; 
v_val_1970_ = lean_ctor_get(v_fst_1966_, 0);
lean_inc(v_val_1970_);
lean_dec_ref_known(v_fst_1966_, 1);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v_val_1970_);
v___x_1972_ = v___x_1964_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_val_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
v_a_1975_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1961_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1961_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object* v_a_1983_, lean_object* v_x_1984_, lean_object* v_c_u2081_1985_, lean_object* v_todo_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_1983_, v_x_1984_, v_c_u2081_1985_, v_todo_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_);
lean_dec(v_a_1997_);
lean_dec_ref(v_a_1996_);
lean_dec(v_a_1995_);
lean_dec_ref(v_a_1994_);
lean_dec(v_a_1993_);
lean_dec_ref(v_a_1992_);
lean_dec(v_a_1991_);
lean_dec_ref(v_a_1990_);
lean_dec(v_a_1989_);
lean_dec(v_a_1988_);
lean_dec(v_a_1987_);
lean_dec_ref(v_todo_1986_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_2000_, lean_object* v_as_2001_, size_t v_sz_2002_, size_t v_i_2003_, lean_object* v_b_2004_){
_start:
{
uint8_t v___x_2005_; 
v___x_2005_ = lean_usize_dec_lt(v_i_2003_, v_sz_2002_);
if (v___x_2005_ == 0)
{
return v_b_2004_;
}
else
{
lean_object* v_snd_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2039_; 
v_snd_2006_ = lean_ctor_get(v_b_2004_, 1);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_b_2004_);
if (v_isSharedCheck_2039_ == 0)
{
lean_object* v_unused_2040_; 
v_unused_2040_ = lean_ctor_get(v_b_2004_, 0);
lean_dec(v_unused_2040_);
v___x_2008_ = v_b_2004_;
v_isShared_2009_ = v_isSharedCheck_2039_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_snd_2006_);
lean_dec(v_b_2004_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2039_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v_fst_2010_; lean_object* v_snd_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2038_; 
v_fst_2010_ = lean_ctor_get(v_snd_2006_, 0);
v_snd_2011_ = lean_ctor_get(v_snd_2006_, 1);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_snd_2006_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2013_ = v_snd_2006_;
v_isShared_2014_ = v_isSharedCheck_2038_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_snd_2011_);
lean_inc(v_fst_2010_);
lean_dec(v_snd_2006_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2038_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v_a_2015_; lean_object* v_p_2016_; lean_object* v___x_2017_; lean_object* v_a_2019_; lean_object* v_b_2026_; lean_object* v___x_2027_; uint8_t v___x_2028_; 
v_a_2015_ = lean_array_uget_borrowed(v_as_2001_, v_i_2003_);
v_p_2016_ = lean_ctor_get(v_a_2015_, 0);
v___x_2017_ = lean_box(0);
v_b_2026_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2016_, v_x_2000_);
v___x_2027_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2028_ = lean_int_dec_eq(v_b_2026_, v___x_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2030_; 
lean_inc(v_a_2015_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 1, v_a_2015_);
lean_ctor_set(v___x_2008_, 0, v_b_2026_);
v___x_2030_ = v___x_2008_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_b_2026_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_a_2015_);
v___x_2030_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v_todo_2031_; lean_object* v___x_2032_; 
v_todo_2031_ = lean_array_push(v_snd_2011_, v___x_2030_);
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v_fst_2010_);
lean_ctor_set(v___x_2032_, 1, v_todo_2031_);
v_a_2019_ = v___x_2032_;
goto v___jp_2018_;
}
}
else
{
lean_object* v_cs_x27_2034_; lean_object* v___x_2036_; 
lean_dec(v_b_2026_);
lean_inc(v_a_2015_);
v_cs_x27_2034_ = l_Lean_PersistentArray_push___redArg(v_fst_2010_, v_a_2015_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 1, v_snd_2011_);
lean_ctor_set(v___x_2008_, 0, v_cs_x27_2034_);
v___x_2036_ = v___x_2008_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_cs_x27_2034_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_snd_2011_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
v_a_2019_ = v___x_2036_;
goto v___jp_2018_;
}
}
v___jp_2018_:
{
lean_object* v___x_2021_; 
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 1, v_a_2019_);
lean_ctor_set(v___x_2013_, 0, v___x_2017_);
v___x_2021_ = v___x_2013_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_a_2019_);
v___x_2021_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
size_t v___x_2022_; size_t v___x_2023_; 
v___x_2022_ = ((size_t)1ULL);
v___x_2023_ = lean_usize_add(v_i_2003_, v___x_2022_);
v_i_2003_ = v___x_2023_;
v_b_2004_ = v___x_2021_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_2041_, lean_object* v_as_2042_, lean_object* v_sz_2043_, lean_object* v_i_2044_, lean_object* v_b_2045_){
_start:
{
size_t v_sz_boxed_2046_; size_t v_i_boxed_2047_; lean_object* v_res_2048_; 
v_sz_boxed_2046_ = lean_unbox_usize(v_sz_2043_);
lean_dec(v_sz_2043_);
v_i_boxed_2047_ = lean_unbox_usize(v_i_2044_);
lean_dec(v_i_2044_);
v_res_2048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2041_, v_as_2042_, v_sz_boxed_2046_, v_i_boxed_2047_, v_b_2045_);
lean_dec_ref(v_as_2042_);
lean_dec(v_x_2041_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(lean_object* v_x_2049_, lean_object* v_as_2050_, size_t v_sz_2051_, size_t v_i_2052_, lean_object* v_b_2053_){
_start:
{
uint8_t v___x_2054_; 
v___x_2054_ = lean_usize_dec_lt(v_i_2052_, v_sz_2051_);
if (v___x_2054_ == 0)
{
return v_b_2053_;
}
else
{
lean_object* v_snd_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2088_; 
v_snd_2055_ = lean_ctor_get(v_b_2053_, 1);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_b_2053_);
if (v_isSharedCheck_2088_ == 0)
{
lean_object* v_unused_2089_; 
v_unused_2089_ = lean_ctor_get(v_b_2053_, 0);
lean_dec(v_unused_2089_);
v___x_2057_ = v_b_2053_;
v_isShared_2058_ = v_isSharedCheck_2088_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_snd_2055_);
lean_dec(v_b_2053_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2088_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v_fst_2059_; lean_object* v_snd_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2087_; 
v_fst_2059_ = lean_ctor_get(v_snd_2055_, 0);
v_snd_2060_ = lean_ctor_get(v_snd_2055_, 1);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_snd_2055_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2062_ = v_snd_2055_;
v_isShared_2063_ = v_isSharedCheck_2087_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_snd_2060_);
lean_inc(v_fst_2059_);
lean_dec(v_snd_2055_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2087_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v_a_2064_; lean_object* v_p_2065_; lean_object* v___x_2066_; lean_object* v_a_2068_; lean_object* v_b_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
v_a_2064_ = lean_array_uget_borrowed(v_as_2050_, v_i_2052_);
v_p_2065_ = lean_ctor_get(v_a_2064_, 0);
v___x_2066_ = lean_box(0);
v_b_2075_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2065_, v_x_2049_);
v___x_2076_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2077_ = lean_int_dec_eq(v_b_2075_, v___x_2076_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2079_; 
lean_inc(v_a_2064_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 1, v_a_2064_);
lean_ctor_set(v___x_2057_, 0, v_b_2075_);
v___x_2079_ = v___x_2057_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_b_2075_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_a_2064_);
v___x_2079_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v_todo_2080_; lean_object* v___x_2081_; 
v_todo_2080_ = lean_array_push(v_snd_2060_, v___x_2079_);
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v_fst_2059_);
lean_ctor_set(v___x_2081_, 1, v_todo_2080_);
v_a_2068_ = v___x_2081_;
goto v___jp_2067_;
}
}
else
{
lean_object* v_cs_x27_2083_; lean_object* v___x_2085_; 
lean_dec(v_b_2075_);
lean_inc(v_a_2064_);
v_cs_x27_2083_ = l_Lean_PersistentArray_push___redArg(v_fst_2059_, v_a_2064_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 1, v_snd_2060_);
lean_ctor_set(v___x_2057_, 0, v_cs_x27_2083_);
v___x_2085_ = v___x_2057_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_cs_x27_2083_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_snd_2060_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
v_a_2068_ = v___x_2085_;
goto v___jp_2067_;
}
}
v___jp_2067_:
{
lean_object* v___x_2070_; 
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 1, v_a_2068_);
lean_ctor_set(v___x_2062_, 0, v___x_2066_);
v___x_2070_ = v___x_2062_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2066_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_a_2068_);
v___x_2070_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
size_t v___x_2071_; size_t v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = ((size_t)1ULL);
v___x_2072_ = lean_usize_add(v_i_2052_, v___x_2071_);
v___x_2073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2049_, v_as_2050_, v_sz_2051_, v___x_2072_, v___x_2070_);
return v___x_2073_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2090_, lean_object* v_as_2091_, lean_object* v_sz_2092_, lean_object* v_i_2093_, lean_object* v_b_2094_){
_start:
{
size_t v_sz_boxed_2095_; size_t v_i_boxed_2096_; lean_object* v_res_2097_; 
v_sz_boxed_2095_ = lean_unbox_usize(v_sz_2092_);
lean_dec(v_sz_2092_);
v_i_boxed_2096_ = lean_unbox_usize(v_i_2093_);
lean_dec(v_i_2093_);
v_res_2097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2090_, v_as_2091_, v_sz_boxed_2095_, v_i_boxed_2096_, v_b_2094_);
lean_dec_ref(v_as_2091_);
lean_dec(v_x_2090_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_2098_, lean_object* v_as_2099_, size_t v_sz_2100_, size_t v_i_2101_, lean_object* v_b_2102_){
_start:
{
uint8_t v___x_2103_; 
v___x_2103_ = lean_usize_dec_lt(v_i_2101_, v_sz_2100_);
if (v___x_2103_ == 0)
{
return v_b_2102_;
}
else
{
lean_object* v_snd_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2137_; 
v_snd_2104_ = lean_ctor_get(v_b_2102_, 1);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_b_2102_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; 
v_unused_2138_ = lean_ctor_get(v_b_2102_, 0);
lean_dec(v_unused_2138_);
v___x_2106_ = v_b_2102_;
v_isShared_2107_ = v_isSharedCheck_2137_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_snd_2104_);
lean_dec(v_b_2102_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2137_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v_fst_2108_; lean_object* v_snd_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2136_; 
v_fst_2108_ = lean_ctor_get(v_snd_2104_, 0);
v_snd_2109_ = lean_ctor_get(v_snd_2104_, 1);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_snd_2104_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2111_ = v_snd_2104_;
v_isShared_2112_ = v_isSharedCheck_2136_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_snd_2109_);
lean_inc(v_fst_2108_);
lean_dec(v_snd_2104_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2136_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v_a_2113_; lean_object* v_p_2114_; lean_object* v___x_2115_; lean_object* v_a_2117_; lean_object* v_b_2124_; lean_object* v___x_2125_; uint8_t v___x_2126_; 
v_a_2113_ = lean_array_uget_borrowed(v_as_2099_, v_i_2101_);
v_p_2114_ = lean_ctor_get(v_a_2113_, 0);
v___x_2115_ = lean_box(0);
v_b_2124_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2114_, v_x_2098_);
v___x_2125_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2126_ = lean_int_dec_eq(v_b_2124_, v___x_2125_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2128_; 
lean_inc(v_a_2113_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 1, v_a_2113_);
lean_ctor_set(v___x_2106_, 0, v_b_2124_);
v___x_2128_ = v___x_2106_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_b_2124_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_a_2113_);
v___x_2128_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v_todo_2129_; lean_object* v___x_2130_; 
v_todo_2129_ = lean_array_push(v_snd_2109_, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2130_, 0, v_fst_2108_);
lean_ctor_set(v___x_2130_, 1, v_todo_2129_);
v_a_2117_ = v___x_2130_;
goto v___jp_2116_;
}
}
else
{
lean_object* v_cs_x27_2132_; lean_object* v___x_2134_; 
lean_dec(v_b_2124_);
lean_inc(v_a_2113_);
v_cs_x27_2132_ = l_Lean_PersistentArray_push___redArg(v_fst_2108_, v_a_2113_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 1, v_snd_2109_);
lean_ctor_set(v___x_2106_, 0, v_cs_x27_2132_);
v___x_2134_ = v___x_2106_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_cs_x27_2132_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_snd_2109_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
v_a_2117_ = v___x_2134_;
goto v___jp_2116_;
}
}
v___jp_2116_:
{
lean_object* v___x_2119_; 
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 1, v_a_2117_);
lean_ctor_set(v___x_2111_, 0, v___x_2115_);
v___x_2119_ = v___x_2111_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_a_2117_);
v___x_2119_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
size_t v___x_2120_; size_t v___x_2121_; 
v___x_2120_ = ((size_t)1ULL);
v___x_2121_ = lean_usize_add(v_i_2101_, v___x_2120_);
v_i_2101_ = v___x_2121_;
v_b_2102_ = v___x_2119_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_2139_, lean_object* v_as_2140_, lean_object* v_sz_2141_, lean_object* v_i_2142_, lean_object* v_b_2143_){
_start:
{
size_t v_sz_boxed_2144_; size_t v_i_boxed_2145_; lean_object* v_res_2146_; 
v_sz_boxed_2144_ = lean_unbox_usize(v_sz_2141_);
lean_dec(v_sz_2141_);
v_i_boxed_2145_ = lean_unbox_usize(v_i_2142_);
lean_dec(v_i_2142_);
v_res_2146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2139_, v_as_2140_, v_sz_boxed_2144_, v_i_boxed_2145_, v_b_2143_);
lean_dec_ref(v_as_2140_);
lean_dec(v_x_2139_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2147_, lean_object* v_as_2148_, size_t v_sz_2149_, size_t v_i_2150_, lean_object* v_b_2151_){
_start:
{
uint8_t v___x_2152_; 
v___x_2152_ = lean_usize_dec_lt(v_i_2150_, v_sz_2149_);
if (v___x_2152_ == 0)
{
return v_b_2151_;
}
else
{
lean_object* v_snd_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2186_; 
v_snd_2153_ = lean_ctor_get(v_b_2151_, 1);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_b_2151_);
if (v_isSharedCheck_2186_ == 0)
{
lean_object* v_unused_2187_; 
v_unused_2187_ = lean_ctor_get(v_b_2151_, 0);
lean_dec(v_unused_2187_);
v___x_2155_ = v_b_2151_;
v_isShared_2156_ = v_isSharedCheck_2186_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_snd_2153_);
lean_dec(v_b_2151_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2186_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v_fst_2157_; lean_object* v_snd_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2185_; 
v_fst_2157_ = lean_ctor_get(v_snd_2153_, 0);
v_snd_2158_ = lean_ctor_get(v_snd_2153_, 1);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_snd_2153_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2160_ = v_snd_2153_;
v_isShared_2161_ = v_isSharedCheck_2185_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_snd_2158_);
lean_inc(v_fst_2157_);
lean_dec(v_snd_2153_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2185_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v_a_2162_; lean_object* v_p_2163_; lean_object* v___x_2164_; lean_object* v_a_2166_; lean_object* v_b_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v_a_2162_ = lean_array_uget_borrowed(v_as_2148_, v_i_2150_);
v_p_2163_ = lean_ctor_get(v_a_2162_, 0);
v___x_2164_ = lean_box(0);
v_b_2173_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2163_, v_x_2147_);
v___x_2174_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2175_ = lean_int_dec_eq(v_b_2173_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2177_; 
lean_inc(v_a_2162_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 1, v_a_2162_);
lean_ctor_set(v___x_2155_, 0, v_b_2173_);
v___x_2177_ = v___x_2155_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_b_2173_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_a_2162_);
v___x_2177_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_object* v_todo_2178_; lean_object* v___x_2179_; 
v_todo_2178_ = lean_array_push(v_snd_2158_, v___x_2177_);
v___x_2179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2179_, 0, v_fst_2157_);
lean_ctor_set(v___x_2179_, 1, v_todo_2178_);
v_a_2166_ = v___x_2179_;
goto v___jp_2165_;
}
}
else
{
lean_object* v_cs_x27_2181_; lean_object* v___x_2183_; 
lean_dec(v_b_2173_);
lean_inc(v_a_2162_);
v_cs_x27_2181_ = l_Lean_PersistentArray_push___redArg(v_fst_2157_, v_a_2162_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 1, v_snd_2158_);
lean_ctor_set(v___x_2155_, 0, v_cs_x27_2181_);
v___x_2183_ = v___x_2155_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_cs_x27_2181_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_snd_2158_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
v_a_2166_ = v___x_2183_;
goto v___jp_2165_;
}
}
v___jp_2165_:
{
lean_object* v___x_2168_; 
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 1, v_a_2166_);
lean_ctor_set(v___x_2160_, 0, v___x_2164_);
v___x_2168_ = v___x_2160_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_a_2166_);
v___x_2168_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
size_t v___x_2169_; size_t v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = ((size_t)1ULL);
v___x_2170_ = lean_usize_add(v_i_2150_, v___x_2169_);
v___x_2171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2147_, v_as_2148_, v_sz_2149_, v___x_2170_, v___x_2168_);
return v___x_2171_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_2188_, lean_object* v_as_2189_, lean_object* v_sz_2190_, lean_object* v_i_2191_, lean_object* v_b_2192_){
_start:
{
size_t v_sz_boxed_2193_; size_t v_i_boxed_2194_; lean_object* v_res_2195_; 
v_sz_boxed_2193_ = lean_unbox_usize(v_sz_2190_);
lean_dec(v_sz_2190_);
v_i_boxed_2194_ = lean_unbox_usize(v_i_2191_);
lean_dec(v_i_2191_);
v_res_2195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2188_, v_as_2189_, v_sz_boxed_2193_, v_i_boxed_2194_, v_b_2192_);
lean_dec_ref(v_as_2189_);
lean_dec(v_x_2188_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(lean_object* v_init_2196_, lean_object* v_x_2197_, lean_object* v_n_2198_, lean_object* v_b_2199_){
_start:
{
if (lean_obj_tag(v_n_2198_) == 0)
{
lean_object* v_cs_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; size_t v_sz_2203_; size_t v___x_2204_; lean_object* v___x_2205_; lean_object* v_fst_2206_; 
v_cs_2200_ = lean_ctor_get(v_n_2198_, 0);
v___x_2201_ = lean_box(0);
v___x_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set(v___x_2202_, 1, v_b_2199_);
v_sz_2203_ = lean_array_size(v_cs_2200_);
v___x_2204_ = ((size_t)0ULL);
v___x_2205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2196_, v_x_2197_, v_cs_2200_, v_sz_2203_, v___x_2204_, v___x_2202_);
v_fst_2206_ = lean_ctor_get(v___x_2205_, 0);
if (lean_obj_tag(v_fst_2206_) == 0)
{
lean_object* v_snd_2207_; lean_object* v___x_2208_; 
v_snd_2207_ = lean_ctor_get(v___x_2205_, 1);
lean_inc(v_snd_2207_);
lean_dec_ref(v___x_2205_);
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v_snd_2207_);
return v___x_2208_;
}
else
{
lean_object* v_val_2209_; 
lean_inc_ref(v_fst_2206_);
lean_dec_ref(v___x_2205_);
v_val_2209_ = lean_ctor_get(v_fst_2206_, 0);
lean_inc(v_val_2209_);
lean_dec_ref_known(v_fst_2206_, 1);
return v_val_2209_;
}
}
else
{
lean_object* v_vs_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; size_t v_sz_2213_; size_t v___x_2214_; lean_object* v___x_2215_; lean_object* v_fst_2216_; 
v_vs_2210_ = lean_ctor_get(v_n_2198_, 0);
v___x_2211_ = lean_box(0);
v___x_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
lean_ctor_set(v___x_2212_, 1, v_b_2199_);
v_sz_2213_ = lean_array_size(v_vs_2210_);
v___x_2214_ = ((size_t)0ULL);
v___x_2215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2197_, v_vs_2210_, v_sz_2213_, v___x_2214_, v___x_2212_);
v_fst_2216_ = lean_ctor_get(v___x_2215_, 0);
if (lean_obj_tag(v_fst_2216_) == 0)
{
lean_object* v_snd_2217_; lean_object* v___x_2218_; 
v_snd_2217_ = lean_ctor_get(v___x_2215_, 1);
lean_inc(v_snd_2217_);
lean_dec_ref(v___x_2215_);
v___x_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2218_, 0, v_snd_2217_);
return v___x_2218_;
}
else
{
lean_object* v_val_2219_; 
lean_inc_ref(v_fst_2216_);
lean_dec_ref(v___x_2215_);
v_val_2219_ = lean_ctor_get(v_fst_2216_, 0);
lean_inc(v_val_2219_);
lean_dec_ref_known(v_fst_2216_, 1);
return v_val_2219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_2220_, lean_object* v_x_2221_, lean_object* v_as_2222_, size_t v_sz_2223_, size_t v_i_2224_, lean_object* v_b_2225_){
_start:
{
uint8_t v___x_2226_; 
v___x_2226_ = lean_usize_dec_lt(v_i_2224_, v_sz_2223_);
if (v___x_2226_ == 0)
{
return v_b_2225_;
}
else
{
lean_object* v_snd_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2245_; 
v_snd_2227_ = lean_ctor_get(v_b_2225_, 1);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_b_2225_);
if (v_isSharedCheck_2245_ == 0)
{
lean_object* v_unused_2246_; 
v_unused_2246_ = lean_ctor_get(v_b_2225_, 0);
lean_dec(v_unused_2246_);
v___x_2229_ = v_b_2225_;
v_isShared_2230_ = v_isSharedCheck_2245_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_snd_2227_);
lean_dec(v_b_2225_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2245_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v_a_2231_; lean_object* v___x_2232_; 
v_a_2231_ = lean_array_uget_borrowed(v_as_2222_, v_i_2224_);
lean_inc(v_snd_2227_);
v___x_2232_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2220_, v_x_2221_, v_a_2231_, v_snd_2227_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2233_);
v___x_2235_ = v___x_2229_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_snd_2227_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2238_; lean_object* v___x_2240_; 
lean_dec(v_snd_2227_);
v_a_2237_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2232_, 1);
v___x_2238_ = lean_box(0);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 1, v_a_2237_);
lean_ctor_set(v___x_2229_, 0, v___x_2238_);
v___x_2240_ = v___x_2229_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2238_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_a_2237_);
v___x_2240_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
size_t v___x_2241_; size_t v___x_2242_; 
v___x_2241_ = ((size_t)1ULL);
v___x_2242_ = lean_usize_add(v_i_2224_, v___x_2241_);
v_i_2224_ = v___x_2242_;
v_b_2225_ = v___x_2240_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_2247_, lean_object* v_x_2248_, lean_object* v_as_2249_, lean_object* v_sz_2250_, lean_object* v_i_2251_, lean_object* v_b_2252_){
_start:
{
size_t v_sz_boxed_2253_; size_t v_i_boxed_2254_; lean_object* v_res_2255_; 
v_sz_boxed_2253_ = lean_unbox_usize(v_sz_2250_);
lean_dec(v_sz_2250_);
v_i_boxed_2254_ = lean_unbox_usize(v_i_2251_);
lean_dec(v_i_2251_);
v_res_2255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2247_, v_x_2248_, v_as_2249_, v_sz_boxed_2253_, v_i_boxed_2254_, v_b_2252_);
lean_dec_ref(v_as_2249_);
lean_dec(v_x_2248_);
lean_dec_ref(v_init_2247_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_2256_, lean_object* v_x_2257_, lean_object* v_n_2258_, lean_object* v_b_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2256_, v_x_2257_, v_n_2258_, v_b_2259_);
lean_dec_ref(v_n_2258_);
lean_dec(v_x_2257_);
lean_dec_ref(v_init_2256_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(lean_object* v_x_2261_, lean_object* v_t_2262_, lean_object* v_init_2263_){
_start:
{
lean_object* v_root_2264_; lean_object* v_tail_2265_; lean_object* v___x_2266_; 
v_root_2264_ = lean_ctor_get(v_t_2262_, 0);
v_tail_2265_ = lean_ctor_get(v_t_2262_, 1);
lean_inc_ref(v_init_2263_);
v___x_2266_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2263_, v_x_2261_, v_root_2264_, v_init_2263_);
lean_dec_ref(v_init_2263_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2266_, 1);
return v_a_2267_;
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; size_t v_sz_2271_; size_t v___x_2272_; lean_object* v___x_2273_; lean_object* v_fst_2274_; 
v_a_2268_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2268_);
lean_dec_ref_known(v___x_2266_, 1);
v___x_2269_ = lean_box(0);
v___x_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
lean_ctor_set(v___x_2270_, 1, v_a_2268_);
v_sz_2271_ = lean_array_size(v_tail_2265_);
v___x_2272_ = ((size_t)0ULL);
v___x_2273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2261_, v_tail_2265_, v_sz_2271_, v___x_2272_, v___x_2270_);
v_fst_2274_ = lean_ctor_get(v___x_2273_, 0);
if (lean_obj_tag(v_fst_2274_) == 0)
{
lean_object* v_snd_2275_; 
v_snd_2275_ = lean_ctor_get(v___x_2273_, 1);
lean_inc(v_snd_2275_);
lean_dec_ref(v___x_2273_);
return v_snd_2275_;
}
else
{
lean_object* v_val_2276_; 
lean_inc_ref(v_fst_2274_);
lean_dec_ref(v___x_2273_);
v_val_2276_ = lean_ctor_get(v_fst_2274_, 0);
lean_inc(v_val_2276_);
lean_dec_ref_known(v_fst_2274_, 1);
return v_val_2276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0___boxed(lean_object* v_x_2277_, lean_object* v_t_2278_, lean_object* v_init_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2277_, v_t_2278_, v_init_2279_);
lean_dec_ref(v_t_2278_);
lean_dec(v_x_2277_);
return v_res_2280_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2281_ = lean_unsigned_to_nat(32u);
v___x_2282_ = lean_mk_empty_array_with_capacity(v___x_2281_);
v___x_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
return v___x_2283_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1(void){
_start:
{
size_t v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v_cs_x27_2289_; 
v___x_2284_ = ((size_t)5ULL);
v___x_2285_ = lean_unsigned_to_nat(0u);
v___x_2286_ = lean_unsigned_to_nat(32u);
v___x_2287_ = lean_mk_empty_array_with_capacity(v___x_2286_);
v___x_2288_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0);
v_cs_x27_2289_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_2289_, 0, v___x_2288_);
lean_ctor_set(v_cs_x27_2289_, 1, v___x_2287_);
lean_ctor_set(v_cs_x27_2289_, 2, v___x_2285_);
lean_ctor_set(v_cs_x27_2289_, 3, v___x_2285_);
lean_ctor_set_usize(v_cs_x27_2289_, 4, v___x_2284_);
return v_cs_x27_2289_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_2292_; lean_object* v_cs_x27_2293_; lean_object* v___x_2294_; 
v_todo_2292_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2));
v_cs_x27_2293_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1);
v___x_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2294_, 0, v_cs_x27_2293_);
lean_ctor_set(v___x_2294_, 1, v_todo_2292_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(lean_object* v_x_2295_, lean_object* v_cs_2296_){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v_fst_2299_; lean_object* v_snd_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
v___x_2297_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3);
v___x_2298_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2295_, v_cs_2296_, v___x_2297_);
v_fst_2299_ = lean_ctor_get(v___x_2298_, 0);
v_snd_2300_ = lean_ctor_get(v___x_2298_, 1);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2298_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_snd_2300_);
lean_inc(v_fst_2299_);
lean_dec(v___x_2298_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_fst_2299_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v_snd_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___boxed(lean_object* v_x_2308_, lean_object* v_cs_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2308_, v_cs_2309_);
lean_dec_ref(v_cs_2309_);
lean_dec(v_x_2308_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object* v_x_2311_, lean_object* v_cs_2312_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2311_, v_cs_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___boxed(lean_object* v_x_2314_, lean_object* v_cs_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(v_x_2314_, v_cs_2315_);
lean_dec_ref(v_cs_2315_);
lean_dec(v_x_2314_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(lean_object* v_a_2317_, lean_object* v_y_2318_, lean_object* v_fst_2319_, lean_object* v_s_2320_){
_start:
{
lean_object* v_structs_2321_; lean_object* v_typeIdOf_2322_; lean_object* v_exprToStructId_2323_; lean_object* v_exprToStructIdEntries_2324_; lean_object* v_forbiddenNatModules_2325_; lean_object* v_natStructs_2326_; lean_object* v_natTypeIdOf_2327_; lean_object* v_exprToNatStructId_2328_; lean_object* v___x_2329_; uint8_t v___x_2330_; 
v_structs_2321_ = lean_ctor_get(v_s_2320_, 0);
v_typeIdOf_2322_ = lean_ctor_get(v_s_2320_, 1);
v_exprToStructId_2323_ = lean_ctor_get(v_s_2320_, 2);
v_exprToStructIdEntries_2324_ = lean_ctor_get(v_s_2320_, 3);
v_forbiddenNatModules_2325_ = lean_ctor_get(v_s_2320_, 4);
v_natStructs_2326_ = lean_ctor_get(v_s_2320_, 5);
v_natTypeIdOf_2327_ = lean_ctor_get(v_s_2320_, 6);
v_exprToNatStructId_2328_ = lean_ctor_get(v_s_2320_, 7);
v___x_2329_ = lean_array_get_size(v_structs_2321_);
v___x_2330_ = lean_nat_dec_lt(v_a_2317_, v___x_2329_);
if (v___x_2330_ == 0)
{
lean_dec_ref(v_fst_2319_);
return v_s_2320_;
}
else
{
lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2392_; 
lean_inc_ref(v_exprToNatStructId_2328_);
lean_inc_ref(v_natTypeIdOf_2327_);
lean_inc_ref(v_natStructs_2326_);
lean_inc_ref(v_forbiddenNatModules_2325_);
lean_inc_ref(v_exprToStructIdEntries_2324_);
lean_inc_ref(v_exprToStructId_2323_);
lean_inc_ref(v_typeIdOf_2322_);
lean_inc_ref(v_structs_2321_);
v_isSharedCheck_2392_ = !lean_is_exclusive(v_s_2320_);
if (v_isSharedCheck_2392_ == 0)
{
lean_object* v_unused_2393_; lean_object* v_unused_2394_; lean_object* v_unused_2395_; lean_object* v_unused_2396_; lean_object* v_unused_2397_; lean_object* v_unused_2398_; lean_object* v_unused_2399_; lean_object* v_unused_2400_; 
v_unused_2393_ = lean_ctor_get(v_s_2320_, 7);
lean_dec(v_unused_2393_);
v_unused_2394_ = lean_ctor_get(v_s_2320_, 6);
lean_dec(v_unused_2394_);
v_unused_2395_ = lean_ctor_get(v_s_2320_, 5);
lean_dec(v_unused_2395_);
v_unused_2396_ = lean_ctor_get(v_s_2320_, 4);
lean_dec(v_unused_2396_);
v_unused_2397_ = lean_ctor_get(v_s_2320_, 3);
lean_dec(v_unused_2397_);
v_unused_2398_ = lean_ctor_get(v_s_2320_, 2);
lean_dec(v_unused_2398_);
v_unused_2399_ = lean_ctor_get(v_s_2320_, 1);
lean_dec(v_unused_2399_);
v_unused_2400_ = lean_ctor_get(v_s_2320_, 0);
lean_dec(v_unused_2400_);
v___x_2332_ = v_s_2320_;
v_isShared_2333_ = v_isSharedCheck_2392_;
goto v_resetjp_2331_;
}
else
{
lean_dec(v_s_2320_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2392_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v_v_2334_; lean_object* v_id_2335_; lean_object* v_ringId_x3f_2336_; lean_object* v_type_2337_; lean_object* v_u_2338_; lean_object* v_intModuleInst_2339_; lean_object* v_leInst_x3f_2340_; lean_object* v_ltInst_x3f_2341_; lean_object* v_lawfulOrderLTInst_x3f_2342_; lean_object* v_isPreorderInst_x3f_2343_; lean_object* v_orderedAddInst_x3f_2344_; lean_object* v_isLinearInst_x3f_2345_; lean_object* v_noNatDivInst_x3f_2346_; lean_object* v_ringInst_x3f_2347_; lean_object* v_commRingInst_x3f_2348_; lean_object* v_orderedRingInst_x3f_2349_; lean_object* v_fieldInst_x3f_2350_; lean_object* v_charInst_x3f_2351_; lean_object* v_zero_2352_; lean_object* v_ofNatZero_2353_; lean_object* v_one_x3f_2354_; lean_object* v_leFn_x3f_2355_; lean_object* v_ltFn_x3f_2356_; lean_object* v_addFn_2357_; lean_object* v_zsmulFn_2358_; lean_object* v_nsmulFn_2359_; lean_object* v_zsmulFn_x3f_2360_; lean_object* v_nsmulFn_x3f_2361_; lean_object* v_homomulFn_x3f_2362_; lean_object* v_subFn_2363_; lean_object* v_negFn_2364_; lean_object* v_vars_2365_; lean_object* v_varMap_2366_; lean_object* v_lowers_2367_; lean_object* v_uppers_2368_; lean_object* v_diseqs_2369_; lean_object* v_assignment_2370_; uint8_t v_caseSplits_2371_; lean_object* v_conflict_x3f_2372_; lean_object* v_diseqSplits_2373_; lean_object* v_elimEqs_2374_; lean_object* v_elimStack_2375_; lean_object* v_occurs_2376_; lean_object* v_ignored_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2391_; 
v_v_2334_ = lean_array_fget(v_structs_2321_, v_a_2317_);
v_id_2335_ = lean_ctor_get(v_v_2334_, 0);
v_ringId_x3f_2336_ = lean_ctor_get(v_v_2334_, 1);
v_type_2337_ = lean_ctor_get(v_v_2334_, 2);
v_u_2338_ = lean_ctor_get(v_v_2334_, 3);
v_intModuleInst_2339_ = lean_ctor_get(v_v_2334_, 4);
v_leInst_x3f_2340_ = lean_ctor_get(v_v_2334_, 5);
v_ltInst_x3f_2341_ = lean_ctor_get(v_v_2334_, 6);
v_lawfulOrderLTInst_x3f_2342_ = lean_ctor_get(v_v_2334_, 7);
v_isPreorderInst_x3f_2343_ = lean_ctor_get(v_v_2334_, 8);
v_orderedAddInst_x3f_2344_ = lean_ctor_get(v_v_2334_, 9);
v_isLinearInst_x3f_2345_ = lean_ctor_get(v_v_2334_, 10);
v_noNatDivInst_x3f_2346_ = lean_ctor_get(v_v_2334_, 11);
v_ringInst_x3f_2347_ = lean_ctor_get(v_v_2334_, 12);
v_commRingInst_x3f_2348_ = lean_ctor_get(v_v_2334_, 13);
v_orderedRingInst_x3f_2349_ = lean_ctor_get(v_v_2334_, 14);
v_fieldInst_x3f_2350_ = lean_ctor_get(v_v_2334_, 15);
v_charInst_x3f_2351_ = lean_ctor_get(v_v_2334_, 16);
v_zero_2352_ = lean_ctor_get(v_v_2334_, 17);
v_ofNatZero_2353_ = lean_ctor_get(v_v_2334_, 18);
v_one_x3f_2354_ = lean_ctor_get(v_v_2334_, 19);
v_leFn_x3f_2355_ = lean_ctor_get(v_v_2334_, 20);
v_ltFn_x3f_2356_ = lean_ctor_get(v_v_2334_, 21);
v_addFn_2357_ = lean_ctor_get(v_v_2334_, 22);
v_zsmulFn_2358_ = lean_ctor_get(v_v_2334_, 23);
v_nsmulFn_2359_ = lean_ctor_get(v_v_2334_, 24);
v_zsmulFn_x3f_2360_ = lean_ctor_get(v_v_2334_, 25);
v_nsmulFn_x3f_2361_ = lean_ctor_get(v_v_2334_, 26);
v_homomulFn_x3f_2362_ = lean_ctor_get(v_v_2334_, 27);
v_subFn_2363_ = lean_ctor_get(v_v_2334_, 28);
v_negFn_2364_ = lean_ctor_get(v_v_2334_, 29);
v_vars_2365_ = lean_ctor_get(v_v_2334_, 30);
v_varMap_2366_ = lean_ctor_get(v_v_2334_, 31);
v_lowers_2367_ = lean_ctor_get(v_v_2334_, 32);
v_uppers_2368_ = lean_ctor_get(v_v_2334_, 33);
v_diseqs_2369_ = lean_ctor_get(v_v_2334_, 34);
v_assignment_2370_ = lean_ctor_get(v_v_2334_, 35);
v_caseSplits_2371_ = lean_ctor_get_uint8(v_v_2334_, sizeof(void*)*42);
v_conflict_x3f_2372_ = lean_ctor_get(v_v_2334_, 36);
v_diseqSplits_2373_ = lean_ctor_get(v_v_2334_, 37);
v_elimEqs_2374_ = lean_ctor_get(v_v_2334_, 38);
v_elimStack_2375_ = lean_ctor_get(v_v_2334_, 39);
v_occurs_2376_ = lean_ctor_get(v_v_2334_, 40);
v_ignored_2377_ = lean_ctor_get(v_v_2334_, 41);
v_isSharedCheck_2391_ = !lean_is_exclusive(v_v_2334_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2379_ = v_v_2334_;
v_isShared_2380_ = v_isSharedCheck_2391_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_ignored_2377_);
lean_inc(v_occurs_2376_);
lean_inc(v_elimStack_2375_);
lean_inc(v_elimEqs_2374_);
lean_inc(v_diseqSplits_2373_);
lean_inc(v_conflict_x3f_2372_);
lean_inc(v_assignment_2370_);
lean_inc(v_diseqs_2369_);
lean_inc(v_uppers_2368_);
lean_inc(v_lowers_2367_);
lean_inc(v_varMap_2366_);
lean_inc(v_vars_2365_);
lean_inc(v_negFn_2364_);
lean_inc(v_subFn_2363_);
lean_inc(v_homomulFn_x3f_2362_);
lean_inc(v_nsmulFn_x3f_2361_);
lean_inc(v_zsmulFn_x3f_2360_);
lean_inc(v_nsmulFn_2359_);
lean_inc(v_zsmulFn_2358_);
lean_inc(v_addFn_2357_);
lean_inc(v_ltFn_x3f_2356_);
lean_inc(v_leFn_x3f_2355_);
lean_inc(v_one_x3f_2354_);
lean_inc(v_ofNatZero_2353_);
lean_inc(v_zero_2352_);
lean_inc(v_charInst_x3f_2351_);
lean_inc(v_fieldInst_x3f_2350_);
lean_inc(v_orderedRingInst_x3f_2349_);
lean_inc(v_commRingInst_x3f_2348_);
lean_inc(v_ringInst_x3f_2347_);
lean_inc(v_noNatDivInst_x3f_2346_);
lean_inc(v_isLinearInst_x3f_2345_);
lean_inc(v_orderedAddInst_x3f_2344_);
lean_inc(v_isPreorderInst_x3f_2343_);
lean_inc(v_lawfulOrderLTInst_x3f_2342_);
lean_inc(v_ltInst_x3f_2341_);
lean_inc(v_leInst_x3f_2340_);
lean_inc(v_intModuleInst_2339_);
lean_inc(v_u_2338_);
lean_inc(v_type_2337_);
lean_inc(v_ringId_x3f_2336_);
lean_inc(v_id_2335_);
lean_dec(v_v_2334_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2391_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v_xs_x27_2382_; lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2381_ = lean_box(0);
v_xs_x27_2382_ = lean_array_fset(v_structs_2321_, v_a_2317_, v___x_2381_);
v___x_2383_ = l_Lean_PersistentArray_set___redArg(v_lowers_2367_, v_y_2318_, v_fst_2319_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 32, v___x_2383_);
v___x_2385_ = v___x_2379_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_id_2335_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v_ringId_x3f_2336_);
lean_ctor_set(v_reuseFailAlloc_2390_, 2, v_type_2337_);
lean_ctor_set(v_reuseFailAlloc_2390_, 3, v_u_2338_);
lean_ctor_set(v_reuseFailAlloc_2390_, 4, v_intModuleInst_2339_);
lean_ctor_set(v_reuseFailAlloc_2390_, 5, v_leInst_x3f_2340_);
lean_ctor_set(v_reuseFailAlloc_2390_, 6, v_ltInst_x3f_2341_);
lean_ctor_set(v_reuseFailAlloc_2390_, 7, v_lawfulOrderLTInst_x3f_2342_);
lean_ctor_set(v_reuseFailAlloc_2390_, 8, v_isPreorderInst_x3f_2343_);
lean_ctor_set(v_reuseFailAlloc_2390_, 9, v_orderedAddInst_x3f_2344_);
lean_ctor_set(v_reuseFailAlloc_2390_, 10, v_isLinearInst_x3f_2345_);
lean_ctor_set(v_reuseFailAlloc_2390_, 11, v_noNatDivInst_x3f_2346_);
lean_ctor_set(v_reuseFailAlloc_2390_, 12, v_ringInst_x3f_2347_);
lean_ctor_set(v_reuseFailAlloc_2390_, 13, v_commRingInst_x3f_2348_);
lean_ctor_set(v_reuseFailAlloc_2390_, 14, v_orderedRingInst_x3f_2349_);
lean_ctor_set(v_reuseFailAlloc_2390_, 15, v_fieldInst_x3f_2350_);
lean_ctor_set(v_reuseFailAlloc_2390_, 16, v_charInst_x3f_2351_);
lean_ctor_set(v_reuseFailAlloc_2390_, 17, v_zero_2352_);
lean_ctor_set(v_reuseFailAlloc_2390_, 18, v_ofNatZero_2353_);
lean_ctor_set(v_reuseFailAlloc_2390_, 19, v_one_x3f_2354_);
lean_ctor_set(v_reuseFailAlloc_2390_, 20, v_leFn_x3f_2355_);
lean_ctor_set(v_reuseFailAlloc_2390_, 21, v_ltFn_x3f_2356_);
lean_ctor_set(v_reuseFailAlloc_2390_, 22, v_addFn_2357_);
lean_ctor_set(v_reuseFailAlloc_2390_, 23, v_zsmulFn_2358_);
lean_ctor_set(v_reuseFailAlloc_2390_, 24, v_nsmulFn_2359_);
lean_ctor_set(v_reuseFailAlloc_2390_, 25, v_zsmulFn_x3f_2360_);
lean_ctor_set(v_reuseFailAlloc_2390_, 26, v_nsmulFn_x3f_2361_);
lean_ctor_set(v_reuseFailAlloc_2390_, 27, v_homomulFn_x3f_2362_);
lean_ctor_set(v_reuseFailAlloc_2390_, 28, v_subFn_2363_);
lean_ctor_set(v_reuseFailAlloc_2390_, 29, v_negFn_2364_);
lean_ctor_set(v_reuseFailAlloc_2390_, 30, v_vars_2365_);
lean_ctor_set(v_reuseFailAlloc_2390_, 31, v_varMap_2366_);
lean_ctor_set(v_reuseFailAlloc_2390_, 32, v___x_2383_);
lean_ctor_set(v_reuseFailAlloc_2390_, 33, v_uppers_2368_);
lean_ctor_set(v_reuseFailAlloc_2390_, 34, v_diseqs_2369_);
lean_ctor_set(v_reuseFailAlloc_2390_, 35, v_assignment_2370_);
lean_ctor_set(v_reuseFailAlloc_2390_, 36, v_conflict_x3f_2372_);
lean_ctor_set(v_reuseFailAlloc_2390_, 37, v_diseqSplits_2373_);
lean_ctor_set(v_reuseFailAlloc_2390_, 38, v_elimEqs_2374_);
lean_ctor_set(v_reuseFailAlloc_2390_, 39, v_elimStack_2375_);
lean_ctor_set(v_reuseFailAlloc_2390_, 40, v_occurs_2376_);
lean_ctor_set(v_reuseFailAlloc_2390_, 41, v_ignored_2377_);
lean_ctor_set_uint8(v_reuseFailAlloc_2390_, sizeof(void*)*42, v_caseSplits_2371_);
v___x_2385_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2386_; lean_object* v___x_2388_; 
v___x_2386_ = lean_array_fset(v_xs_x27_2382_, v_a_2317_, v___x_2385_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2386_);
v___x_2388_ = v___x_2332_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_typeIdOf_2322_);
lean_ctor_set(v_reuseFailAlloc_2389_, 2, v_exprToStructId_2323_);
lean_ctor_set(v_reuseFailAlloc_2389_, 3, v_exprToStructIdEntries_2324_);
lean_ctor_set(v_reuseFailAlloc_2389_, 4, v_forbiddenNatModules_2325_);
lean_ctor_set(v_reuseFailAlloc_2389_, 5, v_natStructs_2326_);
lean_ctor_set(v_reuseFailAlloc_2389_, 6, v_natTypeIdOf_2327_);
lean_ctor_set(v_reuseFailAlloc_2389_, 7, v_exprToNatStructId_2328_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed(lean_object* v_a_2401_, lean_object* v_y_2402_, lean_object* v_fst_2403_, lean_object* v_s_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(v_a_2401_, v_y_2402_, v_fst_2403_, v_s_2404_);
lean_dec(v_y_2402_);
lean_dec(v_a_2401_);
return v_res_2405_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0(void){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object* v_a_2407_, lean_object* v_x_2408_, lean_object* v_c_2409_, lean_object* v_y_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2424_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2458_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2458_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2458_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
uint8_t v___x_2429_; 
v___x_2429_ = lean_unbox(v_a_2425_);
lean_dec(v_a_2425_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; 
lean_del_object(v___x_2427_);
v___x_2430_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___y_2433_; lean_object* v_lowers_2441_; lean_object* v_size_2442_; uint8_t v___x_2443_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref_known(v___x_2430_, 1);
v_lowers_2441_ = lean_ctor_get(v_a_2431_, 32);
lean_inc_ref(v_lowers_2441_);
lean_dec(v_a_2431_);
v_size_2442_ = lean_ctor_get(v_lowers_2441_, 2);
v___x_2443_ = lean_nat_dec_lt(v_y_2410_, v_size_2442_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; 
lean_dec_ref(v_lowers_2441_);
v___x_2444_ = l_outOfBounds___redArg(v___x_2423_);
v___y_2433_ = v___x_2444_;
goto v___jp_2432_;
}
else
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2423_, v_lowers_2441_, v_y_2410_);
lean_dec_ref(v_lowers_2441_);
v___y_2433_ = v___x_2445_;
goto v___jp_2432_;
}
v___jp_2432_:
{
lean_object* v___x_2434_; lean_object* v_fst_2435_; lean_object* v_snd_2436_; lean_object* v___f_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2434_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2408_, v___y_2433_);
lean_dec_ref(v___y_2433_);
v_fst_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_fst_2435_);
v_snd_2436_ = lean_ctor_get(v___x_2434_, 1);
lean_inc(v_snd_2436_);
lean_dec_ref(v___x_2434_);
lean_inc(v_a_2411_);
v___f_2437_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2437_, 0, v_a_2411_);
lean_closure_set(v___f_2437_, 1, v_y_2410_);
lean_closure_set(v___f_2437_, 2, v_fst_2435_);
v___x_2438_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2439_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2438_, v___f_2437_, v_a_2412_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v___x_2440_; 
lean_dec_ref_known(v___x_2439_, 1);
v___x_2440_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2407_, v_x_2408_, v_c_2409_, v_snd_2436_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
lean_dec(v_snd_2436_);
return v___x_2440_;
}
else
{
lean_dec(v_snd_2436_);
lean_dec_ref(v_c_2409_);
lean_dec(v_x_2408_);
lean_dec(v_a_2407_);
return v___x_2439_;
}
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec(v_y_2410_);
lean_dec_ref(v_c_2409_);
lean_dec(v_x_2408_);
lean_dec(v_a_2407_);
v_a_2446_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2430_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2430_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
else
{
lean_object* v___x_2454_; lean_object* v___x_2456_; 
lean_dec(v_y_2410_);
lean_dec_ref(v_c_2409_);
lean_dec(v_x_2408_);
lean_dec(v_a_2407_);
v___x_2454_ = lean_box(0);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2454_);
v___x_2456_ = v___x_2427_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec(v_y_2410_);
lean_dec_ref(v_c_2409_);
lean_dec(v_x_2408_);
lean_dec(v_a_2407_);
v_a_2459_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2424_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2424_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object* v_a_2467_, lean_object* v_x_2468_, lean_object* v_c_2469_, lean_object* v_y_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_2467_, v_x_2468_, v_c_2469_, v_y_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_);
lean_dec(v_a_2481_);
lean_dec_ref(v_a_2480_);
lean_dec(v_a_2479_);
lean_dec_ref(v_a_2478_);
lean_dec(v_a_2477_);
lean_dec_ref(v_a_2476_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
lean_dec(v_a_2473_);
lean_dec(v_a_2472_);
lean_dec(v_a_2471_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(lean_object* v_a_2484_, lean_object* v_y_2485_, lean_object* v_fst_2486_, lean_object* v_s_2487_){
_start:
{
lean_object* v_structs_2488_; lean_object* v_typeIdOf_2489_; lean_object* v_exprToStructId_2490_; lean_object* v_exprToStructIdEntries_2491_; lean_object* v_forbiddenNatModules_2492_; lean_object* v_natStructs_2493_; lean_object* v_natTypeIdOf_2494_; lean_object* v_exprToNatStructId_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; 
v_structs_2488_ = lean_ctor_get(v_s_2487_, 0);
v_typeIdOf_2489_ = lean_ctor_get(v_s_2487_, 1);
v_exprToStructId_2490_ = lean_ctor_get(v_s_2487_, 2);
v_exprToStructIdEntries_2491_ = lean_ctor_get(v_s_2487_, 3);
v_forbiddenNatModules_2492_ = lean_ctor_get(v_s_2487_, 4);
v_natStructs_2493_ = lean_ctor_get(v_s_2487_, 5);
v_natTypeIdOf_2494_ = lean_ctor_get(v_s_2487_, 6);
v_exprToNatStructId_2495_ = lean_ctor_get(v_s_2487_, 7);
v___x_2496_ = lean_array_get_size(v_structs_2488_);
v___x_2497_ = lean_nat_dec_lt(v_a_2484_, v___x_2496_);
if (v___x_2497_ == 0)
{
lean_dec_ref(v_fst_2486_);
return v_s_2487_;
}
else
{
lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2559_; 
lean_inc_ref(v_exprToNatStructId_2495_);
lean_inc_ref(v_natTypeIdOf_2494_);
lean_inc_ref(v_natStructs_2493_);
lean_inc_ref(v_forbiddenNatModules_2492_);
lean_inc_ref(v_exprToStructIdEntries_2491_);
lean_inc_ref(v_exprToStructId_2490_);
lean_inc_ref(v_typeIdOf_2489_);
lean_inc_ref(v_structs_2488_);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_s_2487_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; lean_object* v_unused_2561_; lean_object* v_unused_2562_; lean_object* v_unused_2563_; lean_object* v_unused_2564_; lean_object* v_unused_2565_; lean_object* v_unused_2566_; lean_object* v_unused_2567_; 
v_unused_2560_ = lean_ctor_get(v_s_2487_, 7);
lean_dec(v_unused_2560_);
v_unused_2561_ = lean_ctor_get(v_s_2487_, 6);
lean_dec(v_unused_2561_);
v_unused_2562_ = lean_ctor_get(v_s_2487_, 5);
lean_dec(v_unused_2562_);
v_unused_2563_ = lean_ctor_get(v_s_2487_, 4);
lean_dec(v_unused_2563_);
v_unused_2564_ = lean_ctor_get(v_s_2487_, 3);
lean_dec(v_unused_2564_);
v_unused_2565_ = lean_ctor_get(v_s_2487_, 2);
lean_dec(v_unused_2565_);
v_unused_2566_ = lean_ctor_get(v_s_2487_, 1);
lean_dec(v_unused_2566_);
v_unused_2567_ = lean_ctor_get(v_s_2487_, 0);
lean_dec(v_unused_2567_);
v___x_2499_ = v_s_2487_;
v_isShared_2500_ = v_isSharedCheck_2559_;
goto v_resetjp_2498_;
}
else
{
lean_dec(v_s_2487_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2559_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v_v_2501_; lean_object* v_id_2502_; lean_object* v_ringId_x3f_2503_; lean_object* v_type_2504_; lean_object* v_u_2505_; lean_object* v_intModuleInst_2506_; lean_object* v_leInst_x3f_2507_; lean_object* v_ltInst_x3f_2508_; lean_object* v_lawfulOrderLTInst_x3f_2509_; lean_object* v_isPreorderInst_x3f_2510_; lean_object* v_orderedAddInst_x3f_2511_; lean_object* v_isLinearInst_x3f_2512_; lean_object* v_noNatDivInst_x3f_2513_; lean_object* v_ringInst_x3f_2514_; lean_object* v_commRingInst_x3f_2515_; lean_object* v_orderedRingInst_x3f_2516_; lean_object* v_fieldInst_x3f_2517_; lean_object* v_charInst_x3f_2518_; lean_object* v_zero_2519_; lean_object* v_ofNatZero_2520_; lean_object* v_one_x3f_2521_; lean_object* v_leFn_x3f_2522_; lean_object* v_ltFn_x3f_2523_; lean_object* v_addFn_2524_; lean_object* v_zsmulFn_2525_; lean_object* v_nsmulFn_2526_; lean_object* v_zsmulFn_x3f_2527_; lean_object* v_nsmulFn_x3f_2528_; lean_object* v_homomulFn_x3f_2529_; lean_object* v_subFn_2530_; lean_object* v_negFn_2531_; lean_object* v_vars_2532_; lean_object* v_varMap_2533_; lean_object* v_lowers_2534_; lean_object* v_uppers_2535_; lean_object* v_diseqs_2536_; lean_object* v_assignment_2537_; uint8_t v_caseSplits_2538_; lean_object* v_conflict_x3f_2539_; lean_object* v_diseqSplits_2540_; lean_object* v_elimEqs_2541_; lean_object* v_elimStack_2542_; lean_object* v_occurs_2543_; lean_object* v_ignored_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2558_; 
v_v_2501_ = lean_array_fget(v_structs_2488_, v_a_2484_);
v_id_2502_ = lean_ctor_get(v_v_2501_, 0);
v_ringId_x3f_2503_ = lean_ctor_get(v_v_2501_, 1);
v_type_2504_ = lean_ctor_get(v_v_2501_, 2);
v_u_2505_ = lean_ctor_get(v_v_2501_, 3);
v_intModuleInst_2506_ = lean_ctor_get(v_v_2501_, 4);
v_leInst_x3f_2507_ = lean_ctor_get(v_v_2501_, 5);
v_ltInst_x3f_2508_ = lean_ctor_get(v_v_2501_, 6);
v_lawfulOrderLTInst_x3f_2509_ = lean_ctor_get(v_v_2501_, 7);
v_isPreorderInst_x3f_2510_ = lean_ctor_get(v_v_2501_, 8);
v_orderedAddInst_x3f_2511_ = lean_ctor_get(v_v_2501_, 9);
v_isLinearInst_x3f_2512_ = lean_ctor_get(v_v_2501_, 10);
v_noNatDivInst_x3f_2513_ = lean_ctor_get(v_v_2501_, 11);
v_ringInst_x3f_2514_ = lean_ctor_get(v_v_2501_, 12);
v_commRingInst_x3f_2515_ = lean_ctor_get(v_v_2501_, 13);
v_orderedRingInst_x3f_2516_ = lean_ctor_get(v_v_2501_, 14);
v_fieldInst_x3f_2517_ = lean_ctor_get(v_v_2501_, 15);
v_charInst_x3f_2518_ = lean_ctor_get(v_v_2501_, 16);
v_zero_2519_ = lean_ctor_get(v_v_2501_, 17);
v_ofNatZero_2520_ = lean_ctor_get(v_v_2501_, 18);
v_one_x3f_2521_ = lean_ctor_get(v_v_2501_, 19);
v_leFn_x3f_2522_ = lean_ctor_get(v_v_2501_, 20);
v_ltFn_x3f_2523_ = lean_ctor_get(v_v_2501_, 21);
v_addFn_2524_ = lean_ctor_get(v_v_2501_, 22);
v_zsmulFn_2525_ = lean_ctor_get(v_v_2501_, 23);
v_nsmulFn_2526_ = lean_ctor_get(v_v_2501_, 24);
v_zsmulFn_x3f_2527_ = lean_ctor_get(v_v_2501_, 25);
v_nsmulFn_x3f_2528_ = lean_ctor_get(v_v_2501_, 26);
v_homomulFn_x3f_2529_ = lean_ctor_get(v_v_2501_, 27);
v_subFn_2530_ = lean_ctor_get(v_v_2501_, 28);
v_negFn_2531_ = lean_ctor_get(v_v_2501_, 29);
v_vars_2532_ = lean_ctor_get(v_v_2501_, 30);
v_varMap_2533_ = lean_ctor_get(v_v_2501_, 31);
v_lowers_2534_ = lean_ctor_get(v_v_2501_, 32);
v_uppers_2535_ = lean_ctor_get(v_v_2501_, 33);
v_diseqs_2536_ = lean_ctor_get(v_v_2501_, 34);
v_assignment_2537_ = lean_ctor_get(v_v_2501_, 35);
v_caseSplits_2538_ = lean_ctor_get_uint8(v_v_2501_, sizeof(void*)*42);
v_conflict_x3f_2539_ = lean_ctor_get(v_v_2501_, 36);
v_diseqSplits_2540_ = lean_ctor_get(v_v_2501_, 37);
v_elimEqs_2541_ = lean_ctor_get(v_v_2501_, 38);
v_elimStack_2542_ = lean_ctor_get(v_v_2501_, 39);
v_occurs_2543_ = lean_ctor_get(v_v_2501_, 40);
v_ignored_2544_ = lean_ctor_get(v_v_2501_, 41);
v_isSharedCheck_2558_ = !lean_is_exclusive(v_v_2501_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2546_ = v_v_2501_;
v_isShared_2547_ = v_isSharedCheck_2558_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_ignored_2544_);
lean_inc(v_occurs_2543_);
lean_inc(v_elimStack_2542_);
lean_inc(v_elimEqs_2541_);
lean_inc(v_diseqSplits_2540_);
lean_inc(v_conflict_x3f_2539_);
lean_inc(v_assignment_2537_);
lean_inc(v_diseqs_2536_);
lean_inc(v_uppers_2535_);
lean_inc(v_lowers_2534_);
lean_inc(v_varMap_2533_);
lean_inc(v_vars_2532_);
lean_inc(v_negFn_2531_);
lean_inc(v_subFn_2530_);
lean_inc(v_homomulFn_x3f_2529_);
lean_inc(v_nsmulFn_x3f_2528_);
lean_inc(v_zsmulFn_x3f_2527_);
lean_inc(v_nsmulFn_2526_);
lean_inc(v_zsmulFn_2525_);
lean_inc(v_addFn_2524_);
lean_inc(v_ltFn_x3f_2523_);
lean_inc(v_leFn_x3f_2522_);
lean_inc(v_one_x3f_2521_);
lean_inc(v_ofNatZero_2520_);
lean_inc(v_zero_2519_);
lean_inc(v_charInst_x3f_2518_);
lean_inc(v_fieldInst_x3f_2517_);
lean_inc(v_orderedRingInst_x3f_2516_);
lean_inc(v_commRingInst_x3f_2515_);
lean_inc(v_ringInst_x3f_2514_);
lean_inc(v_noNatDivInst_x3f_2513_);
lean_inc(v_isLinearInst_x3f_2512_);
lean_inc(v_orderedAddInst_x3f_2511_);
lean_inc(v_isPreorderInst_x3f_2510_);
lean_inc(v_lawfulOrderLTInst_x3f_2509_);
lean_inc(v_ltInst_x3f_2508_);
lean_inc(v_leInst_x3f_2507_);
lean_inc(v_intModuleInst_2506_);
lean_inc(v_u_2505_);
lean_inc(v_type_2504_);
lean_inc(v_ringId_x3f_2503_);
lean_inc(v_id_2502_);
lean_dec(v_v_2501_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2558_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2548_; lean_object* v_xs_x27_2549_; lean_object* v___x_2550_; lean_object* v___x_2552_; 
v___x_2548_ = lean_box(0);
v_xs_x27_2549_ = lean_array_fset(v_structs_2488_, v_a_2484_, v___x_2548_);
v___x_2550_ = l_Lean_PersistentArray_set___redArg(v_uppers_2535_, v_y_2485_, v_fst_2486_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 33, v___x_2550_);
v___x_2552_ = v___x_2546_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_id_2502_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_ringId_x3f_2503_);
lean_ctor_set(v_reuseFailAlloc_2557_, 2, v_type_2504_);
lean_ctor_set(v_reuseFailAlloc_2557_, 3, v_u_2505_);
lean_ctor_set(v_reuseFailAlloc_2557_, 4, v_intModuleInst_2506_);
lean_ctor_set(v_reuseFailAlloc_2557_, 5, v_leInst_x3f_2507_);
lean_ctor_set(v_reuseFailAlloc_2557_, 6, v_ltInst_x3f_2508_);
lean_ctor_set(v_reuseFailAlloc_2557_, 7, v_lawfulOrderLTInst_x3f_2509_);
lean_ctor_set(v_reuseFailAlloc_2557_, 8, v_isPreorderInst_x3f_2510_);
lean_ctor_set(v_reuseFailAlloc_2557_, 9, v_orderedAddInst_x3f_2511_);
lean_ctor_set(v_reuseFailAlloc_2557_, 10, v_isLinearInst_x3f_2512_);
lean_ctor_set(v_reuseFailAlloc_2557_, 11, v_noNatDivInst_x3f_2513_);
lean_ctor_set(v_reuseFailAlloc_2557_, 12, v_ringInst_x3f_2514_);
lean_ctor_set(v_reuseFailAlloc_2557_, 13, v_commRingInst_x3f_2515_);
lean_ctor_set(v_reuseFailAlloc_2557_, 14, v_orderedRingInst_x3f_2516_);
lean_ctor_set(v_reuseFailAlloc_2557_, 15, v_fieldInst_x3f_2517_);
lean_ctor_set(v_reuseFailAlloc_2557_, 16, v_charInst_x3f_2518_);
lean_ctor_set(v_reuseFailAlloc_2557_, 17, v_zero_2519_);
lean_ctor_set(v_reuseFailAlloc_2557_, 18, v_ofNatZero_2520_);
lean_ctor_set(v_reuseFailAlloc_2557_, 19, v_one_x3f_2521_);
lean_ctor_set(v_reuseFailAlloc_2557_, 20, v_leFn_x3f_2522_);
lean_ctor_set(v_reuseFailAlloc_2557_, 21, v_ltFn_x3f_2523_);
lean_ctor_set(v_reuseFailAlloc_2557_, 22, v_addFn_2524_);
lean_ctor_set(v_reuseFailAlloc_2557_, 23, v_zsmulFn_2525_);
lean_ctor_set(v_reuseFailAlloc_2557_, 24, v_nsmulFn_2526_);
lean_ctor_set(v_reuseFailAlloc_2557_, 25, v_zsmulFn_x3f_2527_);
lean_ctor_set(v_reuseFailAlloc_2557_, 26, v_nsmulFn_x3f_2528_);
lean_ctor_set(v_reuseFailAlloc_2557_, 27, v_homomulFn_x3f_2529_);
lean_ctor_set(v_reuseFailAlloc_2557_, 28, v_subFn_2530_);
lean_ctor_set(v_reuseFailAlloc_2557_, 29, v_negFn_2531_);
lean_ctor_set(v_reuseFailAlloc_2557_, 30, v_vars_2532_);
lean_ctor_set(v_reuseFailAlloc_2557_, 31, v_varMap_2533_);
lean_ctor_set(v_reuseFailAlloc_2557_, 32, v_lowers_2534_);
lean_ctor_set(v_reuseFailAlloc_2557_, 33, v___x_2550_);
lean_ctor_set(v_reuseFailAlloc_2557_, 34, v_diseqs_2536_);
lean_ctor_set(v_reuseFailAlloc_2557_, 35, v_assignment_2537_);
lean_ctor_set(v_reuseFailAlloc_2557_, 36, v_conflict_x3f_2539_);
lean_ctor_set(v_reuseFailAlloc_2557_, 37, v_diseqSplits_2540_);
lean_ctor_set(v_reuseFailAlloc_2557_, 38, v_elimEqs_2541_);
lean_ctor_set(v_reuseFailAlloc_2557_, 39, v_elimStack_2542_);
lean_ctor_set(v_reuseFailAlloc_2557_, 40, v_occurs_2543_);
lean_ctor_set(v_reuseFailAlloc_2557_, 41, v_ignored_2544_);
lean_ctor_set_uint8(v_reuseFailAlloc_2557_, sizeof(void*)*42, v_caseSplits_2538_);
v___x_2552_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2553_ = lean_array_fset(v_xs_x27_2549_, v_a_2484_, v___x_2552_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 0, v___x_2553_);
v___x_2555_ = v___x_2499_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2553_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v_typeIdOf_2489_);
lean_ctor_set(v_reuseFailAlloc_2556_, 2, v_exprToStructId_2490_);
lean_ctor_set(v_reuseFailAlloc_2556_, 3, v_exprToStructIdEntries_2491_);
lean_ctor_set(v_reuseFailAlloc_2556_, 4, v_forbiddenNatModules_2492_);
lean_ctor_set(v_reuseFailAlloc_2556_, 5, v_natStructs_2493_);
lean_ctor_set(v_reuseFailAlloc_2556_, 6, v_natTypeIdOf_2494_);
lean_ctor_set(v_reuseFailAlloc_2556_, 7, v_exprToNatStructId_2495_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed(lean_object* v_a_2568_, lean_object* v_y_2569_, lean_object* v_fst_2570_, lean_object* v_s_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(v_a_2568_, v_y_2569_, v_fst_2570_, v_s_2571_);
lean_dec(v_y_2569_);
lean_dec(v_a_2568_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object* v_a_2573_, lean_object* v_x_2574_, lean_object* v_c_2575_, lean_object* v_y_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2589_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2590_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2624_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2624_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2624_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
uint8_t v___x_2595_; 
v___x_2595_ = lean_unbox(v_a_2591_);
lean_dec(v_a_2591_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; 
lean_del_object(v___x_2593_);
v___x_2596_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v___y_2599_; lean_object* v_uppers_2607_; lean_object* v_size_2608_; uint8_t v___x_2609_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_a_2597_);
lean_dec_ref_known(v___x_2596_, 1);
v_uppers_2607_ = lean_ctor_get(v_a_2597_, 33);
lean_inc_ref(v_uppers_2607_);
lean_dec(v_a_2597_);
v_size_2608_ = lean_ctor_get(v_uppers_2607_, 2);
v___x_2609_ = lean_nat_dec_lt(v_y_2576_, v_size_2608_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; 
lean_dec_ref(v_uppers_2607_);
v___x_2610_ = l_outOfBounds___redArg(v___x_2589_);
v___y_2599_ = v___x_2610_;
goto v___jp_2598_;
}
else
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2589_, v_uppers_2607_, v_y_2576_);
lean_dec_ref(v_uppers_2607_);
v___y_2599_ = v___x_2611_;
goto v___jp_2598_;
}
v___jp_2598_:
{
lean_object* v___x_2600_; lean_object* v_fst_2601_; lean_object* v_snd_2602_; lean_object* v___f_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2600_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2574_, v___y_2599_);
lean_dec_ref(v___y_2599_);
v_fst_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_fst_2601_);
v_snd_2602_ = lean_ctor_get(v___x_2600_, 1);
lean_inc(v_snd_2602_);
lean_dec_ref(v___x_2600_);
lean_inc(v_a_2577_);
v___f_2603_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2603_, 0, v_a_2577_);
lean_closure_set(v___f_2603_, 1, v_y_2576_);
lean_closure_set(v___f_2603_, 2, v_fst_2601_);
v___x_2604_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2605_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2604_, v___f_2603_, v_a_2578_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v___x_2606_; 
lean_dec_ref_known(v___x_2605_, 1);
v___x_2606_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2573_, v_x_2574_, v_c_2575_, v_snd_2602_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
lean_dec(v_snd_2602_);
return v___x_2606_;
}
else
{
lean_dec(v_snd_2602_);
lean_dec_ref(v_c_2575_);
lean_dec(v_x_2574_);
lean_dec(v_a_2573_);
return v___x_2605_;
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec(v_y_2576_);
lean_dec_ref(v_c_2575_);
lean_dec(v_x_2574_);
lean_dec(v_a_2573_);
v_a_2612_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2596_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2596_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2622_; 
lean_dec(v_y_2576_);
lean_dec_ref(v_c_2575_);
lean_dec(v_x_2574_);
lean_dec(v_a_2573_);
v___x_2620_ = lean_box(0);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2620_);
v___x_2622_ = v___x_2593_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v_y_2576_);
lean_dec_ref(v_c_2575_);
lean_dec(v_x_2574_);
lean_dec(v_a_2573_);
v_a_2625_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2590_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2590_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object* v_a_2633_, lean_object* v_x_2634_, lean_object* v_c_2635_, lean_object* v_y_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_2633_, v_x_2634_, v_c_2635_, v_y_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec(v_a_2639_);
lean_dec(v_a_2638_);
lean_dec(v_a_2637_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(lean_object* v___y_2650_, lean_object* v_a_2651_, lean_object* v_s_2652_){
_start:
{
lean_object* v_structs_2653_; lean_object* v_typeIdOf_2654_; lean_object* v_exprToStructId_2655_; lean_object* v_exprToStructIdEntries_2656_; lean_object* v_forbiddenNatModules_2657_; lean_object* v_natStructs_2658_; lean_object* v_natTypeIdOf_2659_; lean_object* v_exprToNatStructId_2660_; lean_object* v___x_2661_; uint8_t v___x_2662_; 
v_structs_2653_ = lean_ctor_get(v_s_2652_, 0);
v_typeIdOf_2654_ = lean_ctor_get(v_s_2652_, 1);
v_exprToStructId_2655_ = lean_ctor_get(v_s_2652_, 2);
v_exprToStructIdEntries_2656_ = lean_ctor_get(v_s_2652_, 3);
v_forbiddenNatModules_2657_ = lean_ctor_get(v_s_2652_, 4);
v_natStructs_2658_ = lean_ctor_get(v_s_2652_, 5);
v_natTypeIdOf_2659_ = lean_ctor_get(v_s_2652_, 6);
v_exprToNatStructId_2660_ = lean_ctor_get(v_s_2652_, 7);
v___x_2661_ = lean_array_get_size(v_structs_2653_);
v___x_2662_ = lean_nat_dec_lt(v___y_2650_, v___x_2661_);
if (v___x_2662_ == 0)
{
lean_dec_ref(v_a_2651_);
return v_s_2652_;
}
else
{
lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2724_; 
lean_inc_ref(v_exprToNatStructId_2660_);
lean_inc_ref(v_natTypeIdOf_2659_);
lean_inc_ref(v_natStructs_2658_);
lean_inc_ref(v_forbiddenNatModules_2657_);
lean_inc_ref(v_exprToStructIdEntries_2656_);
lean_inc_ref(v_exprToStructId_2655_);
lean_inc_ref(v_typeIdOf_2654_);
lean_inc_ref(v_structs_2653_);
v_isSharedCheck_2724_ = !lean_is_exclusive(v_s_2652_);
if (v_isSharedCheck_2724_ == 0)
{
lean_object* v_unused_2725_; lean_object* v_unused_2726_; lean_object* v_unused_2727_; lean_object* v_unused_2728_; lean_object* v_unused_2729_; lean_object* v_unused_2730_; lean_object* v_unused_2731_; lean_object* v_unused_2732_; 
v_unused_2725_ = lean_ctor_get(v_s_2652_, 7);
lean_dec(v_unused_2725_);
v_unused_2726_ = lean_ctor_get(v_s_2652_, 6);
lean_dec(v_unused_2726_);
v_unused_2727_ = lean_ctor_get(v_s_2652_, 5);
lean_dec(v_unused_2727_);
v_unused_2728_ = lean_ctor_get(v_s_2652_, 4);
lean_dec(v_unused_2728_);
v_unused_2729_ = lean_ctor_get(v_s_2652_, 3);
lean_dec(v_unused_2729_);
v_unused_2730_ = lean_ctor_get(v_s_2652_, 2);
lean_dec(v_unused_2730_);
v_unused_2731_ = lean_ctor_get(v_s_2652_, 1);
lean_dec(v_unused_2731_);
v_unused_2732_ = lean_ctor_get(v_s_2652_, 0);
lean_dec(v_unused_2732_);
v___x_2664_ = v_s_2652_;
v_isShared_2665_ = v_isSharedCheck_2724_;
goto v_resetjp_2663_;
}
else
{
lean_dec(v_s_2652_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2724_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v_v_2666_; lean_object* v_id_2667_; lean_object* v_ringId_x3f_2668_; lean_object* v_type_2669_; lean_object* v_u_2670_; lean_object* v_intModuleInst_2671_; lean_object* v_leInst_x3f_2672_; lean_object* v_ltInst_x3f_2673_; lean_object* v_lawfulOrderLTInst_x3f_2674_; lean_object* v_isPreorderInst_x3f_2675_; lean_object* v_orderedAddInst_x3f_2676_; lean_object* v_isLinearInst_x3f_2677_; lean_object* v_noNatDivInst_x3f_2678_; lean_object* v_ringInst_x3f_2679_; lean_object* v_commRingInst_x3f_2680_; lean_object* v_orderedRingInst_x3f_2681_; lean_object* v_fieldInst_x3f_2682_; lean_object* v_charInst_x3f_2683_; lean_object* v_zero_2684_; lean_object* v_ofNatZero_2685_; lean_object* v_one_x3f_2686_; lean_object* v_leFn_x3f_2687_; lean_object* v_ltFn_x3f_2688_; lean_object* v_addFn_2689_; lean_object* v_zsmulFn_2690_; lean_object* v_nsmulFn_2691_; lean_object* v_zsmulFn_x3f_2692_; lean_object* v_nsmulFn_x3f_2693_; lean_object* v_homomulFn_x3f_2694_; lean_object* v_subFn_2695_; lean_object* v_negFn_2696_; lean_object* v_vars_2697_; lean_object* v_varMap_2698_; lean_object* v_lowers_2699_; lean_object* v_uppers_2700_; lean_object* v_diseqs_2701_; lean_object* v_assignment_2702_; uint8_t v_caseSplits_2703_; lean_object* v_conflict_x3f_2704_; lean_object* v_diseqSplits_2705_; lean_object* v_elimEqs_2706_; lean_object* v_elimStack_2707_; lean_object* v_occurs_2708_; lean_object* v_ignored_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2723_; 
v_v_2666_ = lean_array_fget(v_structs_2653_, v___y_2650_);
v_id_2667_ = lean_ctor_get(v_v_2666_, 0);
v_ringId_x3f_2668_ = lean_ctor_get(v_v_2666_, 1);
v_type_2669_ = lean_ctor_get(v_v_2666_, 2);
v_u_2670_ = lean_ctor_get(v_v_2666_, 3);
v_intModuleInst_2671_ = lean_ctor_get(v_v_2666_, 4);
v_leInst_x3f_2672_ = lean_ctor_get(v_v_2666_, 5);
v_ltInst_x3f_2673_ = lean_ctor_get(v_v_2666_, 6);
v_lawfulOrderLTInst_x3f_2674_ = lean_ctor_get(v_v_2666_, 7);
v_isPreorderInst_x3f_2675_ = lean_ctor_get(v_v_2666_, 8);
v_orderedAddInst_x3f_2676_ = lean_ctor_get(v_v_2666_, 9);
v_isLinearInst_x3f_2677_ = lean_ctor_get(v_v_2666_, 10);
v_noNatDivInst_x3f_2678_ = lean_ctor_get(v_v_2666_, 11);
v_ringInst_x3f_2679_ = lean_ctor_get(v_v_2666_, 12);
v_commRingInst_x3f_2680_ = lean_ctor_get(v_v_2666_, 13);
v_orderedRingInst_x3f_2681_ = lean_ctor_get(v_v_2666_, 14);
v_fieldInst_x3f_2682_ = lean_ctor_get(v_v_2666_, 15);
v_charInst_x3f_2683_ = lean_ctor_get(v_v_2666_, 16);
v_zero_2684_ = lean_ctor_get(v_v_2666_, 17);
v_ofNatZero_2685_ = lean_ctor_get(v_v_2666_, 18);
v_one_x3f_2686_ = lean_ctor_get(v_v_2666_, 19);
v_leFn_x3f_2687_ = lean_ctor_get(v_v_2666_, 20);
v_ltFn_x3f_2688_ = lean_ctor_get(v_v_2666_, 21);
v_addFn_2689_ = lean_ctor_get(v_v_2666_, 22);
v_zsmulFn_2690_ = lean_ctor_get(v_v_2666_, 23);
v_nsmulFn_2691_ = lean_ctor_get(v_v_2666_, 24);
v_zsmulFn_x3f_2692_ = lean_ctor_get(v_v_2666_, 25);
v_nsmulFn_x3f_2693_ = lean_ctor_get(v_v_2666_, 26);
v_homomulFn_x3f_2694_ = lean_ctor_get(v_v_2666_, 27);
v_subFn_2695_ = lean_ctor_get(v_v_2666_, 28);
v_negFn_2696_ = lean_ctor_get(v_v_2666_, 29);
v_vars_2697_ = lean_ctor_get(v_v_2666_, 30);
v_varMap_2698_ = lean_ctor_get(v_v_2666_, 31);
v_lowers_2699_ = lean_ctor_get(v_v_2666_, 32);
v_uppers_2700_ = lean_ctor_get(v_v_2666_, 33);
v_diseqs_2701_ = lean_ctor_get(v_v_2666_, 34);
v_assignment_2702_ = lean_ctor_get(v_v_2666_, 35);
v_caseSplits_2703_ = lean_ctor_get_uint8(v_v_2666_, sizeof(void*)*42);
v_conflict_x3f_2704_ = lean_ctor_get(v_v_2666_, 36);
v_diseqSplits_2705_ = lean_ctor_get(v_v_2666_, 37);
v_elimEqs_2706_ = lean_ctor_get(v_v_2666_, 38);
v_elimStack_2707_ = lean_ctor_get(v_v_2666_, 39);
v_occurs_2708_ = lean_ctor_get(v_v_2666_, 40);
v_ignored_2709_ = lean_ctor_get(v_v_2666_, 41);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_v_2666_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2711_ = v_v_2666_;
v_isShared_2712_ = v_isSharedCheck_2723_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_ignored_2709_);
lean_inc(v_occurs_2708_);
lean_inc(v_elimStack_2707_);
lean_inc(v_elimEqs_2706_);
lean_inc(v_diseqSplits_2705_);
lean_inc(v_conflict_x3f_2704_);
lean_inc(v_assignment_2702_);
lean_inc(v_diseqs_2701_);
lean_inc(v_uppers_2700_);
lean_inc(v_lowers_2699_);
lean_inc(v_varMap_2698_);
lean_inc(v_vars_2697_);
lean_inc(v_negFn_2696_);
lean_inc(v_subFn_2695_);
lean_inc(v_homomulFn_x3f_2694_);
lean_inc(v_nsmulFn_x3f_2693_);
lean_inc(v_zsmulFn_x3f_2692_);
lean_inc(v_nsmulFn_2691_);
lean_inc(v_zsmulFn_2690_);
lean_inc(v_addFn_2689_);
lean_inc(v_ltFn_x3f_2688_);
lean_inc(v_leFn_x3f_2687_);
lean_inc(v_one_x3f_2686_);
lean_inc(v_ofNatZero_2685_);
lean_inc(v_zero_2684_);
lean_inc(v_charInst_x3f_2683_);
lean_inc(v_fieldInst_x3f_2682_);
lean_inc(v_orderedRingInst_x3f_2681_);
lean_inc(v_commRingInst_x3f_2680_);
lean_inc(v_ringInst_x3f_2679_);
lean_inc(v_noNatDivInst_x3f_2678_);
lean_inc(v_isLinearInst_x3f_2677_);
lean_inc(v_orderedAddInst_x3f_2676_);
lean_inc(v_isPreorderInst_x3f_2675_);
lean_inc(v_lawfulOrderLTInst_x3f_2674_);
lean_inc(v_ltInst_x3f_2673_);
lean_inc(v_leInst_x3f_2672_);
lean_inc(v_intModuleInst_2671_);
lean_inc(v_u_2670_);
lean_inc(v_type_2669_);
lean_inc(v_ringId_x3f_2668_);
lean_inc(v_id_2667_);
lean_dec(v_v_2666_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2723_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v_xs_x27_2714_; lean_object* v___x_2715_; lean_object* v___x_2717_; 
v___x_2713_ = lean_box(0);
v_xs_x27_2714_ = lean_array_fset(v_structs_2653_, v___y_2650_, v___x_2713_);
v___x_2715_ = l_Lean_PersistentArray_push___redArg(v_ignored_2709_, v_a_2651_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 41, v___x_2715_);
v___x_2717_ = v___x_2711_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_id_2667_);
lean_ctor_set(v_reuseFailAlloc_2722_, 1, v_ringId_x3f_2668_);
lean_ctor_set(v_reuseFailAlloc_2722_, 2, v_type_2669_);
lean_ctor_set(v_reuseFailAlloc_2722_, 3, v_u_2670_);
lean_ctor_set(v_reuseFailAlloc_2722_, 4, v_intModuleInst_2671_);
lean_ctor_set(v_reuseFailAlloc_2722_, 5, v_leInst_x3f_2672_);
lean_ctor_set(v_reuseFailAlloc_2722_, 6, v_ltInst_x3f_2673_);
lean_ctor_set(v_reuseFailAlloc_2722_, 7, v_lawfulOrderLTInst_x3f_2674_);
lean_ctor_set(v_reuseFailAlloc_2722_, 8, v_isPreorderInst_x3f_2675_);
lean_ctor_set(v_reuseFailAlloc_2722_, 9, v_orderedAddInst_x3f_2676_);
lean_ctor_set(v_reuseFailAlloc_2722_, 10, v_isLinearInst_x3f_2677_);
lean_ctor_set(v_reuseFailAlloc_2722_, 11, v_noNatDivInst_x3f_2678_);
lean_ctor_set(v_reuseFailAlloc_2722_, 12, v_ringInst_x3f_2679_);
lean_ctor_set(v_reuseFailAlloc_2722_, 13, v_commRingInst_x3f_2680_);
lean_ctor_set(v_reuseFailAlloc_2722_, 14, v_orderedRingInst_x3f_2681_);
lean_ctor_set(v_reuseFailAlloc_2722_, 15, v_fieldInst_x3f_2682_);
lean_ctor_set(v_reuseFailAlloc_2722_, 16, v_charInst_x3f_2683_);
lean_ctor_set(v_reuseFailAlloc_2722_, 17, v_zero_2684_);
lean_ctor_set(v_reuseFailAlloc_2722_, 18, v_ofNatZero_2685_);
lean_ctor_set(v_reuseFailAlloc_2722_, 19, v_one_x3f_2686_);
lean_ctor_set(v_reuseFailAlloc_2722_, 20, v_leFn_x3f_2687_);
lean_ctor_set(v_reuseFailAlloc_2722_, 21, v_ltFn_x3f_2688_);
lean_ctor_set(v_reuseFailAlloc_2722_, 22, v_addFn_2689_);
lean_ctor_set(v_reuseFailAlloc_2722_, 23, v_zsmulFn_2690_);
lean_ctor_set(v_reuseFailAlloc_2722_, 24, v_nsmulFn_2691_);
lean_ctor_set(v_reuseFailAlloc_2722_, 25, v_zsmulFn_x3f_2692_);
lean_ctor_set(v_reuseFailAlloc_2722_, 26, v_nsmulFn_x3f_2693_);
lean_ctor_set(v_reuseFailAlloc_2722_, 27, v_homomulFn_x3f_2694_);
lean_ctor_set(v_reuseFailAlloc_2722_, 28, v_subFn_2695_);
lean_ctor_set(v_reuseFailAlloc_2722_, 29, v_negFn_2696_);
lean_ctor_set(v_reuseFailAlloc_2722_, 30, v_vars_2697_);
lean_ctor_set(v_reuseFailAlloc_2722_, 31, v_varMap_2698_);
lean_ctor_set(v_reuseFailAlloc_2722_, 32, v_lowers_2699_);
lean_ctor_set(v_reuseFailAlloc_2722_, 33, v_uppers_2700_);
lean_ctor_set(v_reuseFailAlloc_2722_, 34, v_diseqs_2701_);
lean_ctor_set(v_reuseFailAlloc_2722_, 35, v_assignment_2702_);
lean_ctor_set(v_reuseFailAlloc_2722_, 36, v_conflict_x3f_2704_);
lean_ctor_set(v_reuseFailAlloc_2722_, 37, v_diseqSplits_2705_);
lean_ctor_set(v_reuseFailAlloc_2722_, 38, v_elimEqs_2706_);
lean_ctor_set(v_reuseFailAlloc_2722_, 39, v_elimStack_2707_);
lean_ctor_set(v_reuseFailAlloc_2722_, 40, v_occurs_2708_);
lean_ctor_set(v_reuseFailAlloc_2722_, 41, v___x_2715_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, sizeof(void*)*42, v_caseSplits_2703_);
v___x_2717_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
lean_object* v___x_2718_; lean_object* v___x_2720_; 
v___x_2718_ = lean_array_fset(v_xs_x27_2714_, v___y_2650_, v___x_2717_);
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v___x_2718_);
v___x_2720_ = v___x_2664_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2718_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v_typeIdOf_2654_);
lean_ctor_set(v_reuseFailAlloc_2721_, 2, v_exprToStructId_2655_);
lean_ctor_set(v_reuseFailAlloc_2721_, 3, v_exprToStructIdEntries_2656_);
lean_ctor_set(v_reuseFailAlloc_2721_, 4, v_forbiddenNatModules_2657_);
lean_ctor_set(v_reuseFailAlloc_2721_, 5, v_natStructs_2658_);
lean_ctor_set(v_reuseFailAlloc_2721_, 6, v_natTypeIdOf_2659_);
lean_ctor_set(v_reuseFailAlloc_2721_, 7, v_exprToNatStructId_2660_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed(lean_object* v___y_2733_, lean_object* v_a_2734_, lean_object* v_s_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(v___y_2733_, v_a_2734_, v_s_2735_);
lean_dec(v___y_2733_);
return v_res_2736_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3(void){
_start:
{
lean_object* v_cls_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v_cls_2744_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2745_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_2746_ = l_Lean_Name_append(v___x_2745_, v_cls_2744_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object* v_c_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v_toCold_2785_; lean_object* v_options_2786_; uint8_t v_hasTrace_2787_; 
v_toCold_2785_ = lean_ctor_get(v_a_2757_, 0);
v_options_2786_ = lean_ctor_get(v_toCold_2785_, 2);
v_hasTrace_2787_ = lean_ctor_get_uint8(v_options_2786_, sizeof(void*)*1);
if (v_hasTrace_2787_ == 0)
{
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
v___y_2771_ = v_a_2758_;
goto v___jp_2760_;
}
else
{
lean_object* v_inheritedTraceOptions_2788_; lean_object* v_cls_2789_; lean_object* v___x_2790_; uint8_t v___x_2791_; 
v_inheritedTraceOptions_2788_ = lean_ctor_get(v_toCold_2785_, 11);
v_cls_2789_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2790_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3);
v___x_2791_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2788_, v_options_2786_, v___x_2790_);
if (v___x_2791_ == 0)
{
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
v___y_2771_ = v_a_2758_;
goto v___jp_2760_;
}
else
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2792_, 1);
v___x_2794_ = l_Lean_MessageData_ofExpr(v_a_2793_);
v___x_2795_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_2789_, v___x_2794_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_dec_ref_known(v___x_2795_, 1);
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
v___y_2771_ = v_a_2758_;
goto v___jp_2760_;
}
else
{
return v___x_2795_;
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
v_a_2796_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2792_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2792_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
}
v___jp_2760_:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2747_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; lean_object* v___f_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_a_2773_);
lean_dec_ref_known(v___x_2772_, 1);
lean_inc(v___y_2761_);
v___f_2774_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2774_, 0, v___y_2761_);
lean_closure_set(v___f_2774_, 1, v_a_2773_);
v___x_2775_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2776_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2775_, v___f_2774_, v___y_2762_);
return v___x_2776_;
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
v_a_2777_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2772_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2772_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object* v_c_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_);
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2813_);
lean_dec_ref(v_a_2812_);
lean_dec(v_a_2811_);
lean_dec_ref(v_a_2810_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
lean_dec(v_a_2807_);
lean_dec(v_a_2806_);
lean_dec(v_a_2805_);
lean_dec_ref(v_c_2804_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object* v_c_u2082_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_){
_start:
{
lean_object* v_p_2831_; lean_object* v_toCold_2832_; lean_object* v_currRecDepth_2833_; lean_object* v_ref_2834_; uint16_t v_optionFlags_2835_; uint8_t v_suppressElabErrors_2836_; uint8_t v_checkDeprecated_2837_; uint8_t v_isRecordingDeps_2838_; lean_object* v_maxRecDepth_2890_; lean_object* v___x_2891_; uint8_t v___x_2892_; 
v_p_2831_ = lean_ctor_get(v_c_u2082_2818_, 0);
v_toCold_2832_ = lean_ctor_get(v_a_2828_, 0);
lean_inc_ref(v_toCold_2832_);
v_currRecDepth_2833_ = lean_ctor_get(v_a_2828_, 1);
lean_inc(v_currRecDepth_2833_);
v_ref_2834_ = lean_ctor_get(v_a_2828_, 2);
lean_inc(v_ref_2834_);
v_optionFlags_2835_ = lean_ctor_get_uint16(v_a_2828_, sizeof(void*)*3);
v_suppressElabErrors_2836_ = lean_ctor_get_uint8(v_a_2828_, sizeof(void*)*3 + 2);
v_checkDeprecated_2837_ = lean_ctor_get_uint8(v_a_2828_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2838_ = lean_ctor_get_uint8(v_a_2828_, sizeof(void*)*3 + 4);
lean_dec_ref(v_a_2828_);
v_maxRecDepth_2890_ = lean_ctor_get(v_toCold_2832_, 3);
v___x_2891_ = lean_unsigned_to_nat(0u);
v___x_2892_ = lean_nat_dec_eq(v_maxRecDepth_2890_, v___x_2891_);
if (v___x_2892_ == 0)
{
uint8_t v___x_2893_; 
v___x_2893_ = lean_nat_dec_eq(v_currRecDepth_2833_, v_maxRecDepth_2890_);
if (v___x_2893_ == 0)
{
goto v___jp_2839_;
}
else
{
lean_object* v___x_2894_; 
lean_dec(v_currRecDepth_2833_);
lean_dec_ref(v_toCold_2832_);
lean_dec_ref(v_c_u2082_2818_);
v___x_2894_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_2834_);
return v___x_2894_;
}
}
else
{
goto v___jp_2839_;
}
v___jp_2839_:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2840_ = lean_unsigned_to_nat(1u);
v___x_2841_ = lean_nat_add(v_currRecDepth_2833_, v___x_2840_);
lean_dec(v_currRecDepth_2833_);
v___x_2842_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2842_, 0, v_toCold_2832_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
lean_ctor_set(v___x_2842_, 2, v_ref_2834_);
lean_ctor_set_uint16(v___x_2842_, sizeof(void*)*3, v_optionFlags_2835_);
lean_ctor_set_uint8(v___x_2842_, sizeof(void*)*3 + 2, v_suppressElabErrors_2836_);
lean_ctor_set_uint8(v___x_2842_, sizeof(void*)*3 + 3, v_checkDeprecated_2837_);
lean_ctor_set_uint8(v___x_2842_, sizeof(void*)*3 + 4, v_isRecordingDeps_2838_);
v___x_2843_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2831_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v___x_2842_, v_a_2829_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2881_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2846_ = v___x_2843_;
v_isShared_2847_ = v_isSharedCheck_2881_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2843_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2881_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
if (lean_obj_tag(v_a_2844_) == 1)
{
lean_object* v_val_2848_; lean_object* v_snd_2849_; lean_object* v_snd_2850_; lean_object* v_fst_2851_; lean_object* v_fst_2852_; lean_object* v_p_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
lean_del_object(v___x_2846_);
v_val_2848_ = lean_ctor_get(v_a_2844_, 0);
lean_inc(v_val_2848_);
lean_dec_ref_known(v_a_2844_, 1);
v_snd_2849_ = lean_ctor_get(v_val_2848_, 1);
lean_inc(v_snd_2849_);
v_snd_2850_ = lean_ctor_get(v_snd_2849_, 1);
lean_inc(v_snd_2850_);
v_fst_2851_ = lean_ctor_get(v_val_2848_, 0);
lean_inc(v_fst_2851_);
lean_dec(v_val_2848_);
v_fst_2852_ = lean_ctor_get(v_snd_2849_, 0);
lean_inc(v_fst_2852_);
lean_dec(v_snd_2849_);
v_p_2853_ = lean_ctor_get(v_snd_2850_, 0);
v___x_2854_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2853_, v_fst_2852_);
lean_inc_ref(v_c_u2082_2818_);
v___x_2855_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v___x_2854_, v_fst_2852_, v_snd_2850_, v_fst_2851_, v_c_u2082_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v___x_2842_, v_a_2829_);
lean_dec(v_fst_2852_);
lean_dec(v___x_2854_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2855_, 1);
if (lean_obj_tag(v_a_2856_) == 1)
{
lean_object* v_val_2857_; 
lean_dec_ref(v_c_u2082_2818_);
v_val_2857_ = lean_ctor_get(v_a_2856_, 0);
lean_inc(v_val_2857_);
lean_dec_ref_known(v_a_2856_, 1);
v_c_u2082_2818_ = v_val_2857_;
v_a_2828_ = v___x_2842_;
goto _start;
}
else
{
lean_object* v___x_2859_; 
lean_dec(v_a_2856_);
v___x_2859_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_u2082_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v___x_2842_, v_a_2829_);
lean_dec_ref_known(v___x_2842_, 3);
lean_dec_ref(v_c_u2082_2818_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2867_; 
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2867_ == 0)
{
lean_object* v_unused_2868_; 
v_unused_2868_ = lean_ctor_get(v___x_2859_, 0);
lean_dec(v_unused_2868_);
v___x_2861_ = v___x_2859_;
v_isShared_2862_ = v_isSharedCheck_2867_;
goto v_resetjp_2860_;
}
else
{
lean_dec(v___x_2859_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2867_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2863_; lean_object* v___x_2865_; 
v___x_2863_ = lean_box(0);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 0, v___x_2863_);
v___x_2865_ = v___x_2861_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2863_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
v_a_2869_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2859_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2859_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2842_, 3);
lean_dec_ref(v_c_u2082_2818_);
return v___x_2855_;
}
}
else
{
lean_object* v___x_2877_; lean_object* v___x_2879_; 
lean_dec(v_a_2844_);
lean_dec_ref_known(v___x_2842_, 3);
v___x_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2877_, 0, v_c_u2082_2818_);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v___x_2877_);
v___x_2879_ = v___x_2846_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2877_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec_ref_known(v___x_2842_, 3);
lean_dec_ref(v_c_u2082_2818_);
v_a_2882_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2843_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2843_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object* v_c_u2082_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_u2082_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
lean_dec(v_a_2906_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
lean_dec(v_a_2898_);
lean_dec(v_a_2897_);
lean_dec(v_a_2896_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object* v_val_2909_, lean_object* v_x_2910_, size_t v_x_2911_, size_t v_x_2912_){
_start:
{
if (lean_obj_tag(v_x_2910_) == 0)
{
lean_object* v_cs_2913_; size_t v_j_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; uint8_t v___x_2917_; 
v_cs_2913_ = lean_ctor_get(v_x_2910_, 0);
v_j_2914_ = lean_usize_shift_right(v_x_2911_, v_x_2912_);
v___x_2915_ = lean_usize_to_nat(v_j_2914_);
v___x_2916_ = lean_array_get_size(v_cs_2913_);
v___x_2917_ = lean_nat_dec_lt(v___x_2915_, v___x_2916_);
if (v___x_2917_ == 0)
{
lean_dec(v___x_2915_);
lean_dec_ref(v_val_2909_);
return v_x_2910_;
}
else
{
lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2935_; 
lean_inc_ref(v_cs_2913_);
v_isSharedCheck_2935_ = !lean_is_exclusive(v_x_2910_);
if (v_isSharedCheck_2935_ == 0)
{
lean_object* v_unused_2936_; 
v_unused_2936_ = lean_ctor_get(v_x_2910_, 0);
lean_dec(v_unused_2936_);
v___x_2919_ = v_x_2910_;
v_isShared_2920_ = v_isSharedCheck_2935_;
goto v_resetjp_2918_;
}
else
{
lean_dec(v_x_2910_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2935_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
size_t v___x_2921_; size_t v___x_2922_; size_t v___x_2923_; size_t v_i_2924_; size_t v___x_2925_; size_t v_shift_2926_; lean_object* v_v_2927_; lean_object* v___x_2928_; lean_object* v_xs_x27_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2933_; 
v___x_2921_ = ((size_t)1ULL);
v___x_2922_ = lean_usize_shift_left(v___x_2921_, v_x_2912_);
v___x_2923_ = lean_usize_sub(v___x_2922_, v___x_2921_);
v_i_2924_ = lean_usize_land(v_x_2911_, v___x_2923_);
v___x_2925_ = ((size_t)5ULL);
v_shift_2926_ = lean_usize_sub(v_x_2912_, v___x_2925_);
v_v_2927_ = lean_array_fget(v_cs_2913_, v___x_2915_);
v___x_2928_ = lean_box(0);
v_xs_x27_2929_ = lean_array_fset(v_cs_2913_, v___x_2915_, v___x_2928_);
v___x_2930_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2909_, v_v_2927_, v_i_2924_, v_shift_2926_);
v___x_2931_ = lean_array_fset(v_xs_x27_2929_, v___x_2915_, v___x_2930_);
lean_dec(v___x_2915_);
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 0, v___x_2931_);
v___x_2933_ = v___x_2919_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v___x_2931_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
else
{
lean_object* v_vs_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; 
v_vs_2937_ = lean_ctor_get(v_x_2910_, 0);
v___x_2938_ = lean_usize_to_nat(v_x_2911_);
v___x_2939_ = lean_array_get_size(v_vs_2937_);
v___x_2940_ = lean_nat_dec_lt(v___x_2938_, v___x_2939_);
if (v___x_2940_ == 0)
{
lean_dec(v___x_2938_);
lean_dec_ref(v_val_2909_);
return v_x_2910_;
}
else
{
lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2952_; 
lean_inc_ref(v_vs_2937_);
v_isSharedCheck_2952_ = !lean_is_exclusive(v_x_2910_);
if (v_isSharedCheck_2952_ == 0)
{
lean_object* v_unused_2953_; 
v_unused_2953_ = lean_ctor_get(v_x_2910_, 0);
lean_dec(v_unused_2953_);
v___x_2942_ = v_x_2910_;
v_isShared_2943_ = v_isSharedCheck_2952_;
goto v_resetjp_2941_;
}
else
{
lean_dec(v_x_2910_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2952_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v_v_2944_; lean_object* v___x_2945_; lean_object* v_xs_x27_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2950_; 
v_v_2944_ = lean_array_fget(v_vs_2937_, v___x_2938_);
v___x_2945_ = lean_box(0);
v_xs_x27_2946_ = lean_array_fset(v_vs_2937_, v___x_2938_, v___x_2945_);
v___x_2947_ = l_Lean_PersistentArray_push___redArg(v_v_2944_, v_val_2909_);
v___x_2948_ = lean_array_fset(v_xs_x27_2946_, v___x_2938_, v___x_2947_);
lean_dec(v___x_2938_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2948_);
v___x_2950_ = v___x_2942_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_val_2954_, lean_object* v_x_2955_, lean_object* v_x_2956_, lean_object* v_x_2957_){
_start:
{
size_t v_x_41338__boxed_2958_; size_t v_x_41339__boxed_2959_; lean_object* v_res_2960_; 
v_x_41338__boxed_2958_ = lean_unbox_usize(v_x_2956_);
lean_dec(v_x_2956_);
v_x_41339__boxed_2959_ = lean_unbox_usize(v_x_2957_);
lean_dec(v_x_2957_);
v_res_2960_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2954_, v_x_2955_, v_x_41338__boxed_2958_, v_x_41339__boxed_2959_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object* v_val_2961_, lean_object* v_t_2962_, lean_object* v_i_2963_){
_start:
{
lean_object* v_root_2964_; lean_object* v_tail_2965_; lean_object* v_size_2966_; size_t v_shift_2967_; lean_object* v_tailOff_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2992_; 
v_root_2964_ = lean_ctor_get(v_t_2962_, 0);
v_tail_2965_ = lean_ctor_get(v_t_2962_, 1);
v_size_2966_ = lean_ctor_get(v_t_2962_, 2);
v_shift_2967_ = lean_ctor_get_usize(v_t_2962_, 4);
v_tailOff_2968_ = lean_ctor_get(v_t_2962_, 3);
v_isSharedCheck_2992_ = !lean_is_exclusive(v_t_2962_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2970_ = v_t_2962_;
v_isShared_2971_ = v_isSharedCheck_2992_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_tailOff_2968_);
lean_inc(v_size_2966_);
lean_inc(v_tail_2965_);
lean_inc(v_root_2964_);
lean_dec(v_t_2962_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2992_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
uint8_t v___x_2972_; 
v___x_2972_ = lean_nat_dec_le(v_tailOff_2968_, v_i_2963_);
if (v___x_2972_ == 0)
{
size_t v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2976_; 
v___x_2973_ = lean_usize_of_nat(v_i_2963_);
v___x_2974_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2961_, v_root_2964_, v___x_2973_, v_shift_2967_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 0, v___x_2974_);
v___x_2976_ = v___x_2970_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_tail_2965_);
lean_ctor_set(v_reuseFailAlloc_2977_, 2, v_size_2966_);
lean_ctor_set(v_reuseFailAlloc_2977_, 3, v_tailOff_2968_);
lean_ctor_set_usize(v_reuseFailAlloc_2977_, 4, v_shift_2967_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
else
{
lean_object* v___x_2978_; lean_object* v___x_2979_; uint8_t v___x_2980_; 
v___x_2978_ = lean_nat_sub(v_i_2963_, v_tailOff_2968_);
v___x_2979_ = lean_array_get_size(v_tail_2965_);
v___x_2980_ = lean_nat_dec_lt(v___x_2978_, v___x_2979_);
if (v___x_2980_ == 0)
{
lean_object* v___x_2982_; 
lean_dec(v___x_2978_);
lean_dec_ref(v_val_2961_);
if (v_isShared_2971_ == 0)
{
v___x_2982_ = v___x_2970_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_root_2964_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v_tail_2965_);
lean_ctor_set(v_reuseFailAlloc_2983_, 2, v_size_2966_);
lean_ctor_set(v_reuseFailAlloc_2983_, 3, v_tailOff_2968_);
lean_ctor_set_usize(v_reuseFailAlloc_2983_, 4, v_shift_2967_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
else
{
lean_object* v_v_2984_; lean_object* v___x_2985_; lean_object* v_xs_x27_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2990_; 
v_v_2984_ = lean_array_fget(v_tail_2965_, v___x_2978_);
v___x_2985_ = lean_box(0);
v_xs_x27_2986_ = lean_array_fset(v_tail_2965_, v___x_2978_, v___x_2985_);
v___x_2987_ = l_Lean_PersistentArray_push___redArg(v_v_2984_, v_val_2961_);
v___x_2988_ = lean_array_fset(v_xs_x27_2986_, v___x_2978_, v___x_2987_);
lean_dec(v___x_2978_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 1, v___x_2988_);
v___x_2990_ = v___x_2970_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_root_2964_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v___x_2988_);
lean_ctor_set(v_reuseFailAlloc_2991_, 2, v_size_2966_);
lean_ctor_set(v_reuseFailAlloc_2991_, 3, v_tailOff_2968_);
lean_ctor_set_usize(v_reuseFailAlloc_2991_, 4, v_shift_2967_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object* v_val_2993_, lean_object* v_t_2994_, lean_object* v_i_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_2993_, v_t_2994_, v_i_2995_);
lean_dec(v_i_2995_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(lean_object* v___y_2997_, lean_object* v_val_2998_, lean_object* v_v_2999_, lean_object* v_s_3000_){
_start:
{
lean_object* v_structs_3001_; lean_object* v_typeIdOf_3002_; lean_object* v_exprToStructId_3003_; lean_object* v_exprToStructIdEntries_3004_; lean_object* v_forbiddenNatModules_3005_; lean_object* v_natStructs_3006_; lean_object* v_natTypeIdOf_3007_; lean_object* v_exprToNatStructId_3008_; lean_object* v___x_3009_; uint8_t v___x_3010_; 
v_structs_3001_ = lean_ctor_get(v_s_3000_, 0);
v_typeIdOf_3002_ = lean_ctor_get(v_s_3000_, 1);
v_exprToStructId_3003_ = lean_ctor_get(v_s_3000_, 2);
v_exprToStructIdEntries_3004_ = lean_ctor_get(v_s_3000_, 3);
v_forbiddenNatModules_3005_ = lean_ctor_get(v_s_3000_, 4);
v_natStructs_3006_ = lean_ctor_get(v_s_3000_, 5);
v_natTypeIdOf_3007_ = lean_ctor_get(v_s_3000_, 6);
v_exprToNatStructId_3008_ = lean_ctor_get(v_s_3000_, 7);
v___x_3009_ = lean_array_get_size(v_structs_3001_);
v___x_3010_ = lean_nat_dec_lt(v___y_2997_, v___x_3009_);
if (v___x_3010_ == 0)
{
lean_dec_ref(v_val_2998_);
return v_s_3000_;
}
else
{
lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3072_; 
lean_inc_ref(v_exprToNatStructId_3008_);
lean_inc_ref(v_natTypeIdOf_3007_);
lean_inc_ref(v_natStructs_3006_);
lean_inc_ref(v_forbiddenNatModules_3005_);
lean_inc_ref(v_exprToStructIdEntries_3004_);
lean_inc_ref(v_exprToStructId_3003_);
lean_inc_ref(v_typeIdOf_3002_);
lean_inc_ref(v_structs_3001_);
v_isSharedCheck_3072_ = !lean_is_exclusive(v_s_3000_);
if (v_isSharedCheck_3072_ == 0)
{
lean_object* v_unused_3073_; lean_object* v_unused_3074_; lean_object* v_unused_3075_; lean_object* v_unused_3076_; lean_object* v_unused_3077_; lean_object* v_unused_3078_; lean_object* v_unused_3079_; lean_object* v_unused_3080_; 
v_unused_3073_ = lean_ctor_get(v_s_3000_, 7);
lean_dec(v_unused_3073_);
v_unused_3074_ = lean_ctor_get(v_s_3000_, 6);
lean_dec(v_unused_3074_);
v_unused_3075_ = lean_ctor_get(v_s_3000_, 5);
lean_dec(v_unused_3075_);
v_unused_3076_ = lean_ctor_get(v_s_3000_, 4);
lean_dec(v_unused_3076_);
v_unused_3077_ = lean_ctor_get(v_s_3000_, 3);
lean_dec(v_unused_3077_);
v_unused_3078_ = lean_ctor_get(v_s_3000_, 2);
lean_dec(v_unused_3078_);
v_unused_3079_ = lean_ctor_get(v_s_3000_, 1);
lean_dec(v_unused_3079_);
v_unused_3080_ = lean_ctor_get(v_s_3000_, 0);
lean_dec(v_unused_3080_);
v___x_3012_ = v_s_3000_;
v_isShared_3013_ = v_isSharedCheck_3072_;
goto v_resetjp_3011_;
}
else
{
lean_dec(v_s_3000_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3072_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v_v_3014_; lean_object* v_id_3015_; lean_object* v_ringId_x3f_3016_; lean_object* v_type_3017_; lean_object* v_u_3018_; lean_object* v_intModuleInst_3019_; lean_object* v_leInst_x3f_3020_; lean_object* v_ltInst_x3f_3021_; lean_object* v_lawfulOrderLTInst_x3f_3022_; lean_object* v_isPreorderInst_x3f_3023_; lean_object* v_orderedAddInst_x3f_3024_; lean_object* v_isLinearInst_x3f_3025_; lean_object* v_noNatDivInst_x3f_3026_; lean_object* v_ringInst_x3f_3027_; lean_object* v_commRingInst_x3f_3028_; lean_object* v_orderedRingInst_x3f_3029_; lean_object* v_fieldInst_x3f_3030_; lean_object* v_charInst_x3f_3031_; lean_object* v_zero_3032_; lean_object* v_ofNatZero_3033_; lean_object* v_one_x3f_3034_; lean_object* v_leFn_x3f_3035_; lean_object* v_ltFn_x3f_3036_; lean_object* v_addFn_3037_; lean_object* v_zsmulFn_3038_; lean_object* v_nsmulFn_3039_; lean_object* v_zsmulFn_x3f_3040_; lean_object* v_nsmulFn_x3f_3041_; lean_object* v_homomulFn_x3f_3042_; lean_object* v_subFn_3043_; lean_object* v_negFn_3044_; lean_object* v_vars_3045_; lean_object* v_varMap_3046_; lean_object* v_lowers_3047_; lean_object* v_uppers_3048_; lean_object* v_diseqs_3049_; lean_object* v_assignment_3050_; uint8_t v_caseSplits_3051_; lean_object* v_conflict_x3f_3052_; lean_object* v_diseqSplits_3053_; lean_object* v_elimEqs_3054_; lean_object* v_elimStack_3055_; lean_object* v_occurs_3056_; lean_object* v_ignored_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3071_; 
v_v_3014_ = lean_array_fget(v_structs_3001_, v___y_2997_);
v_id_3015_ = lean_ctor_get(v_v_3014_, 0);
v_ringId_x3f_3016_ = lean_ctor_get(v_v_3014_, 1);
v_type_3017_ = lean_ctor_get(v_v_3014_, 2);
v_u_3018_ = lean_ctor_get(v_v_3014_, 3);
v_intModuleInst_3019_ = lean_ctor_get(v_v_3014_, 4);
v_leInst_x3f_3020_ = lean_ctor_get(v_v_3014_, 5);
v_ltInst_x3f_3021_ = lean_ctor_get(v_v_3014_, 6);
v_lawfulOrderLTInst_x3f_3022_ = lean_ctor_get(v_v_3014_, 7);
v_isPreorderInst_x3f_3023_ = lean_ctor_get(v_v_3014_, 8);
v_orderedAddInst_x3f_3024_ = lean_ctor_get(v_v_3014_, 9);
v_isLinearInst_x3f_3025_ = lean_ctor_get(v_v_3014_, 10);
v_noNatDivInst_x3f_3026_ = lean_ctor_get(v_v_3014_, 11);
v_ringInst_x3f_3027_ = lean_ctor_get(v_v_3014_, 12);
v_commRingInst_x3f_3028_ = lean_ctor_get(v_v_3014_, 13);
v_orderedRingInst_x3f_3029_ = lean_ctor_get(v_v_3014_, 14);
v_fieldInst_x3f_3030_ = lean_ctor_get(v_v_3014_, 15);
v_charInst_x3f_3031_ = lean_ctor_get(v_v_3014_, 16);
v_zero_3032_ = lean_ctor_get(v_v_3014_, 17);
v_ofNatZero_3033_ = lean_ctor_get(v_v_3014_, 18);
v_one_x3f_3034_ = lean_ctor_get(v_v_3014_, 19);
v_leFn_x3f_3035_ = lean_ctor_get(v_v_3014_, 20);
v_ltFn_x3f_3036_ = lean_ctor_get(v_v_3014_, 21);
v_addFn_3037_ = lean_ctor_get(v_v_3014_, 22);
v_zsmulFn_3038_ = lean_ctor_get(v_v_3014_, 23);
v_nsmulFn_3039_ = lean_ctor_get(v_v_3014_, 24);
v_zsmulFn_x3f_3040_ = lean_ctor_get(v_v_3014_, 25);
v_nsmulFn_x3f_3041_ = lean_ctor_get(v_v_3014_, 26);
v_homomulFn_x3f_3042_ = lean_ctor_get(v_v_3014_, 27);
v_subFn_3043_ = lean_ctor_get(v_v_3014_, 28);
v_negFn_3044_ = lean_ctor_get(v_v_3014_, 29);
v_vars_3045_ = lean_ctor_get(v_v_3014_, 30);
v_varMap_3046_ = lean_ctor_get(v_v_3014_, 31);
v_lowers_3047_ = lean_ctor_get(v_v_3014_, 32);
v_uppers_3048_ = lean_ctor_get(v_v_3014_, 33);
v_diseqs_3049_ = lean_ctor_get(v_v_3014_, 34);
v_assignment_3050_ = lean_ctor_get(v_v_3014_, 35);
v_caseSplits_3051_ = lean_ctor_get_uint8(v_v_3014_, sizeof(void*)*42);
v_conflict_x3f_3052_ = lean_ctor_get(v_v_3014_, 36);
v_diseqSplits_3053_ = lean_ctor_get(v_v_3014_, 37);
v_elimEqs_3054_ = lean_ctor_get(v_v_3014_, 38);
v_elimStack_3055_ = lean_ctor_get(v_v_3014_, 39);
v_occurs_3056_ = lean_ctor_get(v_v_3014_, 40);
v_ignored_3057_ = lean_ctor_get(v_v_3014_, 41);
v_isSharedCheck_3071_ = !lean_is_exclusive(v_v_3014_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3059_ = v_v_3014_;
v_isShared_3060_ = v_isSharedCheck_3071_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_ignored_3057_);
lean_inc(v_occurs_3056_);
lean_inc(v_elimStack_3055_);
lean_inc(v_elimEqs_3054_);
lean_inc(v_diseqSplits_3053_);
lean_inc(v_conflict_x3f_3052_);
lean_inc(v_assignment_3050_);
lean_inc(v_diseqs_3049_);
lean_inc(v_uppers_3048_);
lean_inc(v_lowers_3047_);
lean_inc(v_varMap_3046_);
lean_inc(v_vars_3045_);
lean_inc(v_negFn_3044_);
lean_inc(v_subFn_3043_);
lean_inc(v_homomulFn_x3f_3042_);
lean_inc(v_nsmulFn_x3f_3041_);
lean_inc(v_zsmulFn_x3f_3040_);
lean_inc(v_nsmulFn_3039_);
lean_inc(v_zsmulFn_3038_);
lean_inc(v_addFn_3037_);
lean_inc(v_ltFn_x3f_3036_);
lean_inc(v_leFn_x3f_3035_);
lean_inc(v_one_x3f_3034_);
lean_inc(v_ofNatZero_3033_);
lean_inc(v_zero_3032_);
lean_inc(v_charInst_x3f_3031_);
lean_inc(v_fieldInst_x3f_3030_);
lean_inc(v_orderedRingInst_x3f_3029_);
lean_inc(v_commRingInst_x3f_3028_);
lean_inc(v_ringInst_x3f_3027_);
lean_inc(v_noNatDivInst_x3f_3026_);
lean_inc(v_isLinearInst_x3f_3025_);
lean_inc(v_orderedAddInst_x3f_3024_);
lean_inc(v_isPreorderInst_x3f_3023_);
lean_inc(v_lawfulOrderLTInst_x3f_3022_);
lean_inc(v_ltInst_x3f_3021_);
lean_inc(v_leInst_x3f_3020_);
lean_inc(v_intModuleInst_3019_);
lean_inc(v_u_3018_);
lean_inc(v_type_3017_);
lean_inc(v_ringId_x3f_3016_);
lean_inc(v_id_3015_);
lean_dec(v_v_3014_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3071_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3061_; lean_object* v_xs_x27_3062_; lean_object* v___x_3063_; lean_object* v___x_3065_; 
v___x_3061_ = lean_box(0);
v_xs_x27_3062_ = lean_array_fset(v_structs_3001_, v___y_2997_, v___x_3061_);
v___x_3063_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_2998_, v_diseqs_3049_, v_v_2999_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 34, v___x_3063_);
v___x_3065_ = v___x_3059_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_id_3015_);
lean_ctor_set(v_reuseFailAlloc_3070_, 1, v_ringId_x3f_3016_);
lean_ctor_set(v_reuseFailAlloc_3070_, 2, v_type_3017_);
lean_ctor_set(v_reuseFailAlloc_3070_, 3, v_u_3018_);
lean_ctor_set(v_reuseFailAlloc_3070_, 4, v_intModuleInst_3019_);
lean_ctor_set(v_reuseFailAlloc_3070_, 5, v_leInst_x3f_3020_);
lean_ctor_set(v_reuseFailAlloc_3070_, 6, v_ltInst_x3f_3021_);
lean_ctor_set(v_reuseFailAlloc_3070_, 7, v_lawfulOrderLTInst_x3f_3022_);
lean_ctor_set(v_reuseFailAlloc_3070_, 8, v_isPreorderInst_x3f_3023_);
lean_ctor_set(v_reuseFailAlloc_3070_, 9, v_orderedAddInst_x3f_3024_);
lean_ctor_set(v_reuseFailAlloc_3070_, 10, v_isLinearInst_x3f_3025_);
lean_ctor_set(v_reuseFailAlloc_3070_, 11, v_noNatDivInst_x3f_3026_);
lean_ctor_set(v_reuseFailAlloc_3070_, 12, v_ringInst_x3f_3027_);
lean_ctor_set(v_reuseFailAlloc_3070_, 13, v_commRingInst_x3f_3028_);
lean_ctor_set(v_reuseFailAlloc_3070_, 14, v_orderedRingInst_x3f_3029_);
lean_ctor_set(v_reuseFailAlloc_3070_, 15, v_fieldInst_x3f_3030_);
lean_ctor_set(v_reuseFailAlloc_3070_, 16, v_charInst_x3f_3031_);
lean_ctor_set(v_reuseFailAlloc_3070_, 17, v_zero_3032_);
lean_ctor_set(v_reuseFailAlloc_3070_, 18, v_ofNatZero_3033_);
lean_ctor_set(v_reuseFailAlloc_3070_, 19, v_one_x3f_3034_);
lean_ctor_set(v_reuseFailAlloc_3070_, 20, v_leFn_x3f_3035_);
lean_ctor_set(v_reuseFailAlloc_3070_, 21, v_ltFn_x3f_3036_);
lean_ctor_set(v_reuseFailAlloc_3070_, 22, v_addFn_3037_);
lean_ctor_set(v_reuseFailAlloc_3070_, 23, v_zsmulFn_3038_);
lean_ctor_set(v_reuseFailAlloc_3070_, 24, v_nsmulFn_3039_);
lean_ctor_set(v_reuseFailAlloc_3070_, 25, v_zsmulFn_x3f_3040_);
lean_ctor_set(v_reuseFailAlloc_3070_, 26, v_nsmulFn_x3f_3041_);
lean_ctor_set(v_reuseFailAlloc_3070_, 27, v_homomulFn_x3f_3042_);
lean_ctor_set(v_reuseFailAlloc_3070_, 28, v_subFn_3043_);
lean_ctor_set(v_reuseFailAlloc_3070_, 29, v_negFn_3044_);
lean_ctor_set(v_reuseFailAlloc_3070_, 30, v_vars_3045_);
lean_ctor_set(v_reuseFailAlloc_3070_, 31, v_varMap_3046_);
lean_ctor_set(v_reuseFailAlloc_3070_, 32, v_lowers_3047_);
lean_ctor_set(v_reuseFailAlloc_3070_, 33, v_uppers_3048_);
lean_ctor_set(v_reuseFailAlloc_3070_, 34, v___x_3063_);
lean_ctor_set(v_reuseFailAlloc_3070_, 35, v_assignment_3050_);
lean_ctor_set(v_reuseFailAlloc_3070_, 36, v_conflict_x3f_3052_);
lean_ctor_set(v_reuseFailAlloc_3070_, 37, v_diseqSplits_3053_);
lean_ctor_set(v_reuseFailAlloc_3070_, 38, v_elimEqs_3054_);
lean_ctor_set(v_reuseFailAlloc_3070_, 39, v_elimStack_3055_);
lean_ctor_set(v_reuseFailAlloc_3070_, 40, v_occurs_3056_);
lean_ctor_set(v_reuseFailAlloc_3070_, 41, v_ignored_3057_);
lean_ctor_set_uint8(v_reuseFailAlloc_3070_, sizeof(void*)*42, v_caseSplits_3051_);
v___x_3065_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
lean_object* v___x_3066_; lean_object* v___x_3068_; 
v___x_3066_ = lean_array_fset(v_xs_x27_3062_, v___y_2997_, v___x_3065_);
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 0, v___x_3066_);
v___x_3068_ = v___x_3012_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3066_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v_typeIdOf_3002_);
lean_ctor_set(v_reuseFailAlloc_3069_, 2, v_exprToStructId_3003_);
lean_ctor_set(v_reuseFailAlloc_3069_, 3, v_exprToStructIdEntries_3004_);
lean_ctor_set(v_reuseFailAlloc_3069_, 4, v_forbiddenNatModules_3005_);
lean_ctor_set(v_reuseFailAlloc_3069_, 5, v_natStructs_3006_);
lean_ctor_set(v_reuseFailAlloc_3069_, 6, v_natTypeIdOf_3007_);
lean_ctor_set(v_reuseFailAlloc_3069_, 7, v_exprToNatStructId_3008_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed(lean_object* v___y_3081_, lean_object* v_val_3082_, lean_object* v_v_3083_, lean_object* v_s_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(v___y_3081_, v_val_3082_, v_v_3083_, v_s_3084_);
lean_dec(v_v_3083_);
lean_dec(v___y_3081_);
return v_res_3085_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2(void){
_start:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3091_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3092_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3093_ = l_Lean_Name_append(v___x_3092_, v___x_3091_);
return v___x_3093_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3101_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3102_ = l_Lean_Name_append(v___x_3101_, v___x_3100_);
return v___x_3102_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7(void){
_start:
{
lean_object* v_cls_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v_cls_3107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3109_ = l_Lean_Name_append(v___x_3108_, v_cls_3107_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object* v_c_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_){
_start:
{
lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v_toCold_3181_; lean_object* v_options_3182_; lean_object* v_inheritedTraceOptions_3183_; uint8_t v_hasTrace_3184_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; 
v_toCold_3181_ = lean_ctor_get(v_a_3120_, 0);
v_options_3182_ = lean_ctor_get(v_toCold_3181_, 2);
v_inheritedTraceOptions_3183_ = lean_ctor_get(v_toCold_3181_, 11);
v_hasTrace_3184_ = lean_ctor_get_uint8(v_options_3182_, sizeof(void*)*1);
if (v_hasTrace_3184_ == 0)
{
v___y_3186_ = v_a_3111_;
v___y_3187_ = v_a_3112_;
v___y_3188_ = v_a_3113_;
v___y_3189_ = v_a_3114_;
v___y_3190_ = v_a_3115_;
v___y_3191_ = v_a_3116_;
v___y_3192_ = v_a_3117_;
v___y_3193_ = v_a_3118_;
v___y_3194_ = v_a_3119_;
v___y_3195_ = v_a_3120_;
v___y_3196_ = v_a_3121_;
goto v___jp_3185_;
}
else
{
lean_object* v_cls_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; 
v_cls_3257_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3258_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_3259_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3183_, v_options_3182_, v___x_3258_);
if (v___x_3259_ == 0)
{
v___y_3186_ = v_a_3111_;
v___y_3187_ = v_a_3112_;
v___y_3188_ = v_a_3113_;
v___y_3189_ = v_a_3114_;
v___y_3190_ = v_a_3115_;
v___y_3191_ = v_a_3116_;
v___y_3192_ = v_a_3117_;
v___y_3193_ = v_a_3118_;
v___y_3194_ = v_a_3119_;
v___y_3195_ = v_a_3120_;
v___y_3196_ = v_a_3121_;
goto v___jp_3185_;
}
else
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref_known(v___x_3260_, 1);
v___x_3262_ = l_Lean_MessageData_ofExpr(v_a_3261_);
v___x_3263_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_3257_, v___x_3262_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_dec_ref_known(v___x_3263_, 1);
v___y_3186_ = v_a_3111_;
v___y_3187_ = v_a_3112_;
v___y_3188_ = v_a_3113_;
v___y_3189_ = v_a_3114_;
v___y_3190_ = v_a_3115_;
v___y_3191_ = v_a_3116_;
v___y_3192_ = v_a_3117_;
v___y_3193_ = v_a_3118_;
v___y_3194_ = v_a_3119_;
v___y_3195_ = v_a_3120_;
v___y_3196_ = v_a_3121_;
goto v___jp_3185_;
}
else
{
lean_dec_ref(v_c_3110_);
return v___x_3263_;
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_dec_ref(v_c_3110_);
v_a_3264_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3260_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3260_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
}
v___jp_3123_:
{
lean_object* v___f_3140_; lean_object* v___x_3141_; 
lean_inc(v___y_3129_);
v___f_3140_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3140_, 0, v___y_3129_);
lean_closure_set(v___f_3140_, 1, v___y_3124_);
lean_closure_set(v___f_3140_, 2, v___y_3125_);
v___x_3141_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
lean_dec_ref_known(v___x_3141_, 1);
v___x_3142_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3143_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3142_, v___f_3140_, v___y_3130_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v___x_3144_; 
lean_dec_ref_known(v___x_3143_, 1);
v___x_3144_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v___y_3126_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3157_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3147_ = v___x_3144_;
v_isShared_3148_ = v_isSharedCheck_3157_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3144_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3157_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
uint8_t v___x_3149_; uint8_t v___x_3150_; uint8_t v___x_3151_; 
v___x_3149_ = 0;
v___x_3150_ = lean_unbox(v_a_3145_);
lean_dec(v_a_3145_);
v___x_3151_ = l_Lean_instBEqLBool_beq(v___x_3150_, v___x_3149_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; lean_object* v___x_3154_; 
lean_dec(v___y_3127_);
v___x_3152_ = lean_box(0);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v___x_3152_);
v___x_3154_ = v___x_3147_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v___x_3152_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
else
{
lean_object* v___x_3156_; 
lean_del_object(v___x_3147_);
v___x_3156_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_3127_, v___y_3129_, v___y_3130_);
return v___x_3156_;
}
}
}
else
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_dec(v___y_3127_);
v_a_3158_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3144_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3144_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
else
{
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
return v___x_3143_;
}
}
else
{
lean_dec_ref(v___f_3140_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
return v___x_3141_;
}
}
v___jp_3166_:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3179_, 0, v___y_3167_);
v___x_3180_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(v___x_3179_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
return v___x_3180_;
}
v___jp_3185_:
{
lean_object* v___x_3197_; 
lean_inc_ref(v___y_3195_);
v___x_3197_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_3110_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3248_; 
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3200_ = v___x_3197_;
v_isShared_3201_ = v_isSharedCheck_3248_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3197_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3248_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
if (lean_obj_tag(v_a_3198_) == 1)
{
lean_object* v_val_3202_; lean_object* v_p_3203_; 
lean_del_object(v___x_3200_);
v_val_3202_ = lean_ctor_get(v_a_3198_, 0);
lean_inc(v_val_3202_);
lean_dec_ref_known(v_a_3198_, 1);
v_p_3203_ = lean_ctor_get(v_val_3202_, 0);
if (lean_obj_tag(v_p_3203_) == 0)
{
lean_object* v_toCold_3204_; lean_object* v_options_3205_; uint8_t v_hasTrace_3206_; 
v_toCold_3204_ = lean_ctor_get(v___y_3195_, 0);
v_options_3205_ = lean_ctor_get(v_toCold_3204_, 2);
v_hasTrace_3206_ = lean_ctor_get_uint8(v_options_3205_, sizeof(void*)*1);
if (v_hasTrace_3206_ == 0)
{
v___y_3167_ = v_val_3202_;
v___y_3168_ = v___y_3186_;
v___y_3169_ = v___y_3187_;
v___y_3170_ = v___y_3188_;
v___y_3171_ = v___y_3189_;
v___y_3172_ = v___y_3190_;
v___y_3173_ = v___y_3191_;
v___y_3174_ = v___y_3192_;
v___y_3175_ = v___y_3193_;
v___y_3176_ = v___y_3194_;
v___y_3177_ = v___y_3195_;
v___y_3178_ = v___y_3196_;
goto v___jp_3166_;
}
else
{
lean_object* v_inheritedTraceOptions_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; uint8_t v___x_3210_; 
v_inheritedTraceOptions_3207_ = lean_ctor_get(v_toCold_3204_, 11);
v___x_3208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3209_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2);
v___x_3210_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3207_, v_options_3205_, v___x_3209_);
if (v___x_3210_ == 0)
{
v___y_3167_ = v_val_3202_;
v___y_3168_ = v___y_3186_;
v___y_3169_ = v___y_3187_;
v___y_3170_ = v___y_3188_;
v___y_3171_ = v___y_3189_;
v___y_3172_ = v___y_3190_;
v___y_3173_ = v___y_3191_;
v___y_3174_ = v___y_3192_;
v___y_3175_ = v___y_3193_;
v___y_3176_ = v___y_3194_;
v___y_3177_ = v___y_3195_;
v___y_3178_ = v___y_3196_;
goto v___jp_3166_;
}
else
{
lean_object* v___x_3211_; 
v___x_3211_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3202_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_a_3212_);
lean_dec_ref_known(v___x_3211_, 1);
v___x_3213_ = l_Lean_MessageData_ofExpr(v_a_3212_);
v___x_3214_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3208_, v___x_3213_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_dec_ref_known(v___x_3214_, 1);
v___y_3167_ = v_val_3202_;
v___y_3168_ = v___y_3186_;
v___y_3169_ = v___y_3187_;
v___y_3170_ = v___y_3188_;
v___y_3171_ = v___y_3189_;
v___y_3172_ = v___y_3190_;
v___y_3173_ = v___y_3191_;
v___y_3174_ = v___y_3192_;
v___y_3175_ = v___y_3193_;
v___y_3176_ = v___y_3194_;
v___y_3177_ = v___y_3195_;
v___y_3178_ = v___y_3196_;
goto v___jp_3166_;
}
else
{
lean_dec(v_val_3202_);
return v___x_3214_;
}
}
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
lean_dec(v_val_3202_);
v_a_3215_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_3211_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3211_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3223_; lean_object* v_options_3224_; uint8_t v_hasTrace_3225_; 
lean_inc_ref(v_p_3203_);
v_toCold_3223_ = lean_ctor_get(v___y_3195_, 0);
v_options_3224_ = lean_ctor_get(v_toCold_3223_, 2);
v_hasTrace_3225_ = lean_ctor_get_uint8(v_options_3224_, sizeof(void*)*1);
if (v_hasTrace_3225_ == 0)
{
lean_object* v_v_3226_; 
v_v_3226_ = lean_ctor_get(v_p_3203_, 1);
lean_inc_n(v_v_3226_, 2);
lean_inc(v_val_3202_);
v___y_3124_ = v_val_3202_;
v___y_3125_ = v_v_3226_;
v___y_3126_ = v_val_3202_;
v___y_3127_ = v_v_3226_;
v___y_3128_ = v_p_3203_;
v___y_3129_ = v___y_3186_;
v___y_3130_ = v___y_3187_;
v___y_3131_ = v___y_3188_;
v___y_3132_ = v___y_3189_;
v___y_3133_ = v___y_3190_;
v___y_3134_ = v___y_3191_;
v___y_3135_ = v___y_3192_;
v___y_3136_ = v___y_3193_;
v___y_3137_ = v___y_3194_;
v___y_3138_ = v___y_3195_;
v___y_3139_ = v___y_3196_;
goto v___jp_3123_;
}
else
{
lean_object* v_v_3227_; lean_object* v_inheritedTraceOptions_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; uint8_t v___x_3231_; 
v_v_3227_ = lean_ctor_get(v_p_3203_, 1);
lean_inc(v_v_3227_);
v_inheritedTraceOptions_3228_ = lean_ctor_get(v_toCold_3223_, 11);
v___x_3229_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3230_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_3231_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3228_, v_options_3224_, v___x_3230_);
if (v___x_3231_ == 0)
{
lean_inc(v_v_3227_);
lean_inc(v_val_3202_);
v___y_3124_ = v_val_3202_;
v___y_3125_ = v_v_3227_;
v___y_3126_ = v_val_3202_;
v___y_3127_ = v_v_3227_;
v___y_3128_ = v_p_3203_;
v___y_3129_ = v___y_3186_;
v___y_3130_ = v___y_3187_;
v___y_3131_ = v___y_3188_;
v___y_3132_ = v___y_3189_;
v___y_3133_ = v___y_3190_;
v___y_3134_ = v___y_3191_;
v___y_3135_ = v___y_3192_;
v___y_3136_ = v___y_3193_;
v___y_3137_ = v___y_3194_;
v___y_3138_ = v___y_3195_;
v___y_3139_ = v___y_3196_;
goto v___jp_3123_;
}
else
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3202_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3233_);
lean_dec_ref_known(v___x_3232_, 1);
v___x_3234_ = l_Lean_MessageData_ofExpr(v_a_3233_);
v___x_3235_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3229_, v___x_3234_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_dec_ref_known(v___x_3235_, 1);
lean_inc(v_v_3227_);
lean_inc(v_val_3202_);
v___y_3124_ = v_val_3202_;
v___y_3125_ = v_v_3227_;
v___y_3126_ = v_val_3202_;
v___y_3127_ = v_v_3227_;
v___y_3128_ = v_p_3203_;
v___y_3129_ = v___y_3186_;
v___y_3130_ = v___y_3187_;
v___y_3131_ = v___y_3188_;
v___y_3132_ = v___y_3189_;
v___y_3133_ = v___y_3190_;
v___y_3134_ = v___y_3191_;
v___y_3135_ = v___y_3192_;
v___y_3136_ = v___y_3193_;
v___y_3137_ = v___y_3194_;
v___y_3138_ = v___y_3195_;
v___y_3139_ = v___y_3196_;
goto v___jp_3123_;
}
else
{
lean_dec(v_v_3227_);
lean_dec_ref_known(v_p_3203_, 3);
lean_dec(v_val_3202_);
return v___x_3235_;
}
}
else
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
lean_dec(v_v_3227_);
lean_dec_ref_known(v_p_3203_, 3);
lean_dec(v_val_3202_);
v_a_3236_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3232_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3232_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3244_; lean_object* v___x_3246_; 
lean_dec(v_a_3198_);
v___x_3244_ = lean_box(0);
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 0, v___x_3244_);
v___x_3246_ = v___x_3200_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3244_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
}
else
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
v_a_3249_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3197_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3197_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___boxed(lean_object* v_c_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_c_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_);
lean_dec(v_a_3283_);
lean_dec_ref(v_a_3282_);
lean_dec(v_a_3281_);
lean_dec_ref(v_a_3280_);
lean_dec(v_a_3279_);
lean_dec_ref(v_a_3278_);
lean_dec(v_a_3277_);
lean_dec_ref(v_a_3276_);
lean_dec(v_a_3275_);
lean_dec(v_a_3274_);
lean_dec(v_a_3273_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_3286_, lean_object* v_as_3287_, size_t v_sz_3288_, size_t v_i_3289_, lean_object* v_b_3290_){
_start:
{
uint8_t v___x_3291_; 
v___x_3291_ = lean_usize_dec_lt(v_i_3289_, v_sz_3288_);
if (v___x_3291_ == 0)
{
return v_b_3290_;
}
else
{
lean_object* v_snd_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3333_; 
v_snd_3292_ = lean_ctor_get(v_b_3290_, 1);
v_isSharedCheck_3333_ = !lean_is_exclusive(v_b_3290_);
if (v_isSharedCheck_3333_ == 0)
{
lean_object* v_unused_3334_; 
v_unused_3334_ = lean_ctor_get(v_b_3290_, 0);
lean_dec(v_unused_3334_);
v___x_3294_ = v_b_3290_;
v_isShared_3295_ = v_isSharedCheck_3333_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_snd_3292_);
lean_dec(v_b_3290_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3333_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v_fst_3296_; lean_object* v_snd_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3332_; 
v_fst_3296_ = lean_ctor_get(v_snd_3292_, 0);
v_snd_3297_ = lean_ctor_get(v_snd_3292_, 1);
v_isSharedCheck_3332_ = !lean_is_exclusive(v_snd_3292_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3299_ = v_snd_3292_;
v_isShared_3300_ = v_isSharedCheck_3332_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_snd_3297_);
lean_inc(v_fst_3296_);
lean_dec(v_snd_3292_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3332_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v_a_3301_; lean_object* v_p_3302_; lean_object* v___x_3303_; lean_object* v_a_3305_; lean_object* v_b_3312_; lean_object* v___x_3313_; uint8_t v___x_3314_; 
v_a_3301_ = lean_array_uget(v_as_3287_, v_i_3289_);
v_p_3302_ = lean_ctor_get(v_a_3301_, 0);
v___x_3303_ = lean_box(0);
v_b_3312_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3302_, v_x_3286_);
v___x_3313_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3314_ = lean_int_dec_eq(v_b_3312_, v___x_3313_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3316_; 
lean_inc(v_a_3301_);
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 1, v_a_3301_);
lean_ctor_set(v___x_3294_, 0, v_b_3312_);
v___x_3316_ = v___x_3294_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_b_3312_);
lean_ctor_set(v_reuseFailAlloc_3327_, 1, v_a_3301_);
v___x_3316_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3324_; 
v_isSharedCheck_3324_ = !lean_is_exclusive(v_a_3301_);
if (v_isSharedCheck_3324_ == 0)
{
lean_object* v_unused_3325_; lean_object* v_unused_3326_; 
v_unused_3325_ = lean_ctor_get(v_a_3301_, 1);
lean_dec(v_unused_3325_);
v_unused_3326_ = lean_ctor_get(v_a_3301_, 0);
lean_dec(v_unused_3326_);
v___x_3318_ = v_a_3301_;
v_isShared_3319_ = v_isSharedCheck_3324_;
goto v_resetjp_3317_;
}
else
{
lean_dec(v_a_3301_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3324_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v_todo_3320_; lean_object* v___x_3322_; 
v_todo_3320_ = lean_array_push(v_snd_3297_, v___x_3316_);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 1, v_todo_3320_);
lean_ctor_set(v___x_3318_, 0, v_fst_3296_);
v___x_3322_ = v___x_3318_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_fst_3296_);
lean_ctor_set(v_reuseFailAlloc_3323_, 1, v_todo_3320_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
v_a_3305_ = v___x_3322_;
goto v___jp_3304_;
}
}
}
}
else
{
lean_object* v_cs_x27_3328_; lean_object* v___x_3330_; 
lean_dec(v_b_3312_);
v_cs_x27_3328_ = l_Lean_PersistentArray_push___redArg(v_fst_3296_, v_a_3301_);
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 1, v_snd_3297_);
lean_ctor_set(v___x_3294_, 0, v_cs_x27_3328_);
v___x_3330_ = v___x_3294_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_cs_x27_3328_);
lean_ctor_set(v_reuseFailAlloc_3331_, 1, v_snd_3297_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
v_a_3305_ = v___x_3330_;
goto v___jp_3304_;
}
}
v___jp_3304_:
{
lean_object* v___x_3307_; 
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 1, v_a_3305_);
lean_ctor_set(v___x_3299_, 0, v___x_3303_);
v___x_3307_ = v___x_3299_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3303_);
lean_ctor_set(v_reuseFailAlloc_3311_, 1, v_a_3305_);
v___x_3307_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
size_t v___x_3308_; size_t v___x_3309_; 
v___x_3308_ = ((size_t)1ULL);
v___x_3309_ = lean_usize_add(v_i_3289_, v___x_3308_);
v_i_3289_ = v___x_3309_;
v_b_3290_ = v___x_3307_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_3335_, lean_object* v_as_3336_, lean_object* v_sz_3337_, lean_object* v_i_3338_, lean_object* v_b_3339_){
_start:
{
size_t v_sz_boxed_3340_; size_t v_i_boxed_3341_; lean_object* v_res_3342_; 
v_sz_boxed_3340_ = lean_unbox_usize(v_sz_3337_);
lean_dec(v_sz_3337_);
v_i_boxed_3341_ = lean_unbox_usize(v_i_3338_);
lean_dec(v_i_3338_);
v_res_3342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3335_, v_as_3336_, v_sz_boxed_3340_, v_i_boxed_3341_, v_b_3339_);
lean_dec_ref(v_as_3336_);
lean_dec(v_x_3335_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(lean_object* v_x_3343_, lean_object* v_as_3344_, size_t v_sz_3345_, size_t v_i_3346_, lean_object* v_b_3347_){
_start:
{
uint8_t v___x_3348_; 
v___x_3348_ = lean_usize_dec_lt(v_i_3346_, v_sz_3345_);
if (v___x_3348_ == 0)
{
return v_b_3347_;
}
else
{
lean_object* v_snd_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3390_; 
v_snd_3349_ = lean_ctor_get(v_b_3347_, 1);
v_isSharedCheck_3390_ = !lean_is_exclusive(v_b_3347_);
if (v_isSharedCheck_3390_ == 0)
{
lean_object* v_unused_3391_; 
v_unused_3391_ = lean_ctor_get(v_b_3347_, 0);
lean_dec(v_unused_3391_);
v___x_3351_ = v_b_3347_;
v_isShared_3352_ = v_isSharedCheck_3390_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_snd_3349_);
lean_dec(v_b_3347_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3390_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v_fst_3353_; lean_object* v_snd_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3389_; 
v_fst_3353_ = lean_ctor_get(v_snd_3349_, 0);
v_snd_3354_ = lean_ctor_get(v_snd_3349_, 1);
v_isSharedCheck_3389_ = !lean_is_exclusive(v_snd_3349_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3356_ = v_snd_3349_;
v_isShared_3357_ = v_isSharedCheck_3389_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_snd_3354_);
lean_inc(v_fst_3353_);
lean_dec(v_snd_3349_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3389_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v_a_3358_; lean_object* v_p_3359_; lean_object* v___x_3360_; lean_object* v_a_3362_; lean_object* v_b_3369_; lean_object* v___x_3370_; uint8_t v___x_3371_; 
v_a_3358_ = lean_array_uget(v_as_3344_, v_i_3346_);
v_p_3359_ = lean_ctor_get(v_a_3358_, 0);
v___x_3360_ = lean_box(0);
v_b_3369_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3359_, v_x_3343_);
v___x_3370_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3371_ = lean_int_dec_eq(v_b_3369_, v___x_3370_);
if (v___x_3371_ == 0)
{
lean_object* v___x_3373_; 
lean_inc(v_a_3358_);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 1, v_a_3358_);
lean_ctor_set(v___x_3351_, 0, v_b_3369_);
v___x_3373_ = v___x_3351_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_b_3369_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v_a_3358_);
v___x_3373_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3381_; 
v_isSharedCheck_3381_ = !lean_is_exclusive(v_a_3358_);
if (v_isSharedCheck_3381_ == 0)
{
lean_object* v_unused_3382_; lean_object* v_unused_3383_; 
v_unused_3382_ = lean_ctor_get(v_a_3358_, 1);
lean_dec(v_unused_3382_);
v_unused_3383_ = lean_ctor_get(v_a_3358_, 0);
lean_dec(v_unused_3383_);
v___x_3375_ = v_a_3358_;
v_isShared_3376_ = v_isSharedCheck_3381_;
goto v_resetjp_3374_;
}
else
{
lean_dec(v_a_3358_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3381_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v_todo_3377_; lean_object* v___x_3379_; 
v_todo_3377_ = lean_array_push(v_snd_3354_, v___x_3373_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 1, v_todo_3377_);
lean_ctor_set(v___x_3375_, 0, v_fst_3353_);
v___x_3379_ = v___x_3375_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_fst_3353_);
lean_ctor_set(v_reuseFailAlloc_3380_, 1, v_todo_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
v_a_3362_ = v___x_3379_;
goto v___jp_3361_;
}
}
}
}
else
{
lean_object* v_cs_x27_3385_; lean_object* v___x_3387_; 
lean_dec(v_b_3369_);
v_cs_x27_3385_ = l_Lean_PersistentArray_push___redArg(v_fst_3353_, v_a_3358_);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 1, v_snd_3354_);
lean_ctor_set(v___x_3351_, 0, v_cs_x27_3385_);
v___x_3387_ = v___x_3351_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_cs_x27_3385_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v_snd_3354_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
v_a_3362_ = v___x_3387_;
goto v___jp_3361_;
}
}
v___jp_3361_:
{
lean_object* v___x_3364_; 
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 1, v_a_3362_);
lean_ctor_set(v___x_3356_, 0, v___x_3360_);
v___x_3364_ = v___x_3356_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3360_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_a_3362_);
v___x_3364_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
size_t v___x_3365_; size_t v___x_3366_; lean_object* v___x_3367_; 
v___x_3365_ = ((size_t)1ULL);
v___x_3366_ = lean_usize_add(v_i_3346_, v___x_3365_);
v___x_3367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3343_, v_as_3344_, v_sz_3345_, v___x_3366_, v___x_3364_);
return v___x_3367_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_3392_, lean_object* v_as_3393_, lean_object* v_sz_3394_, lean_object* v_i_3395_, lean_object* v_b_3396_){
_start:
{
size_t v_sz_boxed_3397_; size_t v_i_boxed_3398_; lean_object* v_res_3399_; 
v_sz_boxed_3397_ = lean_unbox_usize(v_sz_3394_);
lean_dec(v_sz_3394_);
v_i_boxed_3398_ = lean_unbox_usize(v_i_3395_);
lean_dec(v_i_3395_);
v_res_3399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3392_, v_as_3393_, v_sz_boxed_3397_, v_i_boxed_3398_, v_b_3396_);
lean_dec_ref(v_as_3393_);
lean_dec(v_x_3392_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_3400_, lean_object* v_as_3401_, size_t v_sz_3402_, size_t v_i_3403_, lean_object* v_b_3404_){
_start:
{
uint8_t v___x_3405_; 
v___x_3405_ = lean_usize_dec_lt(v_i_3403_, v_sz_3402_);
if (v___x_3405_ == 0)
{
return v_b_3404_;
}
else
{
lean_object* v_snd_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3447_; 
v_snd_3406_ = lean_ctor_get(v_b_3404_, 1);
v_isSharedCheck_3447_ = !lean_is_exclusive(v_b_3404_);
if (v_isSharedCheck_3447_ == 0)
{
lean_object* v_unused_3448_; 
v_unused_3448_ = lean_ctor_get(v_b_3404_, 0);
lean_dec(v_unused_3448_);
v___x_3408_ = v_b_3404_;
v_isShared_3409_ = v_isSharedCheck_3447_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_snd_3406_);
lean_dec(v_b_3404_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3447_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v_fst_3410_; lean_object* v_snd_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3446_; 
v_fst_3410_ = lean_ctor_get(v_snd_3406_, 0);
v_snd_3411_ = lean_ctor_get(v_snd_3406_, 1);
v_isSharedCheck_3446_ = !lean_is_exclusive(v_snd_3406_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3413_ = v_snd_3406_;
v_isShared_3414_ = v_isSharedCheck_3446_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_snd_3411_);
lean_inc(v_fst_3410_);
lean_dec(v_snd_3406_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3446_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v_a_3415_; lean_object* v_p_3416_; lean_object* v___x_3417_; lean_object* v_a_3419_; lean_object* v_b_3426_; lean_object* v___x_3427_; uint8_t v___x_3428_; 
v_a_3415_ = lean_array_uget(v_as_3401_, v_i_3403_);
v_p_3416_ = lean_ctor_get(v_a_3415_, 0);
v___x_3417_ = lean_box(0);
v_b_3426_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3416_, v_x_3400_);
v___x_3427_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3428_ = lean_int_dec_eq(v_b_3426_, v___x_3427_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3430_; 
lean_inc(v_a_3415_);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 1, v_a_3415_);
lean_ctor_set(v___x_3408_, 0, v_b_3426_);
v___x_3430_ = v___x_3408_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_b_3426_);
lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_a_3415_);
v___x_3430_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3438_; 
v_isSharedCheck_3438_ = !lean_is_exclusive(v_a_3415_);
if (v_isSharedCheck_3438_ == 0)
{
lean_object* v_unused_3439_; lean_object* v_unused_3440_; 
v_unused_3439_ = lean_ctor_get(v_a_3415_, 1);
lean_dec(v_unused_3439_);
v_unused_3440_ = lean_ctor_get(v_a_3415_, 0);
lean_dec(v_unused_3440_);
v___x_3432_ = v_a_3415_;
v_isShared_3433_ = v_isSharedCheck_3438_;
goto v_resetjp_3431_;
}
else
{
lean_dec(v_a_3415_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3438_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v_todo_3434_; lean_object* v___x_3436_; 
v_todo_3434_ = lean_array_push(v_snd_3411_, v___x_3430_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v_todo_3434_);
lean_ctor_set(v___x_3432_, 0, v_fst_3410_);
v___x_3436_ = v___x_3432_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_fst_3410_);
lean_ctor_set(v_reuseFailAlloc_3437_, 1, v_todo_3434_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
v_a_3419_ = v___x_3436_;
goto v___jp_3418_;
}
}
}
}
else
{
lean_object* v_cs_x27_3442_; lean_object* v___x_3444_; 
lean_dec(v_b_3426_);
v_cs_x27_3442_ = l_Lean_PersistentArray_push___redArg(v_fst_3410_, v_a_3415_);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 1, v_snd_3411_);
lean_ctor_set(v___x_3408_, 0, v_cs_x27_3442_);
v___x_3444_ = v___x_3408_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_cs_x27_3442_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v_snd_3411_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
v_a_3419_ = v___x_3444_;
goto v___jp_3418_;
}
}
v___jp_3418_:
{
lean_object* v___x_3421_; 
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 1, v_a_3419_);
lean_ctor_set(v___x_3413_, 0, v___x_3417_);
v___x_3421_ = v___x_3413_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3417_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v_a_3419_);
v___x_3421_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
size_t v___x_3422_; size_t v___x_3423_; 
v___x_3422_ = ((size_t)1ULL);
v___x_3423_ = lean_usize_add(v_i_3403_, v___x_3422_);
v_i_3403_ = v___x_3423_;
v_b_3404_ = v___x_3421_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3449_, lean_object* v_as_3450_, lean_object* v_sz_3451_, lean_object* v_i_3452_, lean_object* v_b_3453_){
_start:
{
size_t v_sz_boxed_3454_; size_t v_i_boxed_3455_; lean_object* v_res_3456_; 
v_sz_boxed_3454_ = lean_unbox_usize(v_sz_3451_);
lean_dec(v_sz_3451_);
v_i_boxed_3455_ = lean_unbox_usize(v_i_3452_);
lean_dec(v_i_3452_);
v_res_3456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3449_, v_as_3450_, v_sz_boxed_3454_, v_i_boxed_3455_, v_b_3453_);
lean_dec_ref(v_as_3450_);
lean_dec(v_x_3449_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_3457_, lean_object* v_as_3458_, size_t v_sz_3459_, size_t v_i_3460_, lean_object* v_b_3461_){
_start:
{
uint8_t v___x_3462_; 
v___x_3462_ = lean_usize_dec_lt(v_i_3460_, v_sz_3459_);
if (v___x_3462_ == 0)
{
return v_b_3461_;
}
else
{
lean_object* v_snd_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3504_; 
v_snd_3463_ = lean_ctor_get(v_b_3461_, 1);
v_isSharedCheck_3504_ = !lean_is_exclusive(v_b_3461_);
if (v_isSharedCheck_3504_ == 0)
{
lean_object* v_unused_3505_; 
v_unused_3505_ = lean_ctor_get(v_b_3461_, 0);
lean_dec(v_unused_3505_);
v___x_3465_ = v_b_3461_;
v_isShared_3466_ = v_isSharedCheck_3504_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_snd_3463_);
lean_dec(v_b_3461_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3504_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v_fst_3467_; lean_object* v_snd_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3503_; 
v_fst_3467_ = lean_ctor_get(v_snd_3463_, 0);
v_snd_3468_ = lean_ctor_get(v_snd_3463_, 1);
v_isSharedCheck_3503_ = !lean_is_exclusive(v_snd_3463_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3470_ = v_snd_3463_;
v_isShared_3471_ = v_isSharedCheck_3503_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_snd_3468_);
lean_inc(v_fst_3467_);
lean_dec(v_snd_3463_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3503_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v_a_3472_; lean_object* v_p_3473_; lean_object* v___x_3474_; lean_object* v_a_3476_; lean_object* v_b_3483_; lean_object* v___x_3484_; uint8_t v___x_3485_; 
v_a_3472_ = lean_array_uget(v_as_3458_, v_i_3460_);
v_p_3473_ = lean_ctor_get(v_a_3472_, 0);
v___x_3474_ = lean_box(0);
v_b_3483_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3473_, v_x_3457_);
v___x_3484_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3485_ = lean_int_dec_eq(v_b_3483_, v___x_3484_);
if (v___x_3485_ == 0)
{
lean_object* v___x_3487_; 
lean_inc(v_a_3472_);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 1, v_a_3472_);
lean_ctor_set(v___x_3465_, 0, v_b_3483_);
v___x_3487_ = v___x_3465_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_b_3483_);
lean_ctor_set(v_reuseFailAlloc_3498_, 1, v_a_3472_);
v___x_3487_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3495_; 
v_isSharedCheck_3495_ = !lean_is_exclusive(v_a_3472_);
if (v_isSharedCheck_3495_ == 0)
{
lean_object* v_unused_3496_; lean_object* v_unused_3497_; 
v_unused_3496_ = lean_ctor_get(v_a_3472_, 1);
lean_dec(v_unused_3496_);
v_unused_3497_ = lean_ctor_get(v_a_3472_, 0);
lean_dec(v_unused_3497_);
v___x_3489_ = v_a_3472_;
v_isShared_3490_ = v_isSharedCheck_3495_;
goto v_resetjp_3488_;
}
else
{
lean_dec(v_a_3472_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3495_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v_todo_3491_; lean_object* v___x_3493_; 
v_todo_3491_ = lean_array_push(v_snd_3468_, v___x_3487_);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 1, v_todo_3491_);
lean_ctor_set(v___x_3489_, 0, v_fst_3467_);
v___x_3493_ = v___x_3489_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_fst_3467_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_todo_3491_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
v_a_3476_ = v___x_3493_;
goto v___jp_3475_;
}
}
}
}
else
{
lean_object* v_cs_x27_3499_; lean_object* v___x_3501_; 
lean_dec(v_b_3483_);
v_cs_x27_3499_ = l_Lean_PersistentArray_push___redArg(v_fst_3467_, v_a_3472_);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 1, v_snd_3468_);
lean_ctor_set(v___x_3465_, 0, v_cs_x27_3499_);
v___x_3501_ = v___x_3465_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_cs_x27_3499_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v_snd_3468_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
v_a_3476_ = v___x_3501_;
goto v___jp_3475_;
}
}
v___jp_3475_:
{
lean_object* v___x_3478_; 
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 1, v_a_3476_);
lean_ctor_set(v___x_3470_, 0, v___x_3474_);
v___x_3478_ = v___x_3470_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3474_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v_a_3476_);
v___x_3478_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
size_t v___x_3479_; size_t v___x_3480_; lean_object* v___x_3481_; 
v___x_3479_ = ((size_t)1ULL);
v___x_3480_ = lean_usize_add(v_i_3460_, v___x_3479_);
v___x_3481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3457_, v_as_3458_, v_sz_3459_, v___x_3480_, v___x_3478_);
return v___x_3481_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_3506_, lean_object* v_as_3507_, lean_object* v_sz_3508_, lean_object* v_i_3509_, lean_object* v_b_3510_){
_start:
{
size_t v_sz_boxed_3511_; size_t v_i_boxed_3512_; lean_object* v_res_3513_; 
v_sz_boxed_3511_ = lean_unbox_usize(v_sz_3508_);
lean_dec(v_sz_3508_);
v_i_boxed_3512_ = lean_unbox_usize(v_i_3509_);
lean_dec(v_i_3509_);
v_res_3513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3506_, v_as_3507_, v_sz_boxed_3511_, v_i_boxed_3512_, v_b_3510_);
lean_dec_ref(v_as_3507_);
lean_dec(v_x_3506_);
return v_res_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(lean_object* v_init_3514_, lean_object* v_x_3515_, lean_object* v_n_3516_, lean_object* v_b_3517_){
_start:
{
if (lean_obj_tag(v_n_3516_) == 0)
{
lean_object* v_cs_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; size_t v_sz_3521_; size_t v___x_3522_; lean_object* v___x_3523_; lean_object* v_fst_3524_; 
v_cs_3518_ = lean_ctor_get(v_n_3516_, 0);
v___x_3519_ = lean_box(0);
v___x_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3519_);
lean_ctor_set(v___x_3520_, 1, v_b_3517_);
v_sz_3521_ = lean_array_size(v_cs_3518_);
v___x_3522_ = ((size_t)0ULL);
v___x_3523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3514_, v_x_3515_, v_cs_3518_, v_sz_3521_, v___x_3522_, v___x_3520_);
v_fst_3524_ = lean_ctor_get(v___x_3523_, 0);
if (lean_obj_tag(v_fst_3524_) == 0)
{
lean_object* v_snd_3525_; lean_object* v___x_3526_; 
v_snd_3525_ = lean_ctor_get(v___x_3523_, 1);
lean_inc(v_snd_3525_);
lean_dec_ref(v___x_3523_);
v___x_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3526_, 0, v_snd_3525_);
return v___x_3526_;
}
else
{
lean_object* v_val_3527_; 
lean_inc_ref(v_fst_3524_);
lean_dec_ref(v___x_3523_);
v_val_3527_ = lean_ctor_get(v_fst_3524_, 0);
lean_inc(v_val_3527_);
lean_dec_ref_known(v_fst_3524_, 1);
return v_val_3527_;
}
}
else
{
lean_object* v_vs_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; size_t v_sz_3531_; size_t v___x_3532_; lean_object* v___x_3533_; lean_object* v_fst_3534_; 
v_vs_3528_ = lean_ctor_get(v_n_3516_, 0);
v___x_3529_ = lean_box(0);
v___x_3530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
lean_ctor_set(v___x_3530_, 1, v_b_3517_);
v_sz_3531_ = lean_array_size(v_vs_3528_);
v___x_3532_ = ((size_t)0ULL);
v___x_3533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3515_, v_vs_3528_, v_sz_3531_, v___x_3532_, v___x_3530_);
v_fst_3534_ = lean_ctor_get(v___x_3533_, 0);
if (lean_obj_tag(v_fst_3534_) == 0)
{
lean_object* v_snd_3535_; lean_object* v___x_3536_; 
v_snd_3535_ = lean_ctor_get(v___x_3533_, 1);
lean_inc(v_snd_3535_);
lean_dec_ref(v___x_3533_);
v___x_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3536_, 0, v_snd_3535_);
return v___x_3536_;
}
else
{
lean_object* v_val_3537_; 
lean_inc_ref(v_fst_3534_);
lean_dec_ref(v___x_3533_);
v_val_3537_ = lean_ctor_get(v_fst_3534_, 0);
lean_inc(v_val_3537_);
lean_dec_ref_known(v_fst_3534_, 1);
return v_val_3537_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3538_, lean_object* v_x_3539_, lean_object* v_as_3540_, size_t v_sz_3541_, size_t v_i_3542_, lean_object* v_b_3543_){
_start:
{
uint8_t v___x_3544_; 
v___x_3544_ = lean_usize_dec_lt(v_i_3542_, v_sz_3541_);
if (v___x_3544_ == 0)
{
return v_b_3543_;
}
else
{
lean_object* v_snd_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3563_; 
v_snd_3545_ = lean_ctor_get(v_b_3543_, 1);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_b_3543_);
if (v_isSharedCheck_3563_ == 0)
{
lean_object* v_unused_3564_; 
v_unused_3564_ = lean_ctor_get(v_b_3543_, 0);
lean_dec(v_unused_3564_);
v___x_3547_ = v_b_3543_;
v_isShared_3548_ = v_isSharedCheck_3563_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_snd_3545_);
lean_dec(v_b_3543_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3563_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v_a_3549_; lean_object* v___x_3550_; 
v_a_3549_ = lean_array_uget_borrowed(v_as_3540_, v_i_3542_);
lean_inc(v_snd_3545_);
v___x_3550_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3538_, v_x_3539_, v_a_3549_, v_snd_3545_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v___x_3551_; lean_object* v___x_3553_; 
v___x_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 0, v___x_3551_);
v___x_3553_ = v___x_3547_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3551_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v_snd_3545_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3556_; lean_object* v___x_3558_; 
lean_dec(v_snd_3545_);
v_a_3555_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3555_);
lean_dec_ref_known(v___x_3550_, 1);
v___x_3556_ = lean_box(0);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 1, v_a_3555_);
lean_ctor_set(v___x_3547_, 0, v___x_3556_);
v___x_3558_ = v___x_3547_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3556_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v_a_3555_);
v___x_3558_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
size_t v___x_3559_; size_t v___x_3560_; 
v___x_3559_ = ((size_t)1ULL);
v___x_3560_ = lean_usize_add(v_i_3542_, v___x_3559_);
v_i_3542_ = v___x_3560_;
v_b_3543_ = v___x_3558_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3565_, lean_object* v_x_3566_, lean_object* v_as_3567_, lean_object* v_sz_3568_, lean_object* v_i_3569_, lean_object* v_b_3570_){
_start:
{
size_t v_sz_boxed_3571_; size_t v_i_boxed_3572_; lean_object* v_res_3573_; 
v_sz_boxed_3571_ = lean_unbox_usize(v_sz_3568_);
lean_dec(v_sz_3568_);
v_i_boxed_3572_ = lean_unbox_usize(v_i_3569_);
lean_dec(v_i_3569_);
v_res_3573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3565_, v_x_3566_, v_as_3567_, v_sz_boxed_3571_, v_i_boxed_3572_, v_b_3570_);
lean_dec_ref(v_as_3567_);
lean_dec(v_x_3566_);
lean_dec_ref(v_init_3565_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3574_, lean_object* v_x_3575_, lean_object* v_n_3576_, lean_object* v_b_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3574_, v_x_3575_, v_n_3576_, v_b_3577_);
lean_dec_ref(v_n_3576_);
lean_dec(v_x_3575_);
lean_dec_ref(v_init_3574_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object* v_x_3579_, lean_object* v_t_3580_, lean_object* v_init_3581_){
_start:
{
lean_object* v_root_3582_; lean_object* v_tail_3583_; lean_object* v___x_3584_; 
v_root_3582_ = lean_ctor_get(v_t_3580_, 0);
v_tail_3583_ = lean_ctor_get(v_t_3580_, 1);
lean_inc_ref(v_init_3581_);
v___x_3584_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3581_, v_x_3579_, v_root_3582_, v_init_3581_);
lean_dec_ref(v_init_3581_);
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_object* v_a_3585_; 
v_a_3585_ = lean_ctor_get(v___x_3584_, 0);
lean_inc(v_a_3585_);
lean_dec_ref_known(v___x_3584_, 1);
return v_a_3585_;
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; size_t v_sz_3589_; size_t v___x_3590_; lean_object* v___x_3591_; lean_object* v_fst_3592_; 
v_a_3586_ = lean_ctor_get(v___x_3584_, 0);
lean_inc(v_a_3586_);
lean_dec_ref_known(v___x_3584_, 1);
v___x_3587_ = lean_box(0);
v___x_3588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3587_);
lean_ctor_set(v___x_3588_, 1, v_a_3586_);
v_sz_3589_ = lean_array_size(v_tail_3583_);
v___x_3590_ = ((size_t)0ULL);
v___x_3591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3579_, v_tail_3583_, v_sz_3589_, v___x_3590_, v___x_3588_);
v_fst_3592_ = lean_ctor_get(v___x_3591_, 0);
if (lean_obj_tag(v_fst_3592_) == 0)
{
lean_object* v_snd_3593_; 
v_snd_3593_ = lean_ctor_get(v___x_3591_, 1);
lean_inc(v_snd_3593_);
lean_dec_ref(v___x_3591_);
return v_snd_3593_;
}
else
{
lean_object* v_val_3594_; 
lean_inc_ref(v_fst_3592_);
lean_dec_ref(v___x_3591_);
v_val_3594_ = lean_ctor_get(v_fst_3592_, 0);
lean_inc(v_val_3594_);
lean_dec_ref_known(v_fst_3592_, 1);
return v_val_3594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object* v_x_3595_, lean_object* v_t_3596_, lean_object* v_init_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3595_, v_t_3596_, v_init_3597_);
lean_dec_ref(v_t_3596_);
lean_dec(v_x_3595_);
return v_res_3598_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3599_ = lean_unsigned_to_nat(32u);
v___x_3600_ = lean_mk_empty_array_with_capacity(v___x_3599_);
v___x_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3600_);
return v___x_3601_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1(void){
_start:
{
size_t v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v_cs_x27_3607_; 
v___x_3602_ = ((size_t)5ULL);
v___x_3603_ = lean_unsigned_to_nat(0u);
v___x_3604_ = lean_unsigned_to_nat(32u);
v___x_3605_ = lean_mk_empty_array_with_capacity(v___x_3604_);
v___x_3606_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0);
v_cs_x27_3607_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_3607_, 0, v___x_3606_);
lean_ctor_set(v_cs_x27_3607_, 1, v___x_3605_);
lean_ctor_set(v_cs_x27_3607_, 2, v___x_3603_);
lean_ctor_set(v_cs_x27_3607_, 3, v___x_3603_);
lean_ctor_set_usize(v_cs_x27_3607_, 4, v___x_3602_);
return v_cs_x27_3607_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_3610_; lean_object* v_cs_x27_3611_; lean_object* v___x_3612_; 
v_todo_3610_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2));
v_cs_x27_3611_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1);
v___x_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3612_, 0, v_cs_x27_3611_);
lean_ctor_set(v___x_3612_, 1, v_todo_3610_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object* v_x_3613_, lean_object* v_cs_3614_){
_start:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v_fst_3617_; lean_object* v_snd_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
v___x_3615_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3);
v___x_3616_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3613_, v_cs_3614_, v___x_3615_);
v_fst_3617_ = lean_ctor_get(v___x_3616_, 0);
v_snd_3618_ = lean_ctor_get(v___x_3616_, 1);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3616_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_snd_3618_);
lean_inc(v_fst_3617_);
lean_dec(v___x_3616_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_fst_3617_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v_snd_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object* v_x_3626_, lean_object* v_cs_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3626_, v_cs_3627_);
lean_dec_ref(v_cs_3627_);
lean_dec(v_x_3626_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object* v_x_3629_, lean_object* v_cs_3630_){
_start:
{
lean_object* v___x_3631_; 
v___x_3631_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3629_, v_cs_3630_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object* v_x_3632_, lean_object* v_cs_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(v_x_3632_, v_cs_3633_);
lean_dec_ref(v_cs_3633_);
lean_dec(v_x_3632_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(lean_object* v_a_3635_, lean_object* v_y_3636_, lean_object* v_fst_3637_, lean_object* v_s_3638_){
_start:
{
lean_object* v_structs_3639_; lean_object* v_typeIdOf_3640_; lean_object* v_exprToStructId_3641_; lean_object* v_exprToStructIdEntries_3642_; lean_object* v_forbiddenNatModules_3643_; lean_object* v_natStructs_3644_; lean_object* v_natTypeIdOf_3645_; lean_object* v_exprToNatStructId_3646_; lean_object* v___x_3647_; uint8_t v___x_3648_; 
v_structs_3639_ = lean_ctor_get(v_s_3638_, 0);
v_typeIdOf_3640_ = lean_ctor_get(v_s_3638_, 1);
v_exprToStructId_3641_ = lean_ctor_get(v_s_3638_, 2);
v_exprToStructIdEntries_3642_ = lean_ctor_get(v_s_3638_, 3);
v_forbiddenNatModules_3643_ = lean_ctor_get(v_s_3638_, 4);
v_natStructs_3644_ = lean_ctor_get(v_s_3638_, 5);
v_natTypeIdOf_3645_ = lean_ctor_get(v_s_3638_, 6);
v_exprToNatStructId_3646_ = lean_ctor_get(v_s_3638_, 7);
v___x_3647_ = lean_array_get_size(v_structs_3639_);
v___x_3648_ = lean_nat_dec_lt(v_a_3635_, v___x_3647_);
if (v___x_3648_ == 0)
{
lean_dec_ref(v_fst_3637_);
return v_s_3638_;
}
else
{
lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3710_; 
lean_inc_ref(v_exprToNatStructId_3646_);
lean_inc_ref(v_natTypeIdOf_3645_);
lean_inc_ref(v_natStructs_3644_);
lean_inc_ref(v_forbiddenNatModules_3643_);
lean_inc_ref(v_exprToStructIdEntries_3642_);
lean_inc_ref(v_exprToStructId_3641_);
lean_inc_ref(v_typeIdOf_3640_);
lean_inc_ref(v_structs_3639_);
v_isSharedCheck_3710_ = !lean_is_exclusive(v_s_3638_);
if (v_isSharedCheck_3710_ == 0)
{
lean_object* v_unused_3711_; lean_object* v_unused_3712_; lean_object* v_unused_3713_; lean_object* v_unused_3714_; lean_object* v_unused_3715_; lean_object* v_unused_3716_; lean_object* v_unused_3717_; lean_object* v_unused_3718_; 
v_unused_3711_ = lean_ctor_get(v_s_3638_, 7);
lean_dec(v_unused_3711_);
v_unused_3712_ = lean_ctor_get(v_s_3638_, 6);
lean_dec(v_unused_3712_);
v_unused_3713_ = lean_ctor_get(v_s_3638_, 5);
lean_dec(v_unused_3713_);
v_unused_3714_ = lean_ctor_get(v_s_3638_, 4);
lean_dec(v_unused_3714_);
v_unused_3715_ = lean_ctor_get(v_s_3638_, 3);
lean_dec(v_unused_3715_);
v_unused_3716_ = lean_ctor_get(v_s_3638_, 2);
lean_dec(v_unused_3716_);
v_unused_3717_ = lean_ctor_get(v_s_3638_, 1);
lean_dec(v_unused_3717_);
v_unused_3718_ = lean_ctor_get(v_s_3638_, 0);
lean_dec(v_unused_3718_);
v___x_3650_ = v_s_3638_;
v_isShared_3651_ = v_isSharedCheck_3710_;
goto v_resetjp_3649_;
}
else
{
lean_dec(v_s_3638_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3710_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v_v_3652_; lean_object* v_id_3653_; lean_object* v_ringId_x3f_3654_; lean_object* v_type_3655_; lean_object* v_u_3656_; lean_object* v_intModuleInst_3657_; lean_object* v_leInst_x3f_3658_; lean_object* v_ltInst_x3f_3659_; lean_object* v_lawfulOrderLTInst_x3f_3660_; lean_object* v_isPreorderInst_x3f_3661_; lean_object* v_orderedAddInst_x3f_3662_; lean_object* v_isLinearInst_x3f_3663_; lean_object* v_noNatDivInst_x3f_3664_; lean_object* v_ringInst_x3f_3665_; lean_object* v_commRingInst_x3f_3666_; lean_object* v_orderedRingInst_x3f_3667_; lean_object* v_fieldInst_x3f_3668_; lean_object* v_charInst_x3f_3669_; lean_object* v_zero_3670_; lean_object* v_ofNatZero_3671_; lean_object* v_one_x3f_3672_; lean_object* v_leFn_x3f_3673_; lean_object* v_ltFn_x3f_3674_; lean_object* v_addFn_3675_; lean_object* v_zsmulFn_3676_; lean_object* v_nsmulFn_3677_; lean_object* v_zsmulFn_x3f_3678_; lean_object* v_nsmulFn_x3f_3679_; lean_object* v_homomulFn_x3f_3680_; lean_object* v_subFn_3681_; lean_object* v_negFn_3682_; lean_object* v_vars_3683_; lean_object* v_varMap_3684_; lean_object* v_lowers_3685_; lean_object* v_uppers_3686_; lean_object* v_diseqs_3687_; lean_object* v_assignment_3688_; uint8_t v_caseSplits_3689_; lean_object* v_conflict_x3f_3690_; lean_object* v_diseqSplits_3691_; lean_object* v_elimEqs_3692_; lean_object* v_elimStack_3693_; lean_object* v_occurs_3694_; lean_object* v_ignored_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3709_; 
v_v_3652_ = lean_array_fget(v_structs_3639_, v_a_3635_);
v_id_3653_ = lean_ctor_get(v_v_3652_, 0);
v_ringId_x3f_3654_ = lean_ctor_get(v_v_3652_, 1);
v_type_3655_ = lean_ctor_get(v_v_3652_, 2);
v_u_3656_ = lean_ctor_get(v_v_3652_, 3);
v_intModuleInst_3657_ = lean_ctor_get(v_v_3652_, 4);
v_leInst_x3f_3658_ = lean_ctor_get(v_v_3652_, 5);
v_ltInst_x3f_3659_ = lean_ctor_get(v_v_3652_, 6);
v_lawfulOrderLTInst_x3f_3660_ = lean_ctor_get(v_v_3652_, 7);
v_isPreorderInst_x3f_3661_ = lean_ctor_get(v_v_3652_, 8);
v_orderedAddInst_x3f_3662_ = lean_ctor_get(v_v_3652_, 9);
v_isLinearInst_x3f_3663_ = lean_ctor_get(v_v_3652_, 10);
v_noNatDivInst_x3f_3664_ = lean_ctor_get(v_v_3652_, 11);
v_ringInst_x3f_3665_ = lean_ctor_get(v_v_3652_, 12);
v_commRingInst_x3f_3666_ = lean_ctor_get(v_v_3652_, 13);
v_orderedRingInst_x3f_3667_ = lean_ctor_get(v_v_3652_, 14);
v_fieldInst_x3f_3668_ = lean_ctor_get(v_v_3652_, 15);
v_charInst_x3f_3669_ = lean_ctor_get(v_v_3652_, 16);
v_zero_3670_ = lean_ctor_get(v_v_3652_, 17);
v_ofNatZero_3671_ = lean_ctor_get(v_v_3652_, 18);
v_one_x3f_3672_ = lean_ctor_get(v_v_3652_, 19);
v_leFn_x3f_3673_ = lean_ctor_get(v_v_3652_, 20);
v_ltFn_x3f_3674_ = lean_ctor_get(v_v_3652_, 21);
v_addFn_3675_ = lean_ctor_get(v_v_3652_, 22);
v_zsmulFn_3676_ = lean_ctor_get(v_v_3652_, 23);
v_nsmulFn_3677_ = lean_ctor_get(v_v_3652_, 24);
v_zsmulFn_x3f_3678_ = lean_ctor_get(v_v_3652_, 25);
v_nsmulFn_x3f_3679_ = lean_ctor_get(v_v_3652_, 26);
v_homomulFn_x3f_3680_ = lean_ctor_get(v_v_3652_, 27);
v_subFn_3681_ = lean_ctor_get(v_v_3652_, 28);
v_negFn_3682_ = lean_ctor_get(v_v_3652_, 29);
v_vars_3683_ = lean_ctor_get(v_v_3652_, 30);
v_varMap_3684_ = lean_ctor_get(v_v_3652_, 31);
v_lowers_3685_ = lean_ctor_get(v_v_3652_, 32);
v_uppers_3686_ = lean_ctor_get(v_v_3652_, 33);
v_diseqs_3687_ = lean_ctor_get(v_v_3652_, 34);
v_assignment_3688_ = lean_ctor_get(v_v_3652_, 35);
v_caseSplits_3689_ = lean_ctor_get_uint8(v_v_3652_, sizeof(void*)*42);
v_conflict_x3f_3690_ = lean_ctor_get(v_v_3652_, 36);
v_diseqSplits_3691_ = lean_ctor_get(v_v_3652_, 37);
v_elimEqs_3692_ = lean_ctor_get(v_v_3652_, 38);
v_elimStack_3693_ = lean_ctor_get(v_v_3652_, 39);
v_occurs_3694_ = lean_ctor_get(v_v_3652_, 40);
v_ignored_3695_ = lean_ctor_get(v_v_3652_, 41);
v_isSharedCheck_3709_ = !lean_is_exclusive(v_v_3652_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3697_ = v_v_3652_;
v_isShared_3698_ = v_isSharedCheck_3709_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_ignored_3695_);
lean_inc(v_occurs_3694_);
lean_inc(v_elimStack_3693_);
lean_inc(v_elimEqs_3692_);
lean_inc(v_diseqSplits_3691_);
lean_inc(v_conflict_x3f_3690_);
lean_inc(v_assignment_3688_);
lean_inc(v_diseqs_3687_);
lean_inc(v_uppers_3686_);
lean_inc(v_lowers_3685_);
lean_inc(v_varMap_3684_);
lean_inc(v_vars_3683_);
lean_inc(v_negFn_3682_);
lean_inc(v_subFn_3681_);
lean_inc(v_homomulFn_x3f_3680_);
lean_inc(v_nsmulFn_x3f_3679_);
lean_inc(v_zsmulFn_x3f_3678_);
lean_inc(v_nsmulFn_3677_);
lean_inc(v_zsmulFn_3676_);
lean_inc(v_addFn_3675_);
lean_inc(v_ltFn_x3f_3674_);
lean_inc(v_leFn_x3f_3673_);
lean_inc(v_one_x3f_3672_);
lean_inc(v_ofNatZero_3671_);
lean_inc(v_zero_3670_);
lean_inc(v_charInst_x3f_3669_);
lean_inc(v_fieldInst_x3f_3668_);
lean_inc(v_orderedRingInst_x3f_3667_);
lean_inc(v_commRingInst_x3f_3666_);
lean_inc(v_ringInst_x3f_3665_);
lean_inc(v_noNatDivInst_x3f_3664_);
lean_inc(v_isLinearInst_x3f_3663_);
lean_inc(v_orderedAddInst_x3f_3662_);
lean_inc(v_isPreorderInst_x3f_3661_);
lean_inc(v_lawfulOrderLTInst_x3f_3660_);
lean_inc(v_ltInst_x3f_3659_);
lean_inc(v_leInst_x3f_3658_);
lean_inc(v_intModuleInst_3657_);
lean_inc(v_u_3656_);
lean_inc(v_type_3655_);
lean_inc(v_ringId_x3f_3654_);
lean_inc(v_id_3653_);
lean_dec(v_v_3652_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3709_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3699_; lean_object* v_xs_x27_3700_; lean_object* v___x_3701_; lean_object* v___x_3703_; 
v___x_3699_ = lean_box(0);
v_xs_x27_3700_ = lean_array_fset(v_structs_3639_, v_a_3635_, v___x_3699_);
v___x_3701_ = l_Lean_PersistentArray_set___redArg(v_diseqs_3687_, v_y_3636_, v_fst_3637_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 34, v___x_3701_);
v___x_3703_ = v___x_3697_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_id_3653_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_ringId_x3f_3654_);
lean_ctor_set(v_reuseFailAlloc_3708_, 2, v_type_3655_);
lean_ctor_set(v_reuseFailAlloc_3708_, 3, v_u_3656_);
lean_ctor_set(v_reuseFailAlloc_3708_, 4, v_intModuleInst_3657_);
lean_ctor_set(v_reuseFailAlloc_3708_, 5, v_leInst_x3f_3658_);
lean_ctor_set(v_reuseFailAlloc_3708_, 6, v_ltInst_x3f_3659_);
lean_ctor_set(v_reuseFailAlloc_3708_, 7, v_lawfulOrderLTInst_x3f_3660_);
lean_ctor_set(v_reuseFailAlloc_3708_, 8, v_isPreorderInst_x3f_3661_);
lean_ctor_set(v_reuseFailAlloc_3708_, 9, v_orderedAddInst_x3f_3662_);
lean_ctor_set(v_reuseFailAlloc_3708_, 10, v_isLinearInst_x3f_3663_);
lean_ctor_set(v_reuseFailAlloc_3708_, 11, v_noNatDivInst_x3f_3664_);
lean_ctor_set(v_reuseFailAlloc_3708_, 12, v_ringInst_x3f_3665_);
lean_ctor_set(v_reuseFailAlloc_3708_, 13, v_commRingInst_x3f_3666_);
lean_ctor_set(v_reuseFailAlloc_3708_, 14, v_orderedRingInst_x3f_3667_);
lean_ctor_set(v_reuseFailAlloc_3708_, 15, v_fieldInst_x3f_3668_);
lean_ctor_set(v_reuseFailAlloc_3708_, 16, v_charInst_x3f_3669_);
lean_ctor_set(v_reuseFailAlloc_3708_, 17, v_zero_3670_);
lean_ctor_set(v_reuseFailAlloc_3708_, 18, v_ofNatZero_3671_);
lean_ctor_set(v_reuseFailAlloc_3708_, 19, v_one_x3f_3672_);
lean_ctor_set(v_reuseFailAlloc_3708_, 20, v_leFn_x3f_3673_);
lean_ctor_set(v_reuseFailAlloc_3708_, 21, v_ltFn_x3f_3674_);
lean_ctor_set(v_reuseFailAlloc_3708_, 22, v_addFn_3675_);
lean_ctor_set(v_reuseFailAlloc_3708_, 23, v_zsmulFn_3676_);
lean_ctor_set(v_reuseFailAlloc_3708_, 24, v_nsmulFn_3677_);
lean_ctor_set(v_reuseFailAlloc_3708_, 25, v_zsmulFn_x3f_3678_);
lean_ctor_set(v_reuseFailAlloc_3708_, 26, v_nsmulFn_x3f_3679_);
lean_ctor_set(v_reuseFailAlloc_3708_, 27, v_homomulFn_x3f_3680_);
lean_ctor_set(v_reuseFailAlloc_3708_, 28, v_subFn_3681_);
lean_ctor_set(v_reuseFailAlloc_3708_, 29, v_negFn_3682_);
lean_ctor_set(v_reuseFailAlloc_3708_, 30, v_vars_3683_);
lean_ctor_set(v_reuseFailAlloc_3708_, 31, v_varMap_3684_);
lean_ctor_set(v_reuseFailAlloc_3708_, 32, v_lowers_3685_);
lean_ctor_set(v_reuseFailAlloc_3708_, 33, v_uppers_3686_);
lean_ctor_set(v_reuseFailAlloc_3708_, 34, v___x_3701_);
lean_ctor_set(v_reuseFailAlloc_3708_, 35, v_assignment_3688_);
lean_ctor_set(v_reuseFailAlloc_3708_, 36, v_conflict_x3f_3690_);
lean_ctor_set(v_reuseFailAlloc_3708_, 37, v_diseqSplits_3691_);
lean_ctor_set(v_reuseFailAlloc_3708_, 38, v_elimEqs_3692_);
lean_ctor_set(v_reuseFailAlloc_3708_, 39, v_elimStack_3693_);
lean_ctor_set(v_reuseFailAlloc_3708_, 40, v_occurs_3694_);
lean_ctor_set(v_reuseFailAlloc_3708_, 41, v_ignored_3695_);
lean_ctor_set_uint8(v_reuseFailAlloc_3708_, sizeof(void*)*42, v_caseSplits_3689_);
v___x_3703_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
lean_object* v___x_3704_; lean_object* v___x_3706_; 
v___x_3704_ = lean_array_fset(v_xs_x27_3700_, v_a_3635_, v___x_3703_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 0, v___x_3704_);
v___x_3706_ = v___x_3650_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3704_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v_typeIdOf_3640_);
lean_ctor_set(v_reuseFailAlloc_3707_, 2, v_exprToStructId_3641_);
lean_ctor_set(v_reuseFailAlloc_3707_, 3, v_exprToStructIdEntries_3642_);
lean_ctor_set(v_reuseFailAlloc_3707_, 4, v_forbiddenNatModules_3643_);
lean_ctor_set(v_reuseFailAlloc_3707_, 5, v_natStructs_3644_);
lean_ctor_set(v_reuseFailAlloc_3707_, 6, v_natTypeIdOf_3645_);
lean_ctor_set(v_reuseFailAlloc_3707_, 7, v_exprToNatStructId_3646_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed(lean_object* v_a_3719_, lean_object* v_y_3720_, lean_object* v_fst_3721_, lean_object* v_s_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(v_a_3719_, v_y_3720_, v_fst_3721_, v_s_3722_);
lean_dec(v_y_3720_);
lean_dec(v_a_3719_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object* v_a_3724_, lean_object* v_x_3725_, lean_object* v_c_3726_, lean_object* v_as_3727_, size_t v_sz_3728_, size_t v_i_3729_, lean_object* v_b_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v_a_3744_; uint8_t v___x_3748_; 
v___x_3748_ = lean_usize_dec_lt(v_i_3729_, v_sz_3728_);
if (v___x_3748_ == 0)
{
lean_object* v___x_3749_; 
lean_dec_ref(v_c_3726_);
v___x_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3749_, 0, v_b_3730_);
return v___x_3749_;
}
else
{
lean_object* v_a_3750_; lean_object* v_fst_3751_; lean_object* v_snd_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
lean_dec_ref(v_b_3730_);
v_a_3750_ = lean_array_uget_borrowed(v_as_3727_, v_i_3729_);
v_fst_3751_ = lean_ctor_get(v_a_3750_, 0);
v_snd_3752_ = lean_ctor_get(v_a_3750_, 1);
v___x_3753_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
lean_inc(v_snd_3752_);
lean_inc(v_fst_3751_);
lean_inc_ref(v_c_3726_);
v___x_3754_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_3724_, v_x_3725_, v_c_3726_, v_fst_3751_, v_snd_3752_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___x_3754_, 1);
if (lean_obj_tag(v_a_3755_) == 1)
{
lean_object* v_val_3756_; lean_object* v___x_3757_; 
v_val_3756_ = lean_ctor_get(v_a_3755_, 0);
lean_inc(v_val_3756_);
lean_dec_ref_known(v_a_3755_, 1);
v___x_3757_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_val_3756_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_object* v___x_3758_; 
lean_dec_ref_known(v___x_3757_, 1);
v___x_3758_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3768_; 
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3761_ = v___x_3758_;
v_isShared_3762_ = v_isSharedCheck_3768_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3758_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3768_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
uint8_t v___x_3763_; 
v___x_3763_ = lean_unbox(v_a_3759_);
lean_dec(v_a_3759_);
if (v___x_3763_ == 0)
{
lean_del_object(v___x_3761_);
v_a_3744_ = v___x_3753_;
goto v___jp_3743_;
}
else
{
lean_object* v___x_3764_; lean_object* v___x_3766_; 
lean_dec_ref(v_c_3726_);
v___x_3764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_3762_ == 0)
{
lean_ctor_set(v___x_3761_, 0, v___x_3764_);
v___x_3766_ = v___x_3761_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3764_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
else
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
lean_dec_ref(v_c_3726_);
v_a_3769_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3758_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3758_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3769_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_dec_ref(v_c_3726_);
v_a_3777_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3757_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3757_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
else
{
lean_object* v___x_3785_; 
lean_dec(v_a_3755_);
v___x_3785_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_snd_3752_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_dec_ref_known(v___x_3785_, 1);
v_a_3744_ = v___x_3753_;
goto v___jp_3743_;
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
lean_dec_ref(v_c_3726_);
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3785_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3785_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
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
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_dec_ref(v_c_3726_);
v_a_3794_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3754_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3754_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
v___jp_3743_:
{
size_t v___x_3745_; size_t v___x_3746_; 
v___x_3745_ = ((size_t)1ULL);
v___x_3746_ = lean_usize_add(v_i_3729_, v___x_3745_);
lean_inc_ref(v_a_3744_);
v_i_3729_ = v___x_3746_;
v_b_3730_ = v_a_3744_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object** _args){
lean_object* v_a_3802_ = _args[0];
lean_object* v_x_3803_ = _args[1];
lean_object* v_c_3804_ = _args[2];
lean_object* v_as_3805_ = _args[3];
lean_object* v_sz_3806_ = _args[4];
lean_object* v_i_3807_ = _args[5];
lean_object* v_b_3808_ = _args[6];
lean_object* v___y_3809_ = _args[7];
lean_object* v___y_3810_ = _args[8];
lean_object* v___y_3811_ = _args[9];
lean_object* v___y_3812_ = _args[10];
lean_object* v___y_3813_ = _args[11];
lean_object* v___y_3814_ = _args[12];
lean_object* v___y_3815_ = _args[13];
lean_object* v___y_3816_ = _args[14];
lean_object* v___y_3817_ = _args[15];
lean_object* v___y_3818_ = _args[16];
lean_object* v___y_3819_ = _args[17];
lean_object* v___y_3820_ = _args[18];
_start:
{
size_t v_sz_boxed_3821_; size_t v_i_boxed_3822_; lean_object* v_res_3823_; 
v_sz_boxed_3821_ = lean_unbox_usize(v_sz_3806_);
lean_dec(v_sz_3806_);
v_i_boxed_3822_ = lean_unbox_usize(v_i_3807_);
lean_dec(v_i_3807_);
v_res_3823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3802_, v_x_3803_, v_c_3804_, v_as_3805_, v_sz_boxed_3821_, v_i_boxed_3822_, v_b_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec(v___y_3809_);
lean_dec_ref(v_as_3805_);
lean_dec(v_x_3803_);
lean_dec(v_a_3802_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object* v_a_3824_, lean_object* v_x_3825_, lean_object* v_c_3826_, lean_object* v_y_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_){
_start:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3840_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_3841_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3900_; 
v_a_3842_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3844_ = v___x_3841_;
v_isShared_3845_ = v_isSharedCheck_3900_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3841_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3900_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
uint8_t v___x_3846_; 
v___x_3846_ = lean_unbox(v_a_3842_);
lean_dec(v_a_3842_);
if (v___x_3846_ == 0)
{
lean_object* v___x_3847_; 
lean_del_object(v___x_3844_);
v___x_3847_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v_a_3848_; lean_object* v___y_3850_; lean_object* v_diseqs_3883_; lean_object* v_size_3884_; uint8_t v___x_3885_; 
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_a_3848_);
lean_dec_ref_known(v___x_3847_, 1);
v_diseqs_3883_ = lean_ctor_get(v_a_3848_, 34);
lean_inc_ref(v_diseqs_3883_);
lean_dec(v_a_3848_);
v_size_3884_ = lean_ctor_get(v_diseqs_3883_, 2);
v___x_3885_ = lean_nat_dec_lt(v_y_3827_, v_size_3884_);
if (v___x_3885_ == 0)
{
lean_object* v___x_3886_; 
lean_dec_ref(v_diseqs_3883_);
v___x_3886_ = l_outOfBounds___redArg(v___x_3840_);
v___y_3850_ = v___x_3886_;
goto v___jp_3849_;
}
else
{
lean_object* v___x_3887_; 
v___x_3887_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3840_, v_diseqs_3883_, v_y_3827_);
lean_dec_ref(v_diseqs_3883_);
v___y_3850_ = v___x_3887_;
goto v___jp_3849_;
}
v___jp_3849_:
{
lean_object* v___x_3851_; lean_object* v_fst_3852_; lean_object* v_snd_3853_; lean_object* v___f_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v___x_3851_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3825_, v___y_3850_);
lean_dec_ref(v___y_3850_);
v_fst_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_fst_3852_);
v_snd_3853_ = lean_ctor_get(v___x_3851_, 1);
lean_inc(v_snd_3853_);
lean_dec_ref(v___x_3851_);
lean_inc(v_a_3828_);
v___f_3854_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3854_, 0, v_a_3828_);
lean_closure_set(v___f_3854_, 1, v_y_3827_);
lean_closure_set(v___f_3854_, 2, v_fst_3852_);
v___x_3855_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3856_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3855_, v___f_3854_, v_a_3829_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v___x_3857_; lean_object* v___x_3858_; size_t v_sz_3859_; size_t v___x_3860_; lean_object* v___x_3861_; 
lean_dec_ref_known(v___x_3856_, 1);
v___x_3857_ = lean_box(0);
v___x_3858_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_3859_ = lean_array_size(v_snd_3853_);
v___x_3860_ = ((size_t)0ULL);
v___x_3861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3824_, v_x_3825_, v_c_3826_, v_snd_3853_, v_sz_3859_, v___x_3860_, v___x_3858_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_);
lean_dec(v_snd_3853_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3874_; 
v_a_3862_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3864_ = v___x_3861_;
v_isShared_3865_ = v_isSharedCheck_3874_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3861_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3874_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v_fst_3866_; 
v_fst_3866_ = lean_ctor_get(v_a_3862_, 0);
lean_inc(v_fst_3866_);
lean_dec(v_a_3862_);
if (lean_obj_tag(v_fst_3866_) == 0)
{
lean_object* v___x_3868_; 
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 0, v___x_3857_);
v___x_3868_ = v___x_3864_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v___x_3857_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
else
{
lean_object* v_val_3870_; lean_object* v___x_3872_; 
v_val_3870_ = lean_ctor_get(v_fst_3866_, 0);
lean_inc(v_val_3870_);
lean_dec_ref_known(v_fst_3866_, 1);
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 0, v_val_3870_);
v___x_3872_ = v___x_3864_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_val_3870_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
else
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3882_; 
v_a_3875_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3877_ = v___x_3861_;
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3861_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3880_; 
if (v_isShared_3878_ == 0)
{
v___x_3880_ = v___x_3877_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_a_3875_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
}
else
{
lean_dec(v_snd_3853_);
lean_dec_ref(v_c_3826_);
return v___x_3856_;
}
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_dec(v_y_3827_);
lean_dec_ref(v_c_3826_);
v_a_3888_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3847_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3847_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
else
{
lean_object* v___x_3896_; lean_object* v___x_3898_; 
lean_dec(v_y_3827_);
lean_dec_ref(v_c_3826_);
v___x_3896_ = lean_box(0);
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 0, v___x_3896_);
v___x_3898_ = v___x_3844_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3896_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
else
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
lean_dec(v_y_3827_);
lean_dec_ref(v_c_3826_);
v_a_3901_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3841_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3841_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object* v_a_3909_, lean_object* v_x_3910_, lean_object* v_c_3911_, lean_object* v_y_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v_a_3909_, v_x_3910_, v_c_3911_, v_y_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_);
lean_dec(v_a_3923_);
lean_dec_ref(v_a_3922_);
lean_dec(v_a_3921_);
lean_dec_ref(v_a_3920_);
lean_dec(v_a_3919_);
lean_dec_ref(v_a_3918_);
lean_dec(v_a_3917_);
lean_dec_ref(v_a_3916_);
lean_dec(v_a_3915_);
lean_dec(v_a_3914_);
lean_dec(v_a_3913_);
lean_dec(v_x_3910_);
lean_dec(v_a_3909_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object* v_a_3926_, lean_object* v_x_3927_, lean_object* v_c_3928_, lean_object* v_y_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_){
_start:
{
lean_object* v___x_3942_; 
lean_inc(v_y_3929_);
lean_inc_ref(v_c_3928_);
lean_inc(v_x_3927_);
lean_inc(v_a_3926_);
v___x_3942_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_3926_, v_x_3927_, v_c_3928_, v_y_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v___x_3943_; 
lean_dec_ref_known(v___x_3942_, 1);
lean_inc(v_y_3929_);
lean_inc_ref(v_c_3928_);
lean_inc(v_x_3927_);
lean_inc(v_a_3926_);
v___x_3943_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_3926_, v_x_3927_, v_c_3928_, v_y_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v___x_3944_; lean_object* v___x_3945_; 
lean_dec_ref_known(v___x_3943_, 1);
v___x_3944_ = lean_nat_to_int(v_a_3926_);
v___x_3945_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v___x_3944_, v_x_3927_, v_c_3928_, v_y_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
lean_dec(v_x_3927_);
lean_dec(v___x_3944_);
return v___x_3945_;
}
else
{
lean_dec(v_y_3929_);
lean_dec_ref(v_c_3928_);
lean_dec(v_x_3927_);
lean_dec(v_a_3926_);
return v___x_3943_;
}
}
else
{
lean_dec(v_y_3929_);
lean_dec_ref(v_c_3928_);
lean_dec(v_x_3927_);
lean_dec(v_a_3926_);
return v___x_3942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object* v_a_3946_, lean_object* v_x_3947_, lean_object* v_c_3948_, lean_object* v_y_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_){
_start:
{
lean_object* v_res_3962_; 
v_res_3962_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_3946_, v_x_3947_, v_c_3948_, v_y_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_);
lean_dec(v_a_3960_);
lean_dec_ref(v_a_3959_);
lean_dec(v_a_3958_);
lean_dec_ref(v_a_3957_);
lean_dec(v_a_3956_);
lean_dec_ref(v_a_3955_);
lean_dec(v_a_3954_);
lean_dec_ref(v_a_3953_);
lean_dec(v_a_3952_);
lean_dec(v_a_3951_);
lean_dec(v_a_3950_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(lean_object* v_a_3963_, lean_object* v_x_3964_, lean_object* v_s_3965_){
_start:
{
lean_object* v_structs_3966_; lean_object* v_typeIdOf_3967_; lean_object* v_exprToStructId_3968_; lean_object* v_exprToStructIdEntries_3969_; lean_object* v_forbiddenNatModules_3970_; lean_object* v_natStructs_3971_; lean_object* v_natTypeIdOf_3972_; lean_object* v_exprToNatStructId_3973_; lean_object* v___x_3974_; uint8_t v___x_3975_; 
v_structs_3966_ = lean_ctor_get(v_s_3965_, 0);
v_typeIdOf_3967_ = lean_ctor_get(v_s_3965_, 1);
v_exprToStructId_3968_ = lean_ctor_get(v_s_3965_, 2);
v_exprToStructIdEntries_3969_ = lean_ctor_get(v_s_3965_, 3);
v_forbiddenNatModules_3970_ = lean_ctor_get(v_s_3965_, 4);
v_natStructs_3971_ = lean_ctor_get(v_s_3965_, 5);
v_natTypeIdOf_3972_ = lean_ctor_get(v_s_3965_, 6);
v_exprToNatStructId_3973_ = lean_ctor_get(v_s_3965_, 7);
v___x_3974_ = lean_array_get_size(v_structs_3966_);
v___x_3975_ = lean_nat_dec_lt(v_a_3963_, v___x_3974_);
if (v___x_3975_ == 0)
{
return v_s_3965_;
}
else
{
lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_4038_; 
lean_inc_ref(v_exprToNatStructId_3973_);
lean_inc_ref(v_natTypeIdOf_3972_);
lean_inc_ref(v_natStructs_3971_);
lean_inc_ref(v_forbiddenNatModules_3970_);
lean_inc_ref(v_exprToStructIdEntries_3969_);
lean_inc_ref(v_exprToStructId_3968_);
lean_inc_ref(v_typeIdOf_3967_);
lean_inc_ref(v_structs_3966_);
v_isSharedCheck_4038_ = !lean_is_exclusive(v_s_3965_);
if (v_isSharedCheck_4038_ == 0)
{
lean_object* v_unused_4039_; lean_object* v_unused_4040_; lean_object* v_unused_4041_; lean_object* v_unused_4042_; lean_object* v_unused_4043_; lean_object* v_unused_4044_; lean_object* v_unused_4045_; lean_object* v_unused_4046_; 
v_unused_4039_ = lean_ctor_get(v_s_3965_, 7);
lean_dec(v_unused_4039_);
v_unused_4040_ = lean_ctor_get(v_s_3965_, 6);
lean_dec(v_unused_4040_);
v_unused_4041_ = lean_ctor_get(v_s_3965_, 5);
lean_dec(v_unused_4041_);
v_unused_4042_ = lean_ctor_get(v_s_3965_, 4);
lean_dec(v_unused_4042_);
v_unused_4043_ = lean_ctor_get(v_s_3965_, 3);
lean_dec(v_unused_4043_);
v_unused_4044_ = lean_ctor_get(v_s_3965_, 2);
lean_dec(v_unused_4044_);
v_unused_4045_ = lean_ctor_get(v_s_3965_, 1);
lean_dec(v_unused_4045_);
v_unused_4046_ = lean_ctor_get(v_s_3965_, 0);
lean_dec(v_unused_4046_);
v___x_3977_ = v_s_3965_;
v_isShared_3978_ = v_isSharedCheck_4038_;
goto v_resetjp_3976_;
}
else
{
lean_dec(v_s_3965_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_4038_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v_v_3979_; lean_object* v_id_3980_; lean_object* v_ringId_x3f_3981_; lean_object* v_type_3982_; lean_object* v_u_3983_; lean_object* v_intModuleInst_3984_; lean_object* v_leInst_x3f_3985_; lean_object* v_ltInst_x3f_3986_; lean_object* v_lawfulOrderLTInst_x3f_3987_; lean_object* v_isPreorderInst_x3f_3988_; lean_object* v_orderedAddInst_x3f_3989_; lean_object* v_isLinearInst_x3f_3990_; lean_object* v_noNatDivInst_x3f_3991_; lean_object* v_ringInst_x3f_3992_; lean_object* v_commRingInst_x3f_3993_; lean_object* v_orderedRingInst_x3f_3994_; lean_object* v_fieldInst_x3f_3995_; lean_object* v_charInst_x3f_3996_; lean_object* v_zero_3997_; lean_object* v_ofNatZero_3998_; lean_object* v_one_x3f_3999_; lean_object* v_leFn_x3f_4000_; lean_object* v_ltFn_x3f_4001_; lean_object* v_addFn_4002_; lean_object* v_zsmulFn_4003_; lean_object* v_nsmulFn_4004_; lean_object* v_zsmulFn_x3f_4005_; lean_object* v_nsmulFn_x3f_4006_; lean_object* v_homomulFn_x3f_4007_; lean_object* v_subFn_4008_; lean_object* v_negFn_4009_; lean_object* v_vars_4010_; lean_object* v_varMap_4011_; lean_object* v_lowers_4012_; lean_object* v_uppers_4013_; lean_object* v_diseqs_4014_; lean_object* v_assignment_4015_; uint8_t v_caseSplits_4016_; lean_object* v_conflict_x3f_4017_; lean_object* v_diseqSplits_4018_; lean_object* v_elimEqs_4019_; lean_object* v_elimStack_4020_; lean_object* v_occurs_4021_; lean_object* v_ignored_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4037_; 
v_v_3979_ = lean_array_fget(v_structs_3966_, v_a_3963_);
v_id_3980_ = lean_ctor_get(v_v_3979_, 0);
v_ringId_x3f_3981_ = lean_ctor_get(v_v_3979_, 1);
v_type_3982_ = lean_ctor_get(v_v_3979_, 2);
v_u_3983_ = lean_ctor_get(v_v_3979_, 3);
v_intModuleInst_3984_ = lean_ctor_get(v_v_3979_, 4);
v_leInst_x3f_3985_ = lean_ctor_get(v_v_3979_, 5);
v_ltInst_x3f_3986_ = lean_ctor_get(v_v_3979_, 6);
v_lawfulOrderLTInst_x3f_3987_ = lean_ctor_get(v_v_3979_, 7);
v_isPreorderInst_x3f_3988_ = lean_ctor_get(v_v_3979_, 8);
v_orderedAddInst_x3f_3989_ = lean_ctor_get(v_v_3979_, 9);
v_isLinearInst_x3f_3990_ = lean_ctor_get(v_v_3979_, 10);
v_noNatDivInst_x3f_3991_ = lean_ctor_get(v_v_3979_, 11);
v_ringInst_x3f_3992_ = lean_ctor_get(v_v_3979_, 12);
v_commRingInst_x3f_3993_ = lean_ctor_get(v_v_3979_, 13);
v_orderedRingInst_x3f_3994_ = lean_ctor_get(v_v_3979_, 14);
v_fieldInst_x3f_3995_ = lean_ctor_get(v_v_3979_, 15);
v_charInst_x3f_3996_ = lean_ctor_get(v_v_3979_, 16);
v_zero_3997_ = lean_ctor_get(v_v_3979_, 17);
v_ofNatZero_3998_ = lean_ctor_get(v_v_3979_, 18);
v_one_x3f_3999_ = lean_ctor_get(v_v_3979_, 19);
v_leFn_x3f_4000_ = lean_ctor_get(v_v_3979_, 20);
v_ltFn_x3f_4001_ = lean_ctor_get(v_v_3979_, 21);
v_addFn_4002_ = lean_ctor_get(v_v_3979_, 22);
v_zsmulFn_4003_ = lean_ctor_get(v_v_3979_, 23);
v_nsmulFn_4004_ = lean_ctor_get(v_v_3979_, 24);
v_zsmulFn_x3f_4005_ = lean_ctor_get(v_v_3979_, 25);
v_nsmulFn_x3f_4006_ = lean_ctor_get(v_v_3979_, 26);
v_homomulFn_x3f_4007_ = lean_ctor_get(v_v_3979_, 27);
v_subFn_4008_ = lean_ctor_get(v_v_3979_, 28);
v_negFn_4009_ = lean_ctor_get(v_v_3979_, 29);
v_vars_4010_ = lean_ctor_get(v_v_3979_, 30);
v_varMap_4011_ = lean_ctor_get(v_v_3979_, 31);
v_lowers_4012_ = lean_ctor_get(v_v_3979_, 32);
v_uppers_4013_ = lean_ctor_get(v_v_3979_, 33);
v_diseqs_4014_ = lean_ctor_get(v_v_3979_, 34);
v_assignment_4015_ = lean_ctor_get(v_v_3979_, 35);
v_caseSplits_4016_ = lean_ctor_get_uint8(v_v_3979_, sizeof(void*)*42);
v_conflict_x3f_4017_ = lean_ctor_get(v_v_3979_, 36);
v_diseqSplits_4018_ = lean_ctor_get(v_v_3979_, 37);
v_elimEqs_4019_ = lean_ctor_get(v_v_3979_, 38);
v_elimStack_4020_ = lean_ctor_get(v_v_3979_, 39);
v_occurs_4021_ = lean_ctor_get(v_v_3979_, 40);
v_ignored_4022_ = lean_ctor_get(v_v_3979_, 41);
v_isSharedCheck_4037_ = !lean_is_exclusive(v_v_3979_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4024_ = v_v_3979_;
v_isShared_4025_ = v_isSharedCheck_4037_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_ignored_4022_);
lean_inc(v_occurs_4021_);
lean_inc(v_elimStack_4020_);
lean_inc(v_elimEqs_4019_);
lean_inc(v_diseqSplits_4018_);
lean_inc(v_conflict_x3f_4017_);
lean_inc(v_assignment_4015_);
lean_inc(v_diseqs_4014_);
lean_inc(v_uppers_4013_);
lean_inc(v_lowers_4012_);
lean_inc(v_varMap_4011_);
lean_inc(v_vars_4010_);
lean_inc(v_negFn_4009_);
lean_inc(v_subFn_4008_);
lean_inc(v_homomulFn_x3f_4007_);
lean_inc(v_nsmulFn_x3f_4006_);
lean_inc(v_zsmulFn_x3f_4005_);
lean_inc(v_nsmulFn_4004_);
lean_inc(v_zsmulFn_4003_);
lean_inc(v_addFn_4002_);
lean_inc(v_ltFn_x3f_4001_);
lean_inc(v_leFn_x3f_4000_);
lean_inc(v_one_x3f_3999_);
lean_inc(v_ofNatZero_3998_);
lean_inc(v_zero_3997_);
lean_inc(v_charInst_x3f_3996_);
lean_inc(v_fieldInst_x3f_3995_);
lean_inc(v_orderedRingInst_x3f_3994_);
lean_inc(v_commRingInst_x3f_3993_);
lean_inc(v_ringInst_x3f_3992_);
lean_inc(v_noNatDivInst_x3f_3991_);
lean_inc(v_isLinearInst_x3f_3990_);
lean_inc(v_orderedAddInst_x3f_3989_);
lean_inc(v_isPreorderInst_x3f_3988_);
lean_inc(v_lawfulOrderLTInst_x3f_3987_);
lean_inc(v_ltInst_x3f_3986_);
lean_inc(v_leInst_x3f_3985_);
lean_inc(v_intModuleInst_3984_);
lean_inc(v_u_3983_);
lean_inc(v_type_3982_);
lean_inc(v_ringId_x3f_3981_);
lean_inc(v_id_3980_);
lean_dec(v_v_3979_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4037_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4026_; lean_object* v_xs_x27_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4031_; 
v___x_4026_ = lean_box(0);
v_xs_x27_4027_ = lean_array_fset(v_structs_3966_, v_a_3963_, v___x_4026_);
v___x_4028_ = lean_box(1);
v___x_4029_ = l_Lean_PersistentArray_set___redArg(v_occurs_4021_, v_x_3964_, v___x_4028_);
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 40, v___x_4029_);
v___x_4031_ = v___x_4024_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_id_3980_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v_ringId_x3f_3981_);
lean_ctor_set(v_reuseFailAlloc_4036_, 2, v_type_3982_);
lean_ctor_set(v_reuseFailAlloc_4036_, 3, v_u_3983_);
lean_ctor_set(v_reuseFailAlloc_4036_, 4, v_intModuleInst_3984_);
lean_ctor_set(v_reuseFailAlloc_4036_, 5, v_leInst_x3f_3985_);
lean_ctor_set(v_reuseFailAlloc_4036_, 6, v_ltInst_x3f_3986_);
lean_ctor_set(v_reuseFailAlloc_4036_, 7, v_lawfulOrderLTInst_x3f_3987_);
lean_ctor_set(v_reuseFailAlloc_4036_, 8, v_isPreorderInst_x3f_3988_);
lean_ctor_set(v_reuseFailAlloc_4036_, 9, v_orderedAddInst_x3f_3989_);
lean_ctor_set(v_reuseFailAlloc_4036_, 10, v_isLinearInst_x3f_3990_);
lean_ctor_set(v_reuseFailAlloc_4036_, 11, v_noNatDivInst_x3f_3991_);
lean_ctor_set(v_reuseFailAlloc_4036_, 12, v_ringInst_x3f_3992_);
lean_ctor_set(v_reuseFailAlloc_4036_, 13, v_commRingInst_x3f_3993_);
lean_ctor_set(v_reuseFailAlloc_4036_, 14, v_orderedRingInst_x3f_3994_);
lean_ctor_set(v_reuseFailAlloc_4036_, 15, v_fieldInst_x3f_3995_);
lean_ctor_set(v_reuseFailAlloc_4036_, 16, v_charInst_x3f_3996_);
lean_ctor_set(v_reuseFailAlloc_4036_, 17, v_zero_3997_);
lean_ctor_set(v_reuseFailAlloc_4036_, 18, v_ofNatZero_3998_);
lean_ctor_set(v_reuseFailAlloc_4036_, 19, v_one_x3f_3999_);
lean_ctor_set(v_reuseFailAlloc_4036_, 20, v_leFn_x3f_4000_);
lean_ctor_set(v_reuseFailAlloc_4036_, 21, v_ltFn_x3f_4001_);
lean_ctor_set(v_reuseFailAlloc_4036_, 22, v_addFn_4002_);
lean_ctor_set(v_reuseFailAlloc_4036_, 23, v_zsmulFn_4003_);
lean_ctor_set(v_reuseFailAlloc_4036_, 24, v_nsmulFn_4004_);
lean_ctor_set(v_reuseFailAlloc_4036_, 25, v_zsmulFn_x3f_4005_);
lean_ctor_set(v_reuseFailAlloc_4036_, 26, v_nsmulFn_x3f_4006_);
lean_ctor_set(v_reuseFailAlloc_4036_, 27, v_homomulFn_x3f_4007_);
lean_ctor_set(v_reuseFailAlloc_4036_, 28, v_subFn_4008_);
lean_ctor_set(v_reuseFailAlloc_4036_, 29, v_negFn_4009_);
lean_ctor_set(v_reuseFailAlloc_4036_, 30, v_vars_4010_);
lean_ctor_set(v_reuseFailAlloc_4036_, 31, v_varMap_4011_);
lean_ctor_set(v_reuseFailAlloc_4036_, 32, v_lowers_4012_);
lean_ctor_set(v_reuseFailAlloc_4036_, 33, v_uppers_4013_);
lean_ctor_set(v_reuseFailAlloc_4036_, 34, v_diseqs_4014_);
lean_ctor_set(v_reuseFailAlloc_4036_, 35, v_assignment_4015_);
lean_ctor_set(v_reuseFailAlloc_4036_, 36, v_conflict_x3f_4017_);
lean_ctor_set(v_reuseFailAlloc_4036_, 37, v_diseqSplits_4018_);
lean_ctor_set(v_reuseFailAlloc_4036_, 38, v_elimEqs_4019_);
lean_ctor_set(v_reuseFailAlloc_4036_, 39, v_elimStack_4020_);
lean_ctor_set(v_reuseFailAlloc_4036_, 40, v___x_4029_);
lean_ctor_set(v_reuseFailAlloc_4036_, 41, v_ignored_4022_);
lean_ctor_set_uint8(v_reuseFailAlloc_4036_, sizeof(void*)*42, v_caseSplits_4016_);
v___x_4031_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
lean_object* v___x_4032_; lean_object* v___x_4034_; 
v___x_4032_ = lean_array_fset(v_xs_x27_4027_, v_a_3963_, v___x_4031_);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 0, v___x_4032_);
v___x_4034_ = v___x_3977_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v___x_4032_);
lean_ctor_set(v_reuseFailAlloc_4035_, 1, v_typeIdOf_3967_);
lean_ctor_set(v_reuseFailAlloc_4035_, 2, v_exprToStructId_3968_);
lean_ctor_set(v_reuseFailAlloc_4035_, 3, v_exprToStructIdEntries_3969_);
lean_ctor_set(v_reuseFailAlloc_4035_, 4, v_forbiddenNatModules_3970_);
lean_ctor_set(v_reuseFailAlloc_4035_, 5, v_natStructs_3971_);
lean_ctor_set(v_reuseFailAlloc_4035_, 6, v_natTypeIdOf_3972_);
lean_ctor_set(v_reuseFailAlloc_4035_, 7, v_exprToNatStructId_3973_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed(lean_object* v_a_4047_, lean_object* v_x_4048_, lean_object* v_s_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(v_a_4047_, v_x_4048_, v_s_4049_);
lean_dec(v_x_4048_);
lean_dec(v_a_4047_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object* v_a_4051_, lean_object* v_x_4052_, lean_object* v_c_4053_, lean_object* v_init_4054_, lean_object* v_x_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
if (lean_obj_tag(v_x_4055_) == 0)
{
lean_object* v_k_4068_; lean_object* v_l_4069_; lean_object* v_r_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v_k_4068_ = lean_ctor_get(v_x_4055_, 1);
lean_inc(v_k_4068_);
v_l_4069_ = lean_ctor_get(v_x_4055_, 3);
lean_inc(v_l_4069_);
v_r_4070_ = lean_ctor_get(v_x_4055_, 4);
lean_inc(v_r_4070_);
lean_dec_ref_known(v_x_4055_, 5);
v___x_4071_ = lean_box(0);
lean_inc_ref(v_c_4053_);
lean_inc(v_x_4052_);
lean_inc(v_a_4051_);
v___x_4072_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4051_, v_x_4052_, v_c_4053_, v_init_4054_, v_l_4069_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v___x_4073_; 
lean_dec_ref_known(v___x_4072_, 1);
lean_inc_ref(v_c_4053_);
lean_inc(v_x_4052_);
lean_inc(v_a_4051_);
v___x_4073_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4051_, v_x_4052_, v_c_4053_, v_k_4068_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_dec_ref_known(v___x_4073_, 1);
v_init_4054_ = v___x_4071_;
v_x_4055_ = v_r_4070_;
goto _start;
}
else
{
lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4082_; 
lean_dec(v_r_4070_);
lean_dec_ref(v_c_4053_);
lean_dec(v_x_4052_);
lean_dec(v_a_4051_);
v_a_4075_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4077_ = v___x_4073_;
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_dec(v___x_4073_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4080_; 
if (v_isShared_4078_ == 0)
{
v___x_4080_ = v___x_4077_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4075_);
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
else
{
lean_dec(v_r_4070_);
lean_dec(v_k_4068_);
lean_dec_ref(v_c_4053_);
lean_dec(v_x_4052_);
lean_dec(v_a_4051_);
return v___x_4072_;
}
}
else
{
lean_object* v___x_4083_; lean_object* v___x_4084_; 
lean_dec_ref(v_c_4053_);
lean_dec(v_x_4052_);
lean_dec(v_a_4051_);
v___x_4083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4083_, 0, v_init_4054_);
v___x_4084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4083_);
return v___x_4084_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object** _args){
lean_object* v_a_4085_ = _args[0];
lean_object* v_x_4086_ = _args[1];
lean_object* v_c_4087_ = _args[2];
lean_object* v_init_4088_ = _args[3];
lean_object* v_x_4089_ = _args[4];
lean_object* v___y_4090_ = _args[5];
lean_object* v___y_4091_ = _args[6];
lean_object* v___y_4092_ = _args[7];
lean_object* v___y_4093_ = _args[8];
lean_object* v___y_4094_ = _args[9];
lean_object* v___y_4095_ = _args[10];
lean_object* v___y_4096_ = _args[11];
lean_object* v___y_4097_ = _args[12];
lean_object* v___y_4098_ = _args[13];
lean_object* v___y_4099_ = _args[14];
lean_object* v___y_4100_ = _args[15];
lean_object* v___y_4101_ = _args[16];
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4085_, v_x_4086_, v_c_4087_, v_init_4088_, v_x_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec(v___y_4092_);
lean_dec(v___y_4091_);
lean_dec(v___y_4090_);
return v_res_4102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object* v_a_4103_, lean_object* v_x_4104_, lean_object* v_c_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_){
_start:
{
lean_object* v___f_4118_; lean_object* v___x_4119_; 
lean_inc(v_x_4104_);
lean_inc(v_a_4106_);
v___f_4118_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4118_, 0, v_a_4106_);
lean_closure_set(v___f_4118_, 1, v_x_4104_);
v___x_4119_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; lean_object* v___y_4122_; lean_object* v_occurs_4144_; lean_object* v_size_4145_; lean_object* v___x_4146_; uint8_t v___x_4147_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref_known(v___x_4119_, 1);
v_occurs_4144_ = lean_ctor_get(v_a_4120_, 40);
lean_inc_ref(v_occurs_4144_);
lean_dec(v_a_4120_);
v_size_4145_ = lean_ctor_get(v_occurs_4144_, 2);
v___x_4146_ = lean_box(1);
v___x_4147_ = lean_nat_dec_lt(v_x_4104_, v_size_4145_);
if (v___x_4147_ == 0)
{
lean_object* v___x_4148_; 
lean_dec_ref(v_occurs_4144_);
v___x_4148_ = l_outOfBounds___redArg(v___x_4146_);
v___y_4122_ = v___x_4148_;
goto v___jp_4121_;
}
else
{
lean_object* v___x_4149_; 
v___x_4149_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4146_, v_occurs_4144_, v_x_4104_);
lean_dec_ref(v_occurs_4144_);
v___y_4122_ = v___x_4149_;
goto v___jp_4121_;
}
v___jp_4121_:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4123_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4124_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4123_, v___f_4118_, v_a_4107_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v___x_4125_; 
lean_dec_ref_known(v___x_4124_, 1);
lean_inc_ref(v_c_4105_);
lean_inc_n(v_x_4104_, 2);
lean_inc(v_a_4103_);
v___x_4125_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4103_, v_x_4104_, v_c_4105_, v_x_4104_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
lean_dec_ref_known(v___x_4125_, 1);
v___x_4126_ = lean_box(0);
v___x_4127_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4103_, v_x_4104_, v_c_4105_, v___x_4126_, v___y_4122_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4134_ == 0)
{
lean_object* v_unused_4135_; 
v_unused_4135_ = lean_ctor_get(v___x_4127_, 0);
lean_dec(v_unused_4135_);
v___x_4129_ = v___x_4127_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_dec(v___x_4127_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
lean_ctor_set(v___x_4129_, 0, v___x_4126_);
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4126_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
v_a_4136_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4127_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4127_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
else
{
lean_dec(v___y_4122_);
lean_dec_ref(v_c_4105_);
lean_dec(v_x_4104_);
lean_dec(v_a_4103_);
return v___x_4125_;
}
}
else
{
lean_dec(v___y_4122_);
lean_dec_ref(v_c_4105_);
lean_dec(v_x_4104_);
lean_dec(v_a_4103_);
return v___x_4124_;
}
}
}
else
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4157_; 
lean_dec_ref(v___f_4118_);
lean_dec_ref(v_c_4105_);
lean_dec(v_x_4104_);
lean_dec(v_a_4103_);
v_a_4150_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4152_ = v___x_4119_;
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4119_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___boxed(lean_object* v_a_4158_, lean_object* v_x_4159_, lean_object* v_c_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_){
_start:
{
lean_object* v_res_4173_; 
v_res_4173_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v_a_4158_, v_x_4159_, v_c_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_);
lean_dec(v_a_4171_);
lean_dec_ref(v_a_4170_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_a_4165_);
lean_dec_ref(v_a_4164_);
lean_dec(v_a_4163_);
lean_dec(v_a_4162_);
lean_dec(v_a_4161_);
return v_res_4173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(lean_object* v_c_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v_p_4191_; 
v_p_4191_ = lean_ctor_get(v_c_4174_, 0);
if (lean_obj_tag(v_p_4191_) == 1)
{
lean_object* v_k_4192_; lean_object* v_v_4193_; lean_object* v_p_4194_; lean_object* v_y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___x_4245_; lean_object* v___x_4246_; uint8_t v___x_4247_; 
v_k_4192_ = lean_ctor_get(v_p_4191_, 0);
v_v_4193_ = lean_ctor_get(v_p_4191_, 1);
v_p_4194_ = lean_ctor_get(v_p_4191_, 2);
v___x_4245_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_4246_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4247_ = lean_int_dec_eq(v_k_4192_, v___x_4246_);
if (v___x_4247_ == 0)
{
uint8_t v___x_4248_; 
v___x_4248_ = lean_int_dec_eq(v_k_4192_, v___x_4245_);
if (v___x_4248_ == 0)
{
goto v___jp_4187_;
}
else
{
if (lean_obj_tag(v_p_4194_) == 1)
{
lean_object* v_k_4249_; lean_object* v_v_4250_; lean_object* v_p_4251_; uint8_t v___x_4252_; 
v_k_4249_ = lean_ctor_get(v_p_4194_, 0);
v_v_4250_ = lean_ctor_get(v_p_4194_, 1);
v_p_4251_ = lean_ctor_get(v_p_4194_, 2);
v___x_4252_ = lean_int_dec_eq(v_k_4249_, v___x_4246_);
if (v___x_4252_ == 0)
{
goto v___jp_4187_;
}
else
{
if (lean_obj_tag(v_p_4251_) == 0)
{
v_y_4196_ = v_v_4250_;
v___y_4197_ = v_a_4175_;
v___y_4198_ = v_a_4176_;
v___y_4199_ = v_a_4177_;
v___y_4200_ = v_a_4178_;
v___y_4201_ = v_a_4179_;
v___y_4202_ = v_a_4180_;
v___y_4203_ = v_a_4181_;
v___y_4204_ = v_a_4182_;
v___y_4205_ = v_a_4183_;
v___y_4206_ = v_a_4184_;
v___y_4207_ = v_a_4185_;
goto v___jp_4195_;
}
else
{
goto v___jp_4187_;
}
}
}
else
{
goto v___jp_4187_;
}
}
}
else
{
if (lean_obj_tag(v_p_4194_) == 1)
{
lean_object* v_k_4253_; lean_object* v_v_4254_; lean_object* v_p_4255_; uint8_t v___x_4256_; 
v_k_4253_ = lean_ctor_get(v_p_4194_, 0);
v_v_4254_ = lean_ctor_get(v_p_4194_, 1);
v_p_4255_ = lean_ctor_get(v_p_4194_, 2);
v___x_4256_ = lean_int_dec_eq(v_k_4253_, v___x_4245_);
if (v___x_4256_ == 0)
{
goto v___jp_4187_;
}
else
{
if (lean_obj_tag(v_p_4255_) == 0)
{
v_y_4196_ = v_v_4254_;
v___y_4197_ = v_a_4175_;
v___y_4198_ = v_a_4176_;
v___y_4199_ = v_a_4177_;
v___y_4200_ = v_a_4178_;
v___y_4201_ = v_a_4179_;
v___y_4202_ = v_a_4180_;
v___y_4203_ = v_a_4181_;
v___y_4204_ = v_a_4182_;
v___y_4205_ = v_a_4183_;
v___y_4206_ = v_a_4184_;
v___y_4207_ = v_a_4185_;
goto v___jp_4195_;
}
else
{
goto v___jp_4187_;
}
}
}
else
{
goto v___jp_4187_;
}
}
v___jp_4195_:
{
lean_object* v___x_4208_; 
v___x_4208_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_v_4193_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; lean_object* v___x_4210_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_a_4209_);
lean_dec_ref_known(v___x_4208_, 1);
v___x_4210_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v_a_4211_; lean_object* v___x_4212_; 
v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
lean_inc(v_a_4211_);
lean_dec_ref_known(v___x_4210_, 1);
v___x_4212_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_4209_, v_a_4211_, v___y_4198_);
lean_dec(v_a_4211_);
lean_dec(v_a_4209_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4228_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4215_ = v___x_4212_;
v_isShared_4216_ = v_isSharedCheck_4228_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4212_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4228_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
uint8_t v___x_4217_; 
v___x_4217_ = lean_unbox(v_a_4213_);
lean_dec(v_a_4213_);
if (v___x_4217_ == 0)
{
uint8_t v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4221_; 
v___x_4218_ = 1;
v___x_4219_ = lean_box(v___x_4218_);
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 0, v___x_4219_);
v___x_4221_ = v___x_4215_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v___x_4219_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
else
{
uint8_t v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4226_; 
v___x_4223_ = 0;
v___x_4224_ = lean_box(v___x_4223_);
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 0, v___x_4224_);
v___x_4226_ = v___x_4215_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v___x_4224_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
}
else
{
return v___x_4212_;
}
}
else
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
lean_dec(v_a_4209_);
v_a_4229_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4210_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4210_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4229_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
else
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
v_a_4237_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___x_4208_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4208_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4237_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
}
else
{
goto v___jp_4187_;
}
v___jp_4187_:
{
uint8_t v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4188_ = 0;
v___x_4189_ = lean_box(v___x_4188_);
v___x_4190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
return v___x_4190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq___boxed(lean_object* v_c_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v_c_4257_, v_a_4258_, v_a_4259_, v_a_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_);
lean_dec(v_a_4268_);
lean_dec_ref(v_a_4267_);
lean_dec(v_a_4266_);
lean_dec_ref(v_a_4265_);
lean_dec(v_a_4264_);
lean_dec_ref(v_a_4263_);
lean_dec(v_a_4262_);
lean_dec_ref(v_a_4261_);
lean_dec(v_a_4260_);
lean_dec(v_a_4259_);
lean_dec(v_a_4258_);
lean_dec_ref(v_c_4257_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(lean_object* v_c_4271_){
_start:
{
lean_object* v_p_4273_; 
v_p_4273_ = lean_ctor_get(v_c_4271_, 0);
if (lean_obj_tag(v_p_4273_) == 1)
{
lean_object* v_k_4274_; lean_object* v___x_4275_; uint8_t v___x_4276_; 
v_k_4274_ = lean_ctor_get(v_p_4273_, 0);
v___x_4275_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_4276_ = lean_int_dec_lt(v_k_4274_, v___x_4275_);
if (v___x_4276_ == 0)
{
lean_object* v___x_4277_; 
v___x_4277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4277_, 0, v_c_4271_);
return v___x_4277_;
}
else
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4278_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_4273_);
v___x_4279_ = l_Lean_Grind_Linarith_Poly_mul(v_p_4273_, v___x_4278_);
v___x_4280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4280_, 0, v_c_4271_);
v___x_4281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4279_);
lean_ctor_set(v___x_4281_, 1, v___x_4280_);
v___x_4282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4282_, 0, v___x_4281_);
return v___x_4282_;
}
}
else
{
lean_object* v___x_4283_; 
v___x_4283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4283_, 0, v_c_4271_);
return v___x_4283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg___boxed(lean_object* v_c_4284_, lean_object* v_a_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4284_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(lean_object* v_c_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_){
_start:
{
lean_object* v___x_4300_; 
v___x_4300_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4287_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___boxed(lean_object* v_c_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_){
_start:
{
lean_object* v_res_4314_; 
v_res_4314_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(v_c_4301_, v_a_4302_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_);
lean_dec(v_a_4312_);
lean_dec_ref(v_a_4311_);
lean_dec(v_a_4310_);
lean_dec_ref(v_a_4309_);
lean_dec(v_a_4308_);
lean_dec_ref(v_a_4307_);
lean_dec(v_a_4306_);
lean_dec_ref(v_a_4305_);
lean_dec(v_a_4304_);
lean_dec(v_a_4303_);
lean_dec(v_a_4302_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(lean_object* v___y_4315_, lean_object* v_snd_4316_, lean_object* v_fst_4317_, lean_object* v_s_4318_){
_start:
{
lean_object* v_structs_4319_; lean_object* v_typeIdOf_4320_; lean_object* v_exprToStructId_4321_; lean_object* v_exprToStructIdEntries_4322_; lean_object* v_forbiddenNatModules_4323_; lean_object* v_natStructs_4324_; lean_object* v_natTypeIdOf_4325_; lean_object* v_exprToNatStructId_4326_; lean_object* v___x_4327_; uint8_t v___x_4328_; 
v_structs_4319_ = lean_ctor_get(v_s_4318_, 0);
v_typeIdOf_4320_ = lean_ctor_get(v_s_4318_, 1);
v_exprToStructId_4321_ = lean_ctor_get(v_s_4318_, 2);
v_exprToStructIdEntries_4322_ = lean_ctor_get(v_s_4318_, 3);
v_forbiddenNatModules_4323_ = lean_ctor_get(v_s_4318_, 4);
v_natStructs_4324_ = lean_ctor_get(v_s_4318_, 5);
v_natTypeIdOf_4325_ = lean_ctor_get(v_s_4318_, 6);
v_exprToNatStructId_4326_ = lean_ctor_get(v_s_4318_, 7);
v___x_4327_ = lean_array_get_size(v_structs_4319_);
v___x_4328_ = lean_nat_dec_lt(v___y_4315_, v___x_4327_);
if (v___x_4328_ == 0)
{
lean_dec(v_fst_4317_);
lean_dec_ref(v_snd_4316_);
return v_s_4318_;
}
else
{
lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4392_; 
lean_inc_ref(v_exprToNatStructId_4326_);
lean_inc_ref(v_natTypeIdOf_4325_);
lean_inc_ref(v_natStructs_4324_);
lean_inc_ref(v_forbiddenNatModules_4323_);
lean_inc_ref(v_exprToStructIdEntries_4322_);
lean_inc_ref(v_exprToStructId_4321_);
lean_inc_ref(v_typeIdOf_4320_);
lean_inc_ref(v_structs_4319_);
v_isSharedCheck_4392_ = !lean_is_exclusive(v_s_4318_);
if (v_isSharedCheck_4392_ == 0)
{
lean_object* v_unused_4393_; lean_object* v_unused_4394_; lean_object* v_unused_4395_; lean_object* v_unused_4396_; lean_object* v_unused_4397_; lean_object* v_unused_4398_; lean_object* v_unused_4399_; lean_object* v_unused_4400_; 
v_unused_4393_ = lean_ctor_get(v_s_4318_, 7);
lean_dec(v_unused_4393_);
v_unused_4394_ = lean_ctor_get(v_s_4318_, 6);
lean_dec(v_unused_4394_);
v_unused_4395_ = lean_ctor_get(v_s_4318_, 5);
lean_dec(v_unused_4395_);
v_unused_4396_ = lean_ctor_get(v_s_4318_, 4);
lean_dec(v_unused_4396_);
v_unused_4397_ = lean_ctor_get(v_s_4318_, 3);
lean_dec(v_unused_4397_);
v_unused_4398_ = lean_ctor_get(v_s_4318_, 2);
lean_dec(v_unused_4398_);
v_unused_4399_ = lean_ctor_get(v_s_4318_, 1);
lean_dec(v_unused_4399_);
v_unused_4400_ = lean_ctor_get(v_s_4318_, 0);
lean_dec(v_unused_4400_);
v___x_4330_ = v_s_4318_;
v_isShared_4331_ = v_isSharedCheck_4392_;
goto v_resetjp_4329_;
}
else
{
lean_dec(v_s_4318_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4392_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v_v_4332_; lean_object* v_id_4333_; lean_object* v_ringId_x3f_4334_; lean_object* v_type_4335_; lean_object* v_u_4336_; lean_object* v_intModuleInst_4337_; lean_object* v_leInst_x3f_4338_; lean_object* v_ltInst_x3f_4339_; lean_object* v_lawfulOrderLTInst_x3f_4340_; lean_object* v_isPreorderInst_x3f_4341_; lean_object* v_orderedAddInst_x3f_4342_; lean_object* v_isLinearInst_x3f_4343_; lean_object* v_noNatDivInst_x3f_4344_; lean_object* v_ringInst_x3f_4345_; lean_object* v_commRingInst_x3f_4346_; lean_object* v_orderedRingInst_x3f_4347_; lean_object* v_fieldInst_x3f_4348_; lean_object* v_charInst_x3f_4349_; lean_object* v_zero_4350_; lean_object* v_ofNatZero_4351_; lean_object* v_one_x3f_4352_; lean_object* v_leFn_x3f_4353_; lean_object* v_ltFn_x3f_4354_; lean_object* v_addFn_4355_; lean_object* v_zsmulFn_4356_; lean_object* v_nsmulFn_4357_; lean_object* v_zsmulFn_x3f_4358_; lean_object* v_nsmulFn_x3f_4359_; lean_object* v_homomulFn_x3f_4360_; lean_object* v_subFn_4361_; lean_object* v_negFn_4362_; lean_object* v_vars_4363_; lean_object* v_varMap_4364_; lean_object* v_lowers_4365_; lean_object* v_uppers_4366_; lean_object* v_diseqs_4367_; lean_object* v_assignment_4368_; uint8_t v_caseSplits_4369_; lean_object* v_conflict_x3f_4370_; lean_object* v_diseqSplits_4371_; lean_object* v_elimEqs_4372_; lean_object* v_elimStack_4373_; lean_object* v_occurs_4374_; lean_object* v_ignored_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4391_; 
v_v_4332_ = lean_array_fget(v_structs_4319_, v___y_4315_);
v_id_4333_ = lean_ctor_get(v_v_4332_, 0);
v_ringId_x3f_4334_ = lean_ctor_get(v_v_4332_, 1);
v_type_4335_ = lean_ctor_get(v_v_4332_, 2);
v_u_4336_ = lean_ctor_get(v_v_4332_, 3);
v_intModuleInst_4337_ = lean_ctor_get(v_v_4332_, 4);
v_leInst_x3f_4338_ = lean_ctor_get(v_v_4332_, 5);
v_ltInst_x3f_4339_ = lean_ctor_get(v_v_4332_, 6);
v_lawfulOrderLTInst_x3f_4340_ = lean_ctor_get(v_v_4332_, 7);
v_isPreorderInst_x3f_4341_ = lean_ctor_get(v_v_4332_, 8);
v_orderedAddInst_x3f_4342_ = lean_ctor_get(v_v_4332_, 9);
v_isLinearInst_x3f_4343_ = lean_ctor_get(v_v_4332_, 10);
v_noNatDivInst_x3f_4344_ = lean_ctor_get(v_v_4332_, 11);
v_ringInst_x3f_4345_ = lean_ctor_get(v_v_4332_, 12);
v_commRingInst_x3f_4346_ = lean_ctor_get(v_v_4332_, 13);
v_orderedRingInst_x3f_4347_ = lean_ctor_get(v_v_4332_, 14);
v_fieldInst_x3f_4348_ = lean_ctor_get(v_v_4332_, 15);
v_charInst_x3f_4349_ = lean_ctor_get(v_v_4332_, 16);
v_zero_4350_ = lean_ctor_get(v_v_4332_, 17);
v_ofNatZero_4351_ = lean_ctor_get(v_v_4332_, 18);
v_one_x3f_4352_ = lean_ctor_get(v_v_4332_, 19);
v_leFn_x3f_4353_ = lean_ctor_get(v_v_4332_, 20);
v_ltFn_x3f_4354_ = lean_ctor_get(v_v_4332_, 21);
v_addFn_4355_ = lean_ctor_get(v_v_4332_, 22);
v_zsmulFn_4356_ = lean_ctor_get(v_v_4332_, 23);
v_nsmulFn_4357_ = lean_ctor_get(v_v_4332_, 24);
v_zsmulFn_x3f_4358_ = lean_ctor_get(v_v_4332_, 25);
v_nsmulFn_x3f_4359_ = lean_ctor_get(v_v_4332_, 26);
v_homomulFn_x3f_4360_ = lean_ctor_get(v_v_4332_, 27);
v_subFn_4361_ = lean_ctor_get(v_v_4332_, 28);
v_negFn_4362_ = lean_ctor_get(v_v_4332_, 29);
v_vars_4363_ = lean_ctor_get(v_v_4332_, 30);
v_varMap_4364_ = lean_ctor_get(v_v_4332_, 31);
v_lowers_4365_ = lean_ctor_get(v_v_4332_, 32);
v_uppers_4366_ = lean_ctor_get(v_v_4332_, 33);
v_diseqs_4367_ = lean_ctor_get(v_v_4332_, 34);
v_assignment_4368_ = lean_ctor_get(v_v_4332_, 35);
v_caseSplits_4369_ = lean_ctor_get_uint8(v_v_4332_, sizeof(void*)*42);
v_conflict_x3f_4370_ = lean_ctor_get(v_v_4332_, 36);
v_diseqSplits_4371_ = lean_ctor_get(v_v_4332_, 37);
v_elimEqs_4372_ = lean_ctor_get(v_v_4332_, 38);
v_elimStack_4373_ = lean_ctor_get(v_v_4332_, 39);
v_occurs_4374_ = lean_ctor_get(v_v_4332_, 40);
v_ignored_4375_ = lean_ctor_get(v_v_4332_, 41);
v_isSharedCheck_4391_ = !lean_is_exclusive(v_v_4332_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4377_ = v_v_4332_;
v_isShared_4378_ = v_isSharedCheck_4391_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_ignored_4375_);
lean_inc(v_occurs_4374_);
lean_inc(v_elimStack_4373_);
lean_inc(v_elimEqs_4372_);
lean_inc(v_diseqSplits_4371_);
lean_inc(v_conflict_x3f_4370_);
lean_inc(v_assignment_4368_);
lean_inc(v_diseqs_4367_);
lean_inc(v_uppers_4366_);
lean_inc(v_lowers_4365_);
lean_inc(v_varMap_4364_);
lean_inc(v_vars_4363_);
lean_inc(v_negFn_4362_);
lean_inc(v_subFn_4361_);
lean_inc(v_homomulFn_x3f_4360_);
lean_inc(v_nsmulFn_x3f_4359_);
lean_inc(v_zsmulFn_x3f_4358_);
lean_inc(v_nsmulFn_4357_);
lean_inc(v_zsmulFn_4356_);
lean_inc(v_addFn_4355_);
lean_inc(v_ltFn_x3f_4354_);
lean_inc(v_leFn_x3f_4353_);
lean_inc(v_one_x3f_4352_);
lean_inc(v_ofNatZero_4351_);
lean_inc(v_zero_4350_);
lean_inc(v_charInst_x3f_4349_);
lean_inc(v_fieldInst_x3f_4348_);
lean_inc(v_orderedRingInst_x3f_4347_);
lean_inc(v_commRingInst_x3f_4346_);
lean_inc(v_ringInst_x3f_4345_);
lean_inc(v_noNatDivInst_x3f_4344_);
lean_inc(v_isLinearInst_x3f_4343_);
lean_inc(v_orderedAddInst_x3f_4342_);
lean_inc(v_isPreorderInst_x3f_4341_);
lean_inc(v_lawfulOrderLTInst_x3f_4340_);
lean_inc(v_ltInst_x3f_4339_);
lean_inc(v_leInst_x3f_4338_);
lean_inc(v_intModuleInst_4337_);
lean_inc(v_u_4336_);
lean_inc(v_type_4335_);
lean_inc(v_ringId_x3f_4334_);
lean_inc(v_id_4333_);
lean_dec(v_v_4332_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4391_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4379_; lean_object* v_xs_x27_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4385_; 
v___x_4379_ = lean_box(0);
v_xs_x27_4380_ = lean_array_fset(v_structs_4319_, v___y_4315_, v___x_4379_);
v___x_4381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4381_, 0, v_snd_4316_);
v___x_4382_ = l_Lean_PersistentArray_set___redArg(v_elimEqs_4372_, v_fst_4317_, v___x_4381_);
v___x_4383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4383_, 0, v_fst_4317_);
lean_ctor_set(v___x_4383_, 1, v_elimStack_4373_);
if (v_isShared_4378_ == 0)
{
lean_ctor_set(v___x_4377_, 39, v___x_4383_);
lean_ctor_set(v___x_4377_, 38, v___x_4382_);
v___x_4385_ = v___x_4377_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_id_4333_);
lean_ctor_set(v_reuseFailAlloc_4390_, 1, v_ringId_x3f_4334_);
lean_ctor_set(v_reuseFailAlloc_4390_, 2, v_type_4335_);
lean_ctor_set(v_reuseFailAlloc_4390_, 3, v_u_4336_);
lean_ctor_set(v_reuseFailAlloc_4390_, 4, v_intModuleInst_4337_);
lean_ctor_set(v_reuseFailAlloc_4390_, 5, v_leInst_x3f_4338_);
lean_ctor_set(v_reuseFailAlloc_4390_, 6, v_ltInst_x3f_4339_);
lean_ctor_set(v_reuseFailAlloc_4390_, 7, v_lawfulOrderLTInst_x3f_4340_);
lean_ctor_set(v_reuseFailAlloc_4390_, 8, v_isPreorderInst_x3f_4341_);
lean_ctor_set(v_reuseFailAlloc_4390_, 9, v_orderedAddInst_x3f_4342_);
lean_ctor_set(v_reuseFailAlloc_4390_, 10, v_isLinearInst_x3f_4343_);
lean_ctor_set(v_reuseFailAlloc_4390_, 11, v_noNatDivInst_x3f_4344_);
lean_ctor_set(v_reuseFailAlloc_4390_, 12, v_ringInst_x3f_4345_);
lean_ctor_set(v_reuseFailAlloc_4390_, 13, v_commRingInst_x3f_4346_);
lean_ctor_set(v_reuseFailAlloc_4390_, 14, v_orderedRingInst_x3f_4347_);
lean_ctor_set(v_reuseFailAlloc_4390_, 15, v_fieldInst_x3f_4348_);
lean_ctor_set(v_reuseFailAlloc_4390_, 16, v_charInst_x3f_4349_);
lean_ctor_set(v_reuseFailAlloc_4390_, 17, v_zero_4350_);
lean_ctor_set(v_reuseFailAlloc_4390_, 18, v_ofNatZero_4351_);
lean_ctor_set(v_reuseFailAlloc_4390_, 19, v_one_x3f_4352_);
lean_ctor_set(v_reuseFailAlloc_4390_, 20, v_leFn_x3f_4353_);
lean_ctor_set(v_reuseFailAlloc_4390_, 21, v_ltFn_x3f_4354_);
lean_ctor_set(v_reuseFailAlloc_4390_, 22, v_addFn_4355_);
lean_ctor_set(v_reuseFailAlloc_4390_, 23, v_zsmulFn_4356_);
lean_ctor_set(v_reuseFailAlloc_4390_, 24, v_nsmulFn_4357_);
lean_ctor_set(v_reuseFailAlloc_4390_, 25, v_zsmulFn_x3f_4358_);
lean_ctor_set(v_reuseFailAlloc_4390_, 26, v_nsmulFn_x3f_4359_);
lean_ctor_set(v_reuseFailAlloc_4390_, 27, v_homomulFn_x3f_4360_);
lean_ctor_set(v_reuseFailAlloc_4390_, 28, v_subFn_4361_);
lean_ctor_set(v_reuseFailAlloc_4390_, 29, v_negFn_4362_);
lean_ctor_set(v_reuseFailAlloc_4390_, 30, v_vars_4363_);
lean_ctor_set(v_reuseFailAlloc_4390_, 31, v_varMap_4364_);
lean_ctor_set(v_reuseFailAlloc_4390_, 32, v_lowers_4365_);
lean_ctor_set(v_reuseFailAlloc_4390_, 33, v_uppers_4366_);
lean_ctor_set(v_reuseFailAlloc_4390_, 34, v_diseqs_4367_);
lean_ctor_set(v_reuseFailAlloc_4390_, 35, v_assignment_4368_);
lean_ctor_set(v_reuseFailAlloc_4390_, 36, v_conflict_x3f_4370_);
lean_ctor_set(v_reuseFailAlloc_4390_, 37, v_diseqSplits_4371_);
lean_ctor_set(v_reuseFailAlloc_4390_, 38, v___x_4382_);
lean_ctor_set(v_reuseFailAlloc_4390_, 39, v___x_4383_);
lean_ctor_set(v_reuseFailAlloc_4390_, 40, v_occurs_4374_);
lean_ctor_set(v_reuseFailAlloc_4390_, 41, v_ignored_4375_);
lean_ctor_set_uint8(v_reuseFailAlloc_4390_, sizeof(void*)*42, v_caseSplits_4369_);
v___x_4385_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
lean_object* v___x_4386_; lean_object* v___x_4388_; 
v___x_4386_ = lean_array_fset(v_xs_x27_4380_, v___y_4315_, v___x_4385_);
if (v_isShared_4331_ == 0)
{
lean_ctor_set(v___x_4330_, 0, v___x_4386_);
v___x_4388_ = v___x_4330_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v___x_4386_);
lean_ctor_set(v_reuseFailAlloc_4389_, 1, v_typeIdOf_4320_);
lean_ctor_set(v_reuseFailAlloc_4389_, 2, v_exprToStructId_4321_);
lean_ctor_set(v_reuseFailAlloc_4389_, 3, v_exprToStructIdEntries_4322_);
lean_ctor_set(v_reuseFailAlloc_4389_, 4, v_forbiddenNatModules_4323_);
lean_ctor_set(v_reuseFailAlloc_4389_, 5, v_natStructs_4324_);
lean_ctor_set(v_reuseFailAlloc_4389_, 6, v_natTypeIdOf_4325_);
lean_ctor_set(v_reuseFailAlloc_4389_, 7, v_exprToNatStructId_4326_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed(lean_object* v___y_4401_, lean_object* v_snd_4402_, lean_object* v_fst_4403_, lean_object* v_s_4404_){
_start:
{
lean_object* v_res_4405_; 
v_res_4405_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(v___y_4401_, v_snd_4402_, v_fst_4403_, v_s_4404_);
lean_dec(v___y_4401_);
return v_res_4405_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1(void){
_start:
{
lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4407_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0));
v___x_4408_ = l_Lean_stringToMessageData(v___x_4407_);
return v___x_4408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4(void){
_start:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4416_ = l_Lean_Name_append(v___x_4415_, v___x_4414_);
return v___x_4416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object* v_c_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_){
_start:
{
lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; lean_object* v___y_4449_; lean_object* v___y_4455_; lean_object* v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v_toCold_4496_; lean_object* v_options_4497_; lean_object* v_inheritedTraceOptions_4498_; uint8_t v_hasTrace_4499_; lean_object* v___y_4501_; lean_object* v___y_4502_; lean_object* v___y_4503_; lean_object* v___y_4504_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4514_; lean_object* v___y_4515_; lean_object* v_options_4516_; lean_object* v_inheritedTraceOptions_4517_; lean_object* v___y_4518_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v___y_4545_; 
v_toCold_4496_ = lean_ctor_get(v_a_4427_, 0);
v_options_4497_ = lean_ctor_get(v_toCold_4496_, 2);
v_inheritedTraceOptions_4498_ = lean_ctor_get(v_toCold_4496_, 11);
v_hasTrace_4499_ = lean_ctor_get_uint8(v_options_4497_, sizeof(void*)*1);
if (v_hasTrace_4499_ == 0)
{
v___y_4535_ = v_a_4418_;
v___y_4536_ = v_a_4419_;
v___y_4537_ = v_a_4420_;
v___y_4538_ = v_a_4421_;
v___y_4539_ = v_a_4422_;
v___y_4540_ = v_a_4423_;
v___y_4541_ = v_a_4424_;
v___y_4542_ = v_a_4425_;
v___y_4543_ = v_a_4426_;
v___y_4544_ = v_a_4427_;
v___y_4545_ = v_a_4428_;
goto v___jp_4534_;
}
else
{
lean_object* v_cls_4643_; lean_object* v___x_4644_; uint8_t v___x_4645_; 
v_cls_4643_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_4644_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_4645_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4498_, v_options_4497_, v___x_4644_);
if (v___x_4645_ == 0)
{
v___y_4535_ = v_a_4418_;
v___y_4536_ = v_a_4419_;
v___y_4537_ = v_a_4420_;
v___y_4538_ = v_a_4421_;
v___y_4539_ = v_a_4422_;
v___y_4540_ = v_a_4423_;
v___y_4541_ = v_a_4424_;
v___y_4542_ = v_a_4425_;
v___y_4543_ = v_a_4426_;
v___y_4544_ = v_a_4427_;
v___y_4545_ = v_a_4428_;
goto v___jp_4534_;
}
else
{
lean_object* v___x_4646_; 
v___x_4646_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_4417_, v_a_4418_, v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v_a_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v_a_4647_ = lean_ctor_get(v___x_4646_, 0);
lean_inc(v_a_4647_);
lean_dec_ref_known(v___x_4646_, 1);
v___x_4648_ = l_Lean_MessageData_ofExpr(v_a_4647_);
v___x_4649_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4643_, v___x_4648_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_);
if (lean_obj_tag(v___x_4649_) == 0)
{
lean_dec_ref_known(v___x_4649_, 1);
v___y_4535_ = v_a_4418_;
v___y_4536_ = v_a_4419_;
v___y_4537_ = v_a_4420_;
v___y_4538_ = v_a_4421_;
v___y_4539_ = v_a_4422_;
v___y_4540_ = v_a_4423_;
v___y_4541_ = v_a_4424_;
v___y_4542_ = v_a_4425_;
v___y_4543_ = v_a_4426_;
v___y_4544_ = v_a_4427_;
v___y_4545_ = v_a_4428_;
goto v___jp_4534_;
}
else
{
lean_dec_ref(v_c_4417_);
return v___x_4649_;
}
}
else
{
lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4657_; 
lean_dec_ref(v_c_4417_);
v_a_4650_ = lean_ctor_get(v___x_4646_, 0);
v_isSharedCheck_4657_ = !lean_is_exclusive(v___x_4646_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4652_ = v___x_4646_;
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_a_4650_);
lean_dec(v___x_4646_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4655_; 
if (v_isShared_4653_ == 0)
{
v___x_4655_ = v___x_4652_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4650_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
return v___x_4655_;
}
}
}
}
}
v___jp_4430_:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4431_ = lean_box(0);
v___x_4432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4431_);
return v___x_4432_;
}
v___jp_4433_:
{
lean_object* v___f_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
lean_inc(v___y_4439_);
v___f_4450_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4450_, 0, v___y_4439_);
lean_closure_set(v___f_4450_, 1, v___y_4435_);
lean_closure_set(v___f_4450_, 2, v___y_4434_);
v___x_4451_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4452_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4451_, v___f_4450_, v___y_4440_);
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_object* v___x_4453_; 
lean_dec_ref_known(v___x_4452_, 1);
v___x_4453_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v___y_4436_, v___y_4438_, v___y_4437_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
return v___x_4453_;
}
else
{
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec(v___y_4436_);
return v___x_4452_;
}
}
v___jp_4454_:
{
lean_object* v___x_4471_; 
v___x_4471_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_object* v_a_4472_; uint8_t v_caseSplits_4473_; 
v_a_4472_ = lean_ctor_get(v___x_4471_, 0);
lean_inc(v_a_4472_);
lean_dec_ref_known(v___x_4471_, 1);
v_caseSplits_4473_ = lean_ctor_get_uint8(v_a_4472_, sizeof(void*)*42);
lean_dec(v_a_4472_);
if (v_caseSplits_4473_ == 0)
{
lean_object* v___x_4474_; 
v___x_4474_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_object* v_a_4475_; uint8_t v___x_4476_; 
v_a_4475_ = lean_ctor_get(v___x_4474_, 0);
lean_inc(v_a_4475_);
lean_dec_ref_known(v___x_4474_, 1);
v___x_4476_ = lean_unbox(v_a_4475_);
lean_dec(v_a_4475_);
if (v___x_4476_ == 0)
{
v___y_4434_ = v___y_4456_;
v___y_4435_ = v___y_4455_;
v___y_4436_ = v___y_4457_;
v___y_4437_ = v___y_4459_;
v___y_4438_ = v___y_4458_;
v___y_4439_ = v___y_4460_;
v___y_4440_ = v___y_4461_;
v___y_4441_ = v___y_4462_;
v___y_4442_ = v___y_4463_;
v___y_4443_ = v___y_4464_;
v___y_4444_ = v___y_4465_;
v___y_4445_ = v___y_4466_;
v___y_4446_ = v___y_4467_;
v___y_4447_ = v___y_4468_;
v___y_4448_ = v___y_4469_;
v___y_4449_ = v___y_4470_;
goto v___jp_4433_;
}
else
{
lean_object* v___x_4477_; lean_object* v_a_4478_; lean_object* v___x_4479_; 
lean_inc_ref(v___y_4459_);
v___x_4477_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v___y_4459_);
v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
lean_inc(v_a_4478_);
lean_dec_ref(v___x_4477_);
v___x_4479_ = l_Lean_Meta_Grind_Arith_Linear_propagateImpEq(v_a_4478_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_dec_ref_known(v___x_4479_, 1);
v___y_4434_ = v___y_4456_;
v___y_4435_ = v___y_4455_;
v___y_4436_ = v___y_4457_;
v___y_4437_ = v___y_4459_;
v___y_4438_ = v___y_4458_;
v___y_4439_ = v___y_4460_;
v___y_4440_ = v___y_4461_;
v___y_4441_ = v___y_4462_;
v___y_4442_ = v___y_4463_;
v___y_4443_ = v___y_4464_;
v___y_4444_ = v___y_4465_;
v___y_4445_ = v___y_4466_;
v___y_4446_ = v___y_4467_;
v___y_4447_ = v___y_4468_;
v___y_4448_ = v___y_4469_;
v___y_4449_ = v___y_4470_;
goto v___jp_4433_;
}
else
{
lean_dec_ref(v___y_4459_);
lean_dec(v___y_4458_);
lean_dec(v___y_4457_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
return v___x_4479_;
}
}
}
else
{
lean_object* v_a_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4487_; 
lean_dec_ref(v___y_4459_);
lean_dec(v___y_4458_);
lean_dec(v___y_4457_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
v_a_4480_ = lean_ctor_get(v___x_4474_, 0);
v_isSharedCheck_4487_ = !lean_is_exclusive(v___x_4474_);
if (v_isSharedCheck_4487_ == 0)
{
v___x_4482_ = v___x_4474_;
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_a_4480_);
lean_dec(v___x_4474_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4485_; 
if (v_isShared_4483_ == 0)
{
v___x_4485_ = v___x_4482_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_a_4480_);
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
else
{
v___y_4434_ = v___y_4456_;
v___y_4435_ = v___y_4455_;
v___y_4436_ = v___y_4457_;
v___y_4437_ = v___y_4459_;
v___y_4438_ = v___y_4458_;
v___y_4439_ = v___y_4460_;
v___y_4440_ = v___y_4461_;
v___y_4441_ = v___y_4462_;
v___y_4442_ = v___y_4463_;
v___y_4443_ = v___y_4464_;
v___y_4444_ = v___y_4465_;
v___y_4445_ = v___y_4466_;
v___y_4446_ = v___y_4467_;
v___y_4447_ = v___y_4468_;
v___y_4448_ = v___y_4469_;
v___y_4449_ = v___y_4470_;
goto v___jp_4433_;
}
}
else
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4495_; 
lean_dec_ref(v___y_4459_);
lean_dec(v___y_4458_);
lean_dec(v___y_4457_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
v_a_4488_ = lean_ctor_get(v___x_4471_, 0);
v_isSharedCheck_4495_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4490_ = v___x_4471_;
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4471_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4493_; 
if (v_isShared_4491_ == 0)
{
v___x_4493_ = v___x_4490_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_a_4488_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
return v___x_4493_;
}
}
}
}
v___jp_4500_:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; uint8_t v___x_4521_; 
v___x_4519_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_4520_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_4521_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4517_, v_options_4516_, v___x_4520_);
if (v___x_4521_ == 0)
{
v___y_4455_ = v___y_4502_;
v___y_4456_ = v___y_4501_;
v___y_4457_ = v___y_4503_;
v___y_4458_ = v___y_4505_;
v___y_4459_ = v___y_4504_;
v___y_4460_ = v___y_4506_;
v___y_4461_ = v___y_4507_;
v___y_4462_ = v___y_4508_;
v___y_4463_ = v___y_4509_;
v___y_4464_ = v___y_4510_;
v___y_4465_ = v___y_4511_;
v___y_4466_ = v___y_4512_;
v___y_4467_ = v___y_4513_;
v___y_4468_ = v___y_4514_;
v___y_4469_ = v___y_4515_;
v___y_4470_ = v___y_4518_;
goto v___jp_4454_;
}
else
{
lean_object* v___x_4522_; 
v___x_4522_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v___y_4504_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4518_);
if (lean_obj_tag(v___x_4522_) == 0)
{
lean_object* v_a_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; 
v_a_4523_ = lean_ctor_get(v___x_4522_, 0);
lean_inc(v_a_4523_);
lean_dec_ref_known(v___x_4522_, 1);
v___x_4524_ = l_Lean_MessageData_ofExpr(v_a_4523_);
v___x_4525_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4519_, v___x_4524_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4518_);
if (lean_obj_tag(v___x_4525_) == 0)
{
lean_dec_ref_known(v___x_4525_, 1);
v___y_4455_ = v___y_4502_;
v___y_4456_ = v___y_4501_;
v___y_4457_ = v___y_4503_;
v___y_4458_ = v___y_4505_;
v___y_4459_ = v___y_4504_;
v___y_4460_ = v___y_4506_;
v___y_4461_ = v___y_4507_;
v___y_4462_ = v___y_4508_;
v___y_4463_ = v___y_4509_;
v___y_4464_ = v___y_4510_;
v___y_4465_ = v___y_4511_;
v___y_4466_ = v___y_4512_;
v___y_4467_ = v___y_4513_;
v___y_4468_ = v___y_4514_;
v___y_4469_ = v___y_4515_;
v___y_4470_ = v___y_4518_;
goto v___jp_4454_;
}
else
{
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
return v___x_4525_;
}
}
else
{
lean_object* v_a_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4533_; 
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
v_a_4526_ = lean_ctor_get(v___x_4522_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4528_ = v___x_4522_;
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_a_4526_);
lean_dec(v___x_4522_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4531_; 
if (v_isShared_4529_ == 0)
{
v___x_4531_ = v___x_4528_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_a_4526_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
}
v___jp_4534_:
{
lean_object* v___x_4546_; 
lean_inc_ref(v___y_4544_);
v___x_4546_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_4417_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
if (lean_obj_tag(v___x_4546_) == 0)
{
lean_object* v_a_4547_; lean_object* v_p_4548_; lean_object* v___x_4549_; uint8_t v___x_4550_; 
v_a_4547_ = lean_ctor_get(v___x_4546_, 0);
lean_inc(v_a_4547_);
lean_dec_ref_known(v___x_4546_, 1);
v_p_4548_ = lean_ctor_get(v_a_4547_, 0);
v___x_4549_ = lean_box(0);
v___x_4550_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_4548_, v___x_4549_);
if (v___x_4550_ == 0)
{
lean_object* v___x_4551_; 
v___x_4551_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_a_4547_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
if (lean_obj_tag(v___x_4551_) == 0)
{
lean_object* v_a_4552_; lean_object* v_snd_4553_; lean_object* v_toCold_4554_; lean_object* v_options_4555_; uint8_t v_hasTrace_4556_; 
v_a_4552_ = lean_ctor_get(v___x_4551_, 0);
lean_inc(v_a_4552_);
lean_dec_ref_known(v___x_4551_, 1);
v_snd_4553_ = lean_ctor_get(v_a_4552_, 1);
lean_inc(v_snd_4553_);
v_toCold_4554_ = lean_ctor_get(v___y_4544_, 0);
v_options_4555_ = lean_ctor_get(v_toCold_4554_, 2);
v_hasTrace_4556_ = lean_ctor_get_uint8(v_options_4555_, sizeof(void*)*1);
if (v_hasTrace_4556_ == 0)
{
lean_object* v_fst_4557_; lean_object* v_fst_4558_; lean_object* v_snd_4559_; 
v_fst_4557_ = lean_ctor_get(v_a_4552_, 0);
lean_inc(v_fst_4557_);
lean_dec(v_a_4552_);
v_fst_4558_ = lean_ctor_get(v_snd_4553_, 0);
lean_inc_n(v_fst_4558_, 2);
v_snd_4559_ = lean_ctor_get(v_snd_4553_, 1);
lean_inc_n(v_snd_4559_, 2);
lean_dec(v_snd_4553_);
v___y_4455_ = v_snd_4559_;
v___y_4456_ = v_fst_4558_;
v___y_4457_ = v_fst_4557_;
v___y_4458_ = v_fst_4558_;
v___y_4459_ = v_snd_4559_;
v___y_4460_ = v___y_4535_;
v___y_4461_ = v___y_4536_;
v___y_4462_ = v___y_4537_;
v___y_4463_ = v___y_4538_;
v___y_4464_ = v___y_4539_;
v___y_4465_ = v___y_4540_;
v___y_4466_ = v___y_4541_;
v___y_4467_ = v___y_4542_;
v___y_4468_ = v___y_4543_;
v___y_4469_ = v___y_4544_;
v___y_4470_ = v___y_4545_;
goto v___jp_4454_;
}
else
{
lean_object* v_fst_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4606_; 
v_fst_4560_ = lean_ctor_get(v_a_4552_, 0);
v_isSharedCheck_4606_ = !lean_is_exclusive(v_a_4552_);
if (v_isSharedCheck_4606_ == 0)
{
lean_object* v_unused_4607_; 
v_unused_4607_ = lean_ctor_get(v_a_4552_, 1);
lean_dec(v_unused_4607_);
v___x_4562_ = v_a_4552_;
v_isShared_4563_ = v_isSharedCheck_4606_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_fst_4560_);
lean_dec(v_a_4552_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4606_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v_fst_4564_; lean_object* v_snd_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4605_; 
v_fst_4564_ = lean_ctor_get(v_snd_4553_, 0);
v_snd_4565_ = lean_ctor_get(v_snd_4553_, 1);
v_isSharedCheck_4605_ = !lean_is_exclusive(v_snd_4553_);
if (v_isSharedCheck_4605_ == 0)
{
v___x_4567_ = v_snd_4553_;
v_isShared_4568_ = v_isSharedCheck_4605_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_snd_4565_);
lean_inc(v_fst_4564_);
lean_dec(v_snd_4553_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4605_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v_inheritedTraceOptions_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; uint8_t v___x_4572_; 
v_inheritedTraceOptions_4569_ = lean_ctor_get(v_toCold_4554_, 11);
v___x_4570_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_4571_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_4572_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4569_, v_options_4555_, v___x_4571_);
if (v___x_4572_ == 0)
{
lean_del_object(v___x_4567_);
lean_del_object(v___x_4562_);
lean_inc(v_snd_4565_);
lean_inc(v_fst_4564_);
v___y_4501_ = v_fst_4564_;
v___y_4502_ = v_snd_4565_;
v___y_4503_ = v_fst_4560_;
v___y_4504_ = v_snd_4565_;
v___y_4505_ = v_fst_4564_;
v___y_4506_ = v___y_4535_;
v___y_4507_ = v___y_4536_;
v___y_4508_ = v___y_4537_;
v___y_4509_ = v___y_4538_;
v___y_4510_ = v___y_4539_;
v___y_4511_ = v___y_4540_;
v___y_4512_ = v___y_4541_;
v___y_4513_ = v___y_4542_;
v___y_4514_ = v___y_4543_;
v___y_4515_ = v___y_4544_;
v_options_4516_ = v_options_4555_;
v_inheritedTraceOptions_4517_ = v_inheritedTraceOptions_4569_;
v___y_4518_ = v___y_4545_;
goto v___jp_4500_;
}
else
{
lean_object* v___x_4573_; 
v___x_4573_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_4564_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
if (lean_obj_tag(v___x_4573_) == 0)
{
lean_object* v_a_4574_; lean_object* v___x_4575_; 
v_a_4574_ = lean_ctor_get(v___x_4573_, 0);
lean_inc(v_a_4574_);
lean_dec_ref_known(v___x_4573_, 1);
v___x_4575_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_4565_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
if (lean_obj_tag(v___x_4575_) == 0)
{
lean_object* v_a_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4580_; 
v_a_4576_ = lean_ctor_get(v___x_4575_, 0);
lean_inc(v_a_4576_);
lean_dec_ref_known(v___x_4575_, 1);
v___x_4577_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1);
v___x_4578_ = l_Lean_MessageData_ofExpr(v_a_4574_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set_tag(v___x_4567_, 7);
lean_ctor_set(v___x_4567_, 1, v___x_4578_);
lean_ctor_set(v___x_4567_, 0, v___x_4577_);
v___x_4580_ = v___x_4567_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v___x_4577_);
lean_ctor_set(v_reuseFailAlloc_4588_, 1, v___x_4578_);
v___x_4580_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
lean_object* v___x_4581_; lean_object* v___x_4583_; 
v___x_4581_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_4563_ == 0)
{
lean_ctor_set_tag(v___x_4562_, 7);
lean_ctor_set(v___x_4562_, 1, v___x_4581_);
lean_ctor_set(v___x_4562_, 0, v___x_4580_);
v___x_4583_ = v___x_4562_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4587_; 
v_reuseFailAlloc_4587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4587_, 0, v___x_4580_);
lean_ctor_set(v_reuseFailAlloc_4587_, 1, v___x_4581_);
v___x_4583_ = v_reuseFailAlloc_4587_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4584_ = l_Lean_MessageData_ofExpr(v_a_4576_);
v___x_4585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4583_);
lean_ctor_set(v___x_4585_, 1, v___x_4584_);
v___x_4586_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4570_, v___x_4585_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_dec_ref_known(v___x_4586_, 1);
lean_inc(v_snd_4565_);
lean_inc(v_fst_4564_);
v___y_4501_ = v_fst_4564_;
v___y_4502_ = v_snd_4565_;
v___y_4503_ = v_fst_4560_;
v___y_4504_ = v_snd_4565_;
v___y_4505_ = v_fst_4564_;
v___y_4506_ = v___y_4535_;
v___y_4507_ = v___y_4536_;
v___y_4508_ = v___y_4537_;
v___y_4509_ = v___y_4538_;
v___y_4510_ = v___y_4539_;
v___y_4511_ = v___y_4540_;
v___y_4512_ = v___y_4541_;
v___y_4513_ = v___y_4542_;
v___y_4514_ = v___y_4543_;
v___y_4515_ = v___y_4544_;
v_options_4516_ = v_options_4555_;
v_inheritedTraceOptions_4517_ = v_inheritedTraceOptions_4569_;
v___y_4518_ = v___y_4545_;
goto v___jp_4500_;
}
else
{
lean_dec(v_snd_4565_);
lean_dec(v_fst_4564_);
lean_dec(v_fst_4560_);
return v___x_4586_;
}
}
}
}
else
{
lean_object* v_a_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4596_; 
lean_dec(v_a_4574_);
lean_del_object(v___x_4567_);
lean_dec(v_snd_4565_);
lean_dec(v_fst_4564_);
lean_del_object(v___x_4562_);
lean_dec(v_fst_4560_);
v_a_4589_ = lean_ctor_get(v___x_4575_, 0);
v_isSharedCheck_4596_ = !lean_is_exclusive(v___x_4575_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4591_ = v___x_4575_;
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_a_4589_);
lean_dec(v___x_4575_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v___x_4594_; 
if (v_isShared_4592_ == 0)
{
v___x_4594_ = v___x_4591_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v_a_4589_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
return v___x_4594_;
}
}
}
}
else
{
lean_object* v_a_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4604_; 
lean_del_object(v___x_4567_);
lean_dec(v_snd_4565_);
lean_dec(v_fst_4564_);
lean_del_object(v___x_4562_);
lean_dec(v_fst_4560_);
v_a_4597_ = lean_ctor_get(v___x_4573_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4573_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4599_ = v___x_4573_;
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_a_4597_);
lean_dec(v___x_4573_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4602_; 
if (v_isShared_4600_ == 0)
{
v___x_4602_ = v___x_4599_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_a_4597_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
return v___x_4602_;
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
lean_object* v_a_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4615_; 
v_a_4608_ = lean_ctor_get(v___x_4551_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v___x_4551_);
if (v_isSharedCheck_4615_ == 0)
{
v___x_4610_ = v___x_4551_;
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_a_4608_);
lean_dec(v___x_4551_);
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
else
{
lean_object* v_toCold_4616_; lean_object* v_options_4617_; uint8_t v_hasTrace_4618_; 
v_toCold_4616_ = lean_ctor_get(v___y_4544_, 0);
v_options_4617_ = lean_ctor_get(v_toCold_4616_, 2);
v_hasTrace_4618_ = lean_ctor_get_uint8(v_options_4617_, sizeof(void*)*1);
if (v_hasTrace_4618_ == 0)
{
lean_dec(v_a_4547_);
goto v___jp_4430_;
}
else
{
lean_object* v_inheritedTraceOptions_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; uint8_t v___x_4622_; 
v_inheritedTraceOptions_4619_ = lean_ctor_get(v_toCold_4616_, 11);
v___x_4620_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4621_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4);
v___x_4622_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4619_, v_options_4617_, v___x_4621_);
if (v___x_4622_ == 0)
{
lean_dec(v_a_4547_);
goto v___jp_4430_;
}
else
{
lean_object* v___x_4623_; 
v___x_4623_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_a_4547_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
lean_dec(v_a_4547_);
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_object* v_a_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v_a_4624_ = lean_ctor_get(v___x_4623_, 0);
lean_inc(v_a_4624_);
lean_dec_ref_known(v___x_4623_, 1);
v___x_4625_ = l_Lean_MessageData_ofExpr(v_a_4624_);
v___x_4626_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4620_, v___x_4625_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
if (lean_obj_tag(v___x_4626_) == 0)
{
lean_dec_ref_known(v___x_4626_, 1);
goto v___jp_4430_;
}
else
{
return v___x_4626_;
}
}
else
{
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4634_; 
v_a_4627_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4629_ = v___x_4623_;
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4623_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v___x_4632_; 
if (v_isShared_4630_ == 0)
{
v___x_4632_ = v___x_4629_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_a_4627_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4642_; 
v_a_4635_ = lean_ctor_get(v___x_4546_, 0);
v_isSharedCheck_4642_ = !lean_is_exclusive(v___x_4546_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4637_ = v___x_4546_;
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_a_4635_);
lean_dec(v___x_4546_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v___x_4640_; 
if (v_isShared_4638_ == 0)
{
v___x_4640_ = v___x_4637_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v_a_4635_);
v___x_4640_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
return v___x_4640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object* v_c_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_){
_start:
{
lean_object* v_res_4671_; 
v_res_4671_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v_c_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_, v_a_4668_, v_a_4669_);
lean_dec(v_a_4669_);
lean_dec_ref(v_a_4668_);
lean_dec(v_a_4667_);
lean_dec_ref(v_a_4666_);
lean_dec(v_a_4665_);
lean_dec_ref(v_a_4664_);
lean_dec(v_a_4663_);
lean_dec_ref(v_a_4662_);
lean_dec(v_a_4661_);
lean_dec(v_a_4660_);
lean_dec(v_a_4659_);
return v_res_4671_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2(void){
_start:
{
lean_object* v_cls_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; 
v_cls_4676_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4678_ = l_Lean_Name_append(v___x_4677_, v_cls_4676_);
return v___x_4678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object* v_a_4679_, lean_object* v_b_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_){
_start:
{
lean_object* v_toCold_4689_; lean_object* v_options_4690_; uint8_t v_hasTrace_4691_; 
v_toCold_4689_ = lean_ctor_get(v_a_4683_, 0);
v_options_4690_ = lean_ctor_get(v_toCold_4689_, 2);
v_hasTrace_4691_ = lean_ctor_get_uint8(v_options_4690_, sizeof(void*)*1);
if (v_hasTrace_4691_ == 0)
{
lean_dec_ref(v_b_4680_);
lean_dec_ref(v_a_4679_);
goto v___jp_4686_;
}
else
{
lean_object* v_inheritedTraceOptions_4692_; lean_object* v_cls_4693_; lean_object* v___x_4694_; uint8_t v___x_4695_; 
v_inheritedTraceOptions_4692_ = lean_ctor_get(v_toCold_4689_, 11);
v_cls_4693_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4694_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2);
v___x_4695_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4692_, v_options_4690_, v___x_4694_);
if (v___x_4695_ == 0)
{
lean_dec_ref(v_b_4680_);
lean_dec_ref(v_a_4679_);
goto v___jp_4686_;
}
else
{
lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; 
v___x_4696_ = l_Lean_MessageData_ofExpr(v_a_4679_);
v___x_4697_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_4698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4698_, 0, v___x_4696_);
lean_ctor_set(v___x_4698_, 1, v___x_4697_);
v___x_4699_ = l_Lean_MessageData_ofExpr(v_b_4680_);
v___x_4700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4700_, 0, v___x_4698_);
lean_ctor_set(v___x_4700_, 1, v___x_4699_);
v___x_4701_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4693_, v___x_4700_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_);
return v___x_4701_;
}
}
v___jp_4686_:
{
lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4687_ = lean_box(0);
v___x_4688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4688_, 0, v___x_4687_);
return v___x_4688_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object* v_a_4702_, lean_object* v_b_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_){
_start:
{
lean_object* v_res_4709_; 
v_res_4709_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4702_, v_b_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_);
lean_dec(v_a_4707_);
lean_dec_ref(v_a_4706_);
lean_dec(v_a_4705_);
lean_dec_ref(v_a_4704_);
return v_res_4709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object* v_a_4710_, lean_object* v_b_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_){
_start:
{
lean_object* v___x_4724_; 
v___x_4724_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4710_, v_b_4711_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_);
return v___x_4724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object* v_a_4725_, lean_object* v_b_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_){
_start:
{
lean_object* v_res_4739_; 
v_res_4739_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(v_a_4725_, v_b_4726_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_, v_a_4736_, v_a_4737_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object* v_a_4740_, lean_object* v_b_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_){
_start:
{
uint8_t v___x_4754_; lean_object* v___x_4755_; 
v___x_4754_ = 0;
lean_inc_ref(v_a_4740_);
v___x_4755_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_4740_, v___x_4754_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
if (lean_obj_tag(v___x_4755_) == 0)
{
lean_object* v_a_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4795_; 
v_a_4756_ = lean_ctor_get(v___x_4755_, 0);
v_isSharedCheck_4795_ = !lean_is_exclusive(v___x_4755_);
if (v_isSharedCheck_4795_ == 0)
{
v___x_4758_ = v___x_4755_;
v_isShared_4759_ = v_isSharedCheck_4795_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_a_4756_);
lean_dec(v___x_4755_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4795_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
if (lean_obj_tag(v_a_4756_) == 1)
{
lean_object* v_val_4760_; lean_object* v___x_4761_; 
lean_del_object(v___x_4758_);
v_val_4760_ = lean_ctor_get(v_a_4756_, 0);
lean_inc(v_val_4760_);
lean_dec_ref_known(v_a_4756_, 1);
lean_inc_ref(v_b_4741_);
v___x_4761_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_4741_, v___x_4754_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
if (lean_obj_tag(v___x_4761_) == 0)
{
lean_object* v_a_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4782_; 
v_a_4762_ = lean_ctor_get(v___x_4761_, 0);
v_isSharedCheck_4782_ = !lean_is_exclusive(v___x_4761_);
if (v_isSharedCheck_4782_ == 0)
{
v___x_4764_ = v___x_4761_;
v_isShared_4765_ = v_isSharedCheck_4782_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_a_4762_);
lean_dec(v___x_4761_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4782_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
if (lean_obj_tag(v_a_4762_) == 1)
{
lean_object* v_val_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; uint8_t v___x_4770_; 
v_val_4766_ = lean_ctor_get(v_a_4762_, 0);
lean_inc_n(v_val_4766_, 2);
lean_dec_ref_known(v_a_4762_, 1);
lean_inc(v_val_4760_);
v___x_4767_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4767_, 0, v_val_4760_);
lean_ctor_set(v___x_4767_, 1, v_val_4766_);
v___x_4768_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4767_);
v___x_4769_ = lean_box(0);
v___x_4770_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4768_, v___x_4769_);
if (v___x_4770_ == 0)
{
lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; 
lean_del_object(v___x_4764_);
v___x_4771_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4771_, 0, v_a_4740_);
lean_ctor_set(v___x_4771_, 1, v_b_4741_);
lean_ctor_set(v___x_4771_, 2, v_val_4760_);
lean_ctor_set(v___x_4771_, 3, v_val_4766_);
v___x_4772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4772_, 0, v___x_4768_);
lean_ctor_set(v___x_4772_, 1, v___x_4771_);
v___x_4773_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_4772_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
return v___x_4773_;
}
else
{
lean_object* v___x_4774_; lean_object* v___x_4776_; 
lean_dec(v___x_4768_);
lean_dec(v_val_4766_);
lean_dec(v_val_4760_);
lean_dec_ref(v_b_4741_);
lean_dec_ref(v_a_4740_);
v___x_4774_ = lean_box(0);
if (v_isShared_4765_ == 0)
{
lean_ctor_set(v___x_4764_, 0, v___x_4774_);
v___x_4776_ = v___x_4764_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v___x_4774_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
else
{
lean_object* v___x_4778_; lean_object* v___x_4780_; 
lean_dec(v_a_4762_);
lean_dec(v_val_4760_);
lean_dec_ref(v_b_4741_);
lean_dec_ref(v_a_4740_);
v___x_4778_ = lean_box(0);
if (v_isShared_4765_ == 0)
{
lean_ctor_set(v___x_4764_, 0, v___x_4778_);
v___x_4780_ = v___x_4764_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v___x_4778_);
v___x_4780_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
return v___x_4780_;
}
}
}
}
else
{
lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4790_; 
lean_dec(v_val_4760_);
lean_dec_ref(v_b_4741_);
lean_dec_ref(v_a_4740_);
v_a_4783_ = lean_ctor_get(v___x_4761_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4761_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4785_ = v___x_4761_;
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_dec(v___x_4761_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4788_; 
if (v_isShared_4786_ == 0)
{
v___x_4788_ = v___x_4785_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_a_4783_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
}
}
else
{
lean_object* v___x_4791_; lean_object* v___x_4793_; 
lean_dec(v_a_4756_);
lean_dec_ref(v_b_4741_);
lean_dec_ref(v_a_4740_);
v___x_4791_ = lean_box(0);
if (v_isShared_4759_ == 0)
{
lean_ctor_set(v___x_4758_, 0, v___x_4791_);
v___x_4793_ = v___x_4758_;
goto v_reusejp_4792_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v___x_4791_);
v___x_4793_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4792_;
}
v_reusejp_4792_:
{
return v___x_4793_;
}
}
}
}
else
{
lean_object* v_a_4796_; lean_object* v___x_4798_; uint8_t v_isShared_4799_; uint8_t v_isSharedCheck_4803_; 
lean_dec_ref(v_b_4741_);
lean_dec_ref(v_a_4740_);
v_a_4796_ = lean_ctor_get(v___x_4755_, 0);
v_isSharedCheck_4803_ = !lean_is_exclusive(v___x_4755_);
if (v_isSharedCheck_4803_ == 0)
{
v___x_4798_ = v___x_4755_;
v_isShared_4799_ = v_isSharedCheck_4803_;
goto v_resetjp_4797_;
}
else
{
lean_inc(v_a_4796_);
lean_dec(v___x_4755_);
v___x_4798_ = lean_box(0);
v_isShared_4799_ = v_isSharedCheck_4803_;
goto v_resetjp_4797_;
}
v_resetjp_4797_:
{
lean_object* v___x_4801_; 
if (v_isShared_4799_ == 0)
{
v___x_4801_ = v___x_4798_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v_a_4796_);
v___x_4801_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
return v___x_4801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___boxed(lean_object* v_a_4804_, lean_object* v_b_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_){
_start:
{
lean_object* v_res_4818_; 
v_res_4818_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_4804_, v_b_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(lean_object* v_a_4819_, lean_object* v_b_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_){
_start:
{
lean_object* v___x_4833_; 
v___x_4833_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
if (lean_obj_tag(v___x_4833_) == 0)
{
lean_object* v_a_4834_; lean_object* v___x_4835_; 
v_a_4834_ = lean_ctor_get(v___x_4833_, 0);
lean_inc(v_a_4834_);
lean_dec_ref_known(v___x_4833_, 1);
lean_inc_ref(v_a_4819_);
v___x_4835_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_4819_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_object* v_a_4836_; lean_object* v_fst_4837_; lean_object* v___x_4838_; 
v_a_4836_ = lean_ctor_get(v___x_4835_, 0);
lean_inc(v_a_4836_);
lean_dec_ref_known(v___x_4835_, 1);
v_fst_4837_ = lean_ctor_get(v_a_4836_, 0);
lean_inc(v_fst_4837_);
lean_dec(v_a_4836_);
lean_inc_ref(v_b_4820_);
v___x_4838_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
if (lean_obj_tag(v___x_4838_) == 0)
{
lean_object* v_a_4839_; lean_object* v_fst_4840_; lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4903_; 
v_a_4839_ = lean_ctor_get(v___x_4838_, 0);
lean_inc(v_a_4839_);
lean_dec_ref_known(v___x_4838_, 1);
v_fst_4840_ = lean_ctor_get(v_a_4839_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v_a_4839_);
if (v_isSharedCheck_4903_ == 0)
{
lean_object* v_unused_4904_; 
v_unused_4904_ = lean_ctor_get(v_a_4839_, 1);
lean_dec(v_unused_4904_);
v___x_4842_ = v_a_4839_;
v_isShared_4843_ = v_isSharedCheck_4903_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_fst_4840_);
lean_dec(v_a_4839_);
v___x_4842_ = lean_box(0);
v_isShared_4843_ = v_isSharedCheck_4903_;
goto v_resetjp_4841_;
}
v_resetjp_4841_:
{
lean_object* v_id_4844_; lean_object* v_structId_4845_; uint8_t v___x_4846_; lean_object* v___x_4847_; 
v_id_4844_ = lean_ctor_get(v_a_4834_, 0);
lean_inc(v_id_4844_);
v_structId_4845_ = lean_ctor_get(v_a_4834_, 1);
lean_inc(v_structId_4845_);
lean_dec(v_a_4834_);
v___x_4846_ = 0;
v___x_4847_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4837_, v___x_4846_, v_structId_4845_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
if (lean_obj_tag(v___x_4847_) == 0)
{
lean_object* v_a_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4894_; 
v_a_4848_ = lean_ctor_get(v___x_4847_, 0);
v_isSharedCheck_4894_ = !lean_is_exclusive(v___x_4847_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4850_ = v___x_4847_;
v_isShared_4851_ = v_isSharedCheck_4894_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_a_4848_);
lean_dec(v___x_4847_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4894_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
if (lean_obj_tag(v_a_4848_) == 1)
{
lean_object* v_val_4852_; lean_object* v___x_4853_; 
lean_del_object(v___x_4850_);
v_val_4852_ = lean_ctor_get(v_a_4848_, 0);
lean_inc(v_val_4852_);
lean_dec_ref_known(v_a_4848_, 1);
v___x_4853_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4840_, v___x_4846_, v_structId_4845_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
if (lean_obj_tag(v___x_4853_) == 0)
{
lean_object* v_a_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4881_; 
v_a_4854_ = lean_ctor_get(v___x_4853_, 0);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4853_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4856_ = v___x_4853_;
v_isShared_4857_ = v_isSharedCheck_4881_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_a_4854_);
lean_dec(v___x_4853_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4881_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
if (lean_obj_tag(v_a_4854_) == 1)
{
lean_object* v_val_4858_; lean_object* v___x_4860_; 
v_val_4858_ = lean_ctor_get(v_a_4854_, 0);
lean_inc_n(v_val_4858_, 2);
lean_dec_ref_known(v_a_4854_, 1);
lean_inc(v_val_4852_);
if (v_isShared_4843_ == 0)
{
lean_ctor_set_tag(v___x_4842_, 3);
lean_ctor_set(v___x_4842_, 1, v_val_4858_);
lean_ctor_set(v___x_4842_, 0, v_val_4852_);
v___x_4860_ = v___x_4842_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4876_; 
v_reuseFailAlloc_4876_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4876_, 0, v_val_4852_);
lean_ctor_set(v_reuseFailAlloc_4876_, 1, v_val_4858_);
v___x_4860_ = v_reuseFailAlloc_4876_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
lean_object* v___x_4861_; lean_object* v___x_4862_; uint8_t v___x_4863_; 
v___x_4861_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4860_);
v___x_4862_ = lean_box(0);
v___x_4863_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4861_, v___x_4862_);
if (v___x_4863_ == 0)
{
lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
lean_del_object(v___x_4856_);
lean_inc(v_val_4858_);
lean_inc(v_val_4852_);
lean_inc(v_id_4844_);
lean_inc_ref(v_b_4820_);
lean_inc_ref(v_a_4819_);
v___x_4864_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4864_, 0, v_a_4819_);
lean_ctor_set(v___x_4864_, 1, v_b_4820_);
lean_ctor_set(v___x_4864_, 2, v_id_4844_);
lean_ctor_set(v___x_4864_, 3, v_val_4852_);
lean_ctor_set(v___x_4864_, 4, v_val_4858_);
lean_inc(v___x_4861_);
v___x_4865_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4865_, 0, v___x_4861_);
lean_ctor_set(v___x_4865_, 1, v___x_4864_);
lean_ctor_set_uint8(v___x_4865_, sizeof(void*)*2, v___x_4846_);
v___x_4866_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4865_, v_structId_4845_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; 
lean_dec_ref_known(v___x_4866_, 1);
v___x_4867_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4868_ = l_Lean_Grind_Linarith_Poly_mul(v___x_4861_, v___x_4867_);
v___x_4869_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4869_, 0, v_b_4820_);
lean_ctor_set(v___x_4869_, 1, v_a_4819_);
lean_ctor_set(v___x_4869_, 2, v_id_4844_);
lean_ctor_set(v___x_4869_, 3, v_val_4858_);
lean_ctor_set(v___x_4869_, 4, v_val_4852_);
v___x_4870_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4870_, 0, v___x_4868_);
lean_ctor_set(v___x_4870_, 1, v___x_4869_);
lean_ctor_set_uint8(v___x_4870_, sizeof(void*)*2, v___x_4846_);
v___x_4871_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4870_, v_structId_4845_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
lean_dec(v_structId_4845_);
return v___x_4871_;
}
else
{
lean_dec(v___x_4861_);
lean_dec(v_val_4858_);
lean_dec(v_val_4852_);
lean_dec(v_structId_4845_);
lean_dec(v_id_4844_);
lean_dec_ref(v_b_4820_);
lean_dec_ref(v_a_4819_);
return v___x_4866_;
}
}
else
{
lean_object* v___x_4872_; lean_object* v___x_4874_; 
lean_dec(v___x_4861_);
lean_dec(v_val_4858_);
lean_dec(v_val_4852_);
lean_dec(v_structId_4845_);
lean_dec(v_id_4844_);
lean_dec_ref(v_b_4820_);
lean_dec_ref(v_a_4819_);
v___x_4872_ = lean_box(0);
if (v_isShared_4857_ == 0)
{
lean_ctor_set(v___x_4856_, 0, v___x_4872_);
v___x_4874_ = v___x_4856_;
goto v_reusejp_4873_;
}
else
{
lean_object* v_reuseFailAlloc_4875_; 
v_reuseFailAlloc_4875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4875_, 0, v___x_4872_);
v___x_4874_ = v_reuseFailAlloc_4875_;
goto v_reusejp_4873_;
}
v_reusejp_4873_:
{
return v___x_4874_;
}
}
}
}
else
{
lean_object* v___x_4877_; lean_object* v___x_4879_; 
lean_dec(v_a_4854_);
lean_dec(v_val_4852_);
lean_dec(v_structId_4845_);
lean_dec(v_id_4844_);
lean_del_object(v___x_4842_);
lean_dec_ref(v_b_4820_);
lean_dec_ref(v_a_4819_);
v___x_4877_ = lean_box(0);
if (v_isShared_4857_ == 0)
{
lean_ctor_set(v___x_4856_, 0, v___x_4877_);
v___x_4879_ = v___x_4856_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v___x_4877_);
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
lean_object* v_a_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4889_; 
lean_dec(v_val_4852_);
lean_dec(v_structId_4845_);
lean_dec(v_id_4844_);
lean_del_object(v___x_4842_);
lean_dec_ref(v_b_4820_);
lean_dec_ref(v_a_4819_);
v_a_4882_ = lean_ctor_get(v___x_4853_, 0);
v_isSharedCheck_4889_ = !lean_is_exclusive(v___x_4853_);
if (v_isSharedCheck_4889_ == 0)
{
v___x_4884_ = v___x_4853_;
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_a_4882_);
lean_dec(v___x_4853_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___x_4887_; 
if (v_isShared_4885_ == 0)
{
v___x_4887_ = v___x_4884_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v_a_4882_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
return v___x_4887_;
}
}
}
}
else
{
lean_object* v___x_4890_; lean_object* v___x_4892_; 
lean_dec(v_a_4848_);
lean_dec(v_structId_4845_);
lean_dec(v_id_4844_);
lean_del_object(v___x_4842_);
lean_dec(v_fst_4840_);
lean_dec_ref(v_b_4820_);
lean_dec_ref(v_a_4819_);
v___x_4890_ = lean_box(0);
if (v_isShared_4851_ == 0)
{
lean_ctor_set(v___x_4850_, 0, v___x_4890_);
v___x_4892_ = v___x_4850_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v___x_4890_);
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
lean_dec(v_structId_4845_);
lean_dec(v_id_4844_);
lean_del_object(v___x_4842_);
lean_dec(v_fst_4840_);
lean_dec_ref(v_b_4820_);
lean_dec_ref(v_a_4819_);
v_a_4895_ = lean_ctor_get(v___x_4847_, 0);
v_isSharedCheck_4902_ = !lean_is_exclusive(v___x_4847_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4897_ = v___x_4847_;
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_a_4895_);
lean_dec(v___x_4847_);
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
else
{
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4912_; 
lean_dec(v_fst_4837_);
lean_dec(v_a_4834_);
lean_dec_ref(v_b_4820_);
lean_dec_ref(v_a_4819_);
v_a_4905_ = lean_ctor_get(v___x_4838_, 0);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4838_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4907_ = v___x_4838_;
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4838_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4910_; 
if (v_isShared_4908_ == 0)
{
v___x_4910_ = v___x_4907_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_a_4905_);
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
lean_dec(v_a_4834_);
lean_dec_ref(v_b_4820_);
lean_dec_ref(v_a_4819_);
v_a_4913_ = lean_ctor_get(v___x_4835_, 0);
v_isSharedCheck_4920_ = !lean_is_exclusive(v___x_4835_);
if (v_isSharedCheck_4920_ == 0)
{
v___x_4915_ = v___x_4835_;
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_a_4913_);
lean_dec(v___x_4835_);
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
lean_dec_ref(v_b_4820_);
lean_dec_ref(v_a_4819_);
v_a_4921_ = lean_ctor_get(v___x_4833_, 0);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4923_ = v___x_4833_;
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_a_4921_);
lean_dec(v___x_4833_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27___boxed(lean_object* v_a_4929_, lean_object* v_b_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_){
_start:
{
lean_object* v_res_4943_; 
v_res_4943_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_4929_, v_b_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_);
lean_dec(v_a_4941_);
lean_dec_ref(v_a_4940_);
lean_dec(v_a_4939_);
lean_dec_ref(v_a_4938_);
lean_dec(v_a_4937_);
lean_dec_ref(v_a_4936_);
lean_dec(v_a_4935_);
lean_dec_ref(v_a_4934_);
lean_dec(v_a_4933_);
lean_dec(v_a_4932_);
lean_dec(v_a_4931_);
return v_res_4943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(lean_object* v_a_4944_, lean_object* v_b_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_){
_start:
{
lean_object* v___x_4958_; 
v___x_4958_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_);
if (lean_obj_tag(v___x_4958_) == 0)
{
lean_object* v_a_4959_; lean_object* v___x_4960_; 
v_a_4959_ = lean_ctor_get(v___x_4958_, 0);
lean_inc(v_a_4959_);
lean_dec_ref_known(v___x_4958_, 1);
lean_inc_ref(v_a_4944_);
v___x_4960_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_4944_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_);
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_object* v_a_4961_; lean_object* v_fst_4962_; lean_object* v___x_4964_; uint8_t v_isShared_4965_; uint8_t v_isSharedCheck_5038_; 
v_a_4961_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_a_4961_);
lean_dec_ref_known(v___x_4960_, 1);
v_fst_4962_ = lean_ctor_get(v_a_4961_, 0);
v_isSharedCheck_5038_ = !lean_is_exclusive(v_a_4961_);
if (v_isSharedCheck_5038_ == 0)
{
lean_object* v_unused_5039_; 
v_unused_5039_ = lean_ctor_get(v_a_4961_, 1);
lean_dec(v_unused_5039_);
v___x_4964_ = v_a_4961_;
v_isShared_4965_ = v_isSharedCheck_5038_;
goto v_resetjp_4963_;
}
else
{
lean_inc(v_fst_4962_);
lean_dec(v_a_4961_);
v___x_4964_ = lean_box(0);
v_isShared_4965_ = v_isSharedCheck_5038_;
goto v_resetjp_4963_;
}
v_resetjp_4963_:
{
lean_object* v___x_4966_; 
lean_inc_ref(v_b_4945_);
v___x_4966_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_);
if (lean_obj_tag(v___x_4966_) == 0)
{
lean_object* v_a_4967_; lean_object* v_fst_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_5028_; 
v_a_4967_ = lean_ctor_get(v___x_4966_, 0);
lean_inc(v_a_4967_);
lean_dec_ref_known(v___x_4966_, 1);
v_fst_4968_ = lean_ctor_get(v_a_4967_, 0);
v_isSharedCheck_5028_ = !lean_is_exclusive(v_a_4967_);
if (v_isSharedCheck_5028_ == 0)
{
lean_object* v_unused_5029_; 
v_unused_5029_ = lean_ctor_get(v_a_4967_, 1);
lean_dec(v_unused_5029_);
v___x_4970_ = v_a_4967_;
v_isShared_4971_ = v_isSharedCheck_5028_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_fst_4968_);
lean_dec(v_a_4967_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_5028_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v_id_4972_; lean_object* v_structId_4973_; uint8_t v___x_4974_; lean_object* v___x_4975_; 
v_id_4972_ = lean_ctor_get(v_a_4959_, 0);
lean_inc(v_id_4972_);
v_structId_4973_ = lean_ctor_get(v_a_4959_, 1);
lean_inc(v_structId_4973_);
lean_dec(v_a_4959_);
v___x_4974_ = 0;
v___x_4975_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4962_, v___x_4974_, v_structId_4973_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_);
if (lean_obj_tag(v___x_4975_) == 0)
{
lean_object* v_a_4976_; lean_object* v___x_4978_; uint8_t v_isShared_4979_; uint8_t v_isSharedCheck_5019_; 
v_a_4976_ = lean_ctor_get(v___x_4975_, 0);
v_isSharedCheck_5019_ = !lean_is_exclusive(v___x_4975_);
if (v_isSharedCheck_5019_ == 0)
{
v___x_4978_ = v___x_4975_;
v_isShared_4979_ = v_isSharedCheck_5019_;
goto v_resetjp_4977_;
}
else
{
lean_inc(v_a_4976_);
lean_dec(v___x_4975_);
v___x_4978_ = lean_box(0);
v_isShared_4979_ = v_isSharedCheck_5019_;
goto v_resetjp_4977_;
}
v_resetjp_4977_:
{
if (lean_obj_tag(v_a_4976_) == 1)
{
lean_object* v_val_4980_; lean_object* v___x_4981_; 
lean_del_object(v___x_4978_);
v_val_4980_ = lean_ctor_get(v_a_4976_, 0);
lean_inc(v_val_4980_);
lean_dec_ref_known(v_a_4976_, 1);
v___x_4981_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4968_, v___x_4974_, v_structId_4973_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_);
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_object* v_a_4982_; lean_object* v___x_4984_; uint8_t v_isShared_4985_; uint8_t v_isSharedCheck_5006_; 
v_a_4982_ = lean_ctor_get(v___x_4981_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4981_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_4984_ = v___x_4981_;
v_isShared_4985_ = v_isSharedCheck_5006_;
goto v_resetjp_4983_;
}
else
{
lean_inc(v_a_4982_);
lean_dec(v___x_4981_);
v___x_4984_ = lean_box(0);
v_isShared_4985_ = v_isSharedCheck_5006_;
goto v_resetjp_4983_;
}
v_resetjp_4983_:
{
if (lean_obj_tag(v_a_4982_) == 1)
{
lean_object* v_val_4986_; lean_object* v___x_4988_; 
v_val_4986_ = lean_ctor_get(v_a_4982_, 0);
lean_inc_n(v_val_4986_, 2);
lean_dec_ref_known(v_a_4982_, 1);
lean_inc(v_val_4980_);
if (v_isShared_4971_ == 0)
{
lean_ctor_set_tag(v___x_4970_, 3);
lean_ctor_set(v___x_4970_, 1, v_val_4986_);
lean_ctor_set(v___x_4970_, 0, v_val_4980_);
v___x_4988_ = v___x_4970_;
goto v_reusejp_4987_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_val_4980_);
lean_ctor_set(v_reuseFailAlloc_5001_, 1, v_val_4986_);
v___x_4988_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4987_;
}
v_reusejp_4987_:
{
lean_object* v___x_4989_; lean_object* v___x_4990_; uint8_t v___x_4991_; 
v___x_4989_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4988_);
v___x_4990_ = lean_box(0);
v___x_4991_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4989_, v___x_4990_);
if (v___x_4991_ == 0)
{
lean_object* v___x_4992_; lean_object* v___x_4994_; 
lean_del_object(v___x_4984_);
v___x_4992_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_4992_, 0, v_a_4944_);
lean_ctor_set(v___x_4992_, 1, v_b_4945_);
lean_ctor_set(v___x_4992_, 2, v_id_4972_);
lean_ctor_set(v___x_4992_, 3, v_val_4980_);
lean_ctor_set(v___x_4992_, 4, v_val_4986_);
if (v_isShared_4965_ == 0)
{
lean_ctor_set(v___x_4964_, 1, v___x_4992_);
lean_ctor_set(v___x_4964_, 0, v___x_4989_);
v___x_4994_ = v___x_4964_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v___x_4989_);
lean_ctor_set(v_reuseFailAlloc_4996_, 1, v___x_4992_);
v___x_4994_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
lean_object* v___x_4995_; 
v___x_4995_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_4994_, v_structId_4973_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_);
lean_dec(v_structId_4973_);
return v___x_4995_;
}
}
else
{
lean_object* v___x_4997_; lean_object* v___x_4999_; 
lean_dec(v___x_4989_);
lean_dec(v_val_4986_);
lean_dec(v_val_4980_);
lean_dec(v_structId_4973_);
lean_dec(v_id_4972_);
lean_del_object(v___x_4964_);
lean_dec_ref(v_b_4945_);
lean_dec_ref(v_a_4944_);
v___x_4997_ = lean_box(0);
if (v_isShared_4985_ == 0)
{
lean_ctor_set(v___x_4984_, 0, v___x_4997_);
v___x_4999_ = v___x_4984_;
goto v_reusejp_4998_;
}
else
{
lean_object* v_reuseFailAlloc_5000_; 
v_reuseFailAlloc_5000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5000_, 0, v___x_4997_);
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
lean_object* v___x_5002_; lean_object* v___x_5004_; 
lean_dec(v_a_4982_);
lean_dec(v_val_4980_);
lean_dec(v_structId_4973_);
lean_dec(v_id_4972_);
lean_del_object(v___x_4970_);
lean_del_object(v___x_4964_);
lean_dec_ref(v_b_4945_);
lean_dec_ref(v_a_4944_);
v___x_5002_ = lean_box(0);
if (v_isShared_4985_ == 0)
{
lean_ctor_set(v___x_4984_, 0, v___x_5002_);
v___x_5004_ = v___x_4984_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v___x_5002_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
}
else
{
lean_object* v_a_5007_; lean_object* v___x_5009_; uint8_t v_isShared_5010_; uint8_t v_isSharedCheck_5014_; 
lean_dec(v_val_4980_);
lean_dec(v_structId_4973_);
lean_dec(v_id_4972_);
lean_del_object(v___x_4970_);
lean_del_object(v___x_4964_);
lean_dec_ref(v_b_4945_);
lean_dec_ref(v_a_4944_);
v_a_5007_ = lean_ctor_get(v___x_4981_, 0);
v_isSharedCheck_5014_ = !lean_is_exclusive(v___x_4981_);
if (v_isSharedCheck_5014_ == 0)
{
v___x_5009_ = v___x_4981_;
v_isShared_5010_ = v_isSharedCheck_5014_;
goto v_resetjp_5008_;
}
else
{
lean_inc(v_a_5007_);
lean_dec(v___x_4981_);
v___x_5009_ = lean_box(0);
v_isShared_5010_ = v_isSharedCheck_5014_;
goto v_resetjp_5008_;
}
v_resetjp_5008_:
{
lean_object* v___x_5012_; 
if (v_isShared_5010_ == 0)
{
v___x_5012_ = v___x_5009_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v_a_5007_);
v___x_5012_ = v_reuseFailAlloc_5013_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
return v___x_5012_;
}
}
}
}
else
{
lean_object* v___x_5015_; lean_object* v___x_5017_; 
lean_dec(v_a_4976_);
lean_dec(v_structId_4973_);
lean_dec(v_id_4972_);
lean_del_object(v___x_4970_);
lean_dec(v_fst_4968_);
lean_del_object(v___x_4964_);
lean_dec_ref(v_b_4945_);
lean_dec_ref(v_a_4944_);
v___x_5015_ = lean_box(0);
if (v_isShared_4979_ == 0)
{
lean_ctor_set(v___x_4978_, 0, v___x_5015_);
v___x_5017_ = v___x_4978_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v___x_5015_);
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
lean_dec(v_structId_4973_);
lean_dec(v_id_4972_);
lean_del_object(v___x_4970_);
lean_dec(v_fst_4968_);
lean_del_object(v___x_4964_);
lean_dec_ref(v_b_4945_);
lean_dec_ref(v_a_4944_);
v_a_5020_ = lean_ctor_get(v___x_4975_, 0);
v_isSharedCheck_5027_ = !lean_is_exclusive(v___x_4975_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_5022_ = v___x_4975_;
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
else
{
lean_inc(v_a_5020_);
lean_dec(v___x_4975_);
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
}
else
{
lean_object* v_a_5030_; lean_object* v___x_5032_; uint8_t v_isShared_5033_; uint8_t v_isSharedCheck_5037_; 
lean_del_object(v___x_4964_);
lean_dec(v_fst_4962_);
lean_dec(v_a_4959_);
lean_dec_ref(v_b_4945_);
lean_dec_ref(v_a_4944_);
v_a_5030_ = lean_ctor_get(v___x_4966_, 0);
v_isSharedCheck_5037_ = !lean_is_exclusive(v___x_4966_);
if (v_isSharedCheck_5037_ == 0)
{
v___x_5032_ = v___x_4966_;
v_isShared_5033_ = v_isSharedCheck_5037_;
goto v_resetjp_5031_;
}
else
{
lean_inc(v_a_5030_);
lean_dec(v___x_4966_);
v___x_5032_ = lean_box(0);
v_isShared_5033_ = v_isSharedCheck_5037_;
goto v_resetjp_5031_;
}
v_resetjp_5031_:
{
lean_object* v___x_5035_; 
if (v_isShared_5033_ == 0)
{
v___x_5035_ = v___x_5032_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_a_5030_);
v___x_5035_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
return v___x_5035_;
}
}
}
}
}
else
{
lean_object* v_a_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5047_; 
lean_dec(v_a_4959_);
lean_dec_ref(v_b_4945_);
lean_dec_ref(v_a_4944_);
v_a_5040_ = lean_ctor_get(v___x_4960_, 0);
v_isSharedCheck_5047_ = !lean_is_exclusive(v___x_4960_);
if (v_isSharedCheck_5047_ == 0)
{
v___x_5042_ = v___x_4960_;
v_isShared_5043_ = v_isSharedCheck_5047_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_a_5040_);
lean_dec(v___x_4960_);
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
else
{
lean_object* v_a_5048_; lean_object* v___x_5050_; uint8_t v_isShared_5051_; uint8_t v_isSharedCheck_5055_; 
lean_dec_ref(v_b_4945_);
lean_dec_ref(v_a_4944_);
v_a_5048_ = lean_ctor_get(v___x_4958_, 0);
v_isSharedCheck_5055_ = !lean_is_exclusive(v___x_4958_);
if (v_isSharedCheck_5055_ == 0)
{
v___x_5050_ = v___x_4958_;
v_isShared_5051_ = v_isSharedCheck_5055_;
goto v_resetjp_5049_;
}
else
{
lean_inc(v_a_5048_);
lean_dec(v___x_4958_);
v___x_5050_ = lean_box(0);
v_isShared_5051_ = v_isSharedCheck_5055_;
goto v_resetjp_5049_;
}
v_resetjp_5049_:
{
lean_object* v___x_5053_; 
if (v_isShared_5051_ == 0)
{
v___x_5053_ = v___x_5050_;
goto v_reusejp_5052_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_a_5048_);
v___x_5053_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5052_;
}
v_reusejp_5052_:
{
return v___x_5053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq___boxed(lean_object* v_a_5056_, lean_object* v_b_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_){
_start:
{
lean_object* v_res_5070_; 
v_res_5070_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5056_, v_b_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_);
lean_dec(v_a_5068_);
lean_dec_ref(v_a_5067_);
lean_dec(v_a_5066_);
lean_dec_ref(v_a_5065_);
lean_dec(v_a_5064_);
lean_dec_ref(v_a_5063_);
lean_dec(v_a_5062_);
lean_dec_ref(v_a_5061_);
lean_dec(v_a_5060_);
lean_dec(v_a_5059_);
lean_dec(v_a_5058_);
return v_res_5070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq(lean_object* v_a_5071_, lean_object* v_b_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_){
_start:
{
size_t v___x_5084_; size_t v___x_5085_; uint8_t v___x_5086_; 
v___x_5084_ = lean_ptr_addr(v_a_5071_);
v___x_5085_ = lean_ptr_addr(v_b_5072_);
v___x_5086_ = lean_usize_dec_eq(v___x_5084_, v___x_5085_);
if (v___x_5086_ == 0)
{
lean_object* v___x_5087_; 
v___x_5087_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5071_, v_b_5072_, v_a_5073_, v_a_5081_);
if (lean_obj_tag(v___x_5087_) == 0)
{
lean_object* v_a_5088_; 
v_a_5088_ = lean_ctor_get(v___x_5087_, 0);
lean_inc(v_a_5088_);
lean_dec_ref_known(v___x_5087_, 1);
if (lean_obj_tag(v_a_5088_) == 1)
{
lean_object* v_val_5089_; lean_object* v___x_5090_; 
v_val_5089_ = lean_ctor_get(v_a_5088_, 0);
lean_inc(v_val_5089_);
lean_dec_ref_known(v_a_5088_, 1);
v___x_5090_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_val_5089_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_);
if (lean_obj_tag(v___x_5090_) == 0)
{
lean_object* v_a_5091_; uint8_t v___x_5092_; 
v_a_5091_ = lean_ctor_get(v___x_5090_, 0);
lean_inc(v_a_5091_);
lean_dec_ref_known(v___x_5090_, 1);
v___x_5092_ = lean_unbox(v_a_5091_);
lean_dec(v_a_5091_);
if (v___x_5092_ == 0)
{
lean_object* v___x_5093_; 
v___x_5093_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5089_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_);
if (lean_obj_tag(v___x_5093_) == 0)
{
lean_object* v_a_5094_; uint8_t v___x_5095_; 
v_a_5094_ = lean_ctor_get(v___x_5093_, 0);
lean_inc(v_a_5094_);
lean_dec_ref_known(v___x_5093_, 1);
v___x_5095_ = lean_unbox(v_a_5094_);
lean_dec(v_a_5094_);
if (v___x_5095_ == 0)
{
lean_object* v___x_5096_; 
v___x_5096_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_5071_, v_b_5072_, v_val_5089_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_);
lean_dec(v_val_5089_);
return v___x_5096_;
}
else
{
lean_object* v___x_5097_; 
lean_dec(v_val_5089_);
v___x_5097_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_5071_, v_b_5072_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_);
return v___x_5097_;
}
}
else
{
lean_object* v_a_5098_; lean_object* v___x_5100_; uint8_t v_isShared_5101_; uint8_t v_isSharedCheck_5105_; 
lean_dec(v_val_5089_);
lean_dec_ref(v_b_5072_);
lean_dec_ref(v_a_5071_);
v_a_5098_ = lean_ctor_get(v___x_5093_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_5093_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5100_ = v___x_5093_;
v_isShared_5101_ = v_isSharedCheck_5105_;
goto v_resetjp_5099_;
}
else
{
lean_inc(v_a_5098_);
lean_dec(v___x_5093_);
v___x_5100_ = lean_box(0);
v_isShared_5101_ = v_isSharedCheck_5105_;
goto v_resetjp_5099_;
}
v_resetjp_5099_:
{
lean_object* v___x_5103_; 
if (v_isShared_5101_ == 0)
{
v___x_5103_ = v___x_5100_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v_a_5098_);
v___x_5103_ = v_reuseFailAlloc_5104_;
goto v_reusejp_5102_;
}
v_reusejp_5102_:
{
return v___x_5103_;
}
}
}
}
else
{
lean_object* v___x_5106_; 
v___x_5106_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5089_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_);
if (lean_obj_tag(v___x_5106_) == 0)
{
lean_object* v_a_5107_; uint8_t v___x_5108_; 
v_a_5107_ = lean_ctor_get(v___x_5106_, 0);
lean_inc(v_a_5107_);
lean_dec_ref_known(v___x_5106_, 1);
v___x_5108_ = lean_unbox(v_a_5107_);
lean_dec(v_a_5107_);
if (v___x_5108_ == 0)
{
lean_object* v___x_5109_; 
v___x_5109_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_5071_, v_b_5072_, v_val_5089_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_);
lean_dec(v_val_5089_);
return v___x_5109_;
}
else
{
lean_object* v___x_5110_; 
v___x_5110_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_5071_, v_b_5072_, v_val_5089_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_);
lean_dec(v_val_5089_);
return v___x_5110_;
}
}
else
{
lean_object* v_a_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5118_; 
lean_dec(v_val_5089_);
lean_dec_ref(v_b_5072_);
lean_dec_ref(v_a_5071_);
v_a_5111_ = lean_ctor_get(v___x_5106_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v___x_5106_);
if (v_isSharedCheck_5118_ == 0)
{
v___x_5113_ = v___x_5106_;
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_a_5111_);
lean_dec(v___x_5106_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5116_; 
if (v_isShared_5114_ == 0)
{
v___x_5116_ = v___x_5113_;
goto v_reusejp_5115_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v_a_5111_);
v___x_5116_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5115_;
}
v_reusejp_5115_:
{
return v___x_5116_;
}
}
}
}
}
else
{
lean_object* v_a_5119_; lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5126_; 
lean_dec(v_val_5089_);
lean_dec_ref(v_b_5072_);
lean_dec_ref(v_a_5071_);
v_a_5119_ = lean_ctor_get(v___x_5090_, 0);
v_isSharedCheck_5126_ = !lean_is_exclusive(v___x_5090_);
if (v_isSharedCheck_5126_ == 0)
{
v___x_5121_ = v___x_5090_;
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
else
{
lean_inc(v_a_5119_);
lean_dec(v___x_5090_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v___x_5124_; 
if (v_isShared_5122_ == 0)
{
v___x_5124_ = v___x_5121_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5125_; 
v_reuseFailAlloc_5125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5125_, 0, v_a_5119_);
v___x_5124_ = v_reuseFailAlloc_5125_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
return v___x_5124_;
}
}
}
}
else
{
lean_object* v___x_5127_; 
lean_dec(v_a_5088_);
v___x_5127_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5071_, v_b_5072_, v_a_5073_, v_a_5081_);
if (lean_obj_tag(v___x_5127_) == 0)
{
lean_object* v_a_5128_; lean_object* v___x_5130_; uint8_t v_isShared_5131_; uint8_t v_isSharedCheck_5150_; 
v_a_5128_ = lean_ctor_get(v___x_5127_, 0);
v_isSharedCheck_5150_ = !lean_is_exclusive(v___x_5127_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_5130_ = v___x_5127_;
v_isShared_5131_ = v_isSharedCheck_5150_;
goto v_resetjp_5129_;
}
else
{
lean_inc(v_a_5128_);
lean_dec(v___x_5127_);
v___x_5130_ = lean_box(0);
v_isShared_5131_ = v_isSharedCheck_5150_;
goto v_resetjp_5129_;
}
v_resetjp_5129_:
{
if (lean_obj_tag(v_a_5128_) == 1)
{
lean_object* v_val_5132_; lean_object* v___x_5133_; 
lean_del_object(v___x_5130_);
v_val_5132_ = lean_ctor_get(v_a_5128_, 0);
lean_inc(v_val_5132_);
lean_dec_ref_known(v_a_5128_, 1);
v___x_5133_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_5132_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_);
if (lean_obj_tag(v___x_5133_) == 0)
{
lean_object* v_a_5134_; lean_object* v_orderedAddInst_x3f_5135_; 
v_a_5134_ = lean_ctor_get(v___x_5133_, 0);
lean_inc(v_a_5134_);
lean_dec_ref_known(v___x_5133_, 1);
v_orderedAddInst_x3f_5135_ = lean_ctor_get(v_a_5134_, 9);
lean_inc(v_orderedAddInst_x3f_5135_);
lean_dec(v_a_5134_);
if (lean_obj_tag(v_orderedAddInst_x3f_5135_) == 0)
{
lean_object* v___x_5136_; 
v___x_5136_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5071_, v_b_5072_, v_val_5132_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_);
lean_dec(v_val_5132_);
return v___x_5136_;
}
else
{
lean_object* v___x_5137_; 
lean_dec_ref_known(v_orderedAddInst_x3f_5135_, 1);
v___x_5137_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5071_, v_b_5072_, v_val_5132_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_);
lean_dec(v_val_5132_);
return v___x_5137_;
}
}
else
{
lean_object* v_a_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5145_; 
lean_dec(v_val_5132_);
lean_dec_ref(v_b_5072_);
lean_dec_ref(v_a_5071_);
v_a_5138_ = lean_ctor_get(v___x_5133_, 0);
v_isSharedCheck_5145_ = !lean_is_exclusive(v___x_5133_);
if (v_isSharedCheck_5145_ == 0)
{
v___x_5140_ = v___x_5133_;
v_isShared_5141_ = v_isSharedCheck_5145_;
goto v_resetjp_5139_;
}
else
{
lean_inc(v_a_5138_);
lean_dec(v___x_5133_);
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
lean_dec(v_a_5128_);
lean_dec_ref(v_b_5072_);
lean_dec_ref(v_a_5071_);
v___x_5146_ = lean_box(0);
if (v_isShared_5131_ == 0)
{
lean_ctor_set(v___x_5130_, 0, v___x_5146_);
v___x_5148_ = v___x_5130_;
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
lean_dec_ref(v_b_5072_);
lean_dec_ref(v_a_5071_);
v_a_5151_ = lean_ctor_get(v___x_5127_, 0);
v_isSharedCheck_5158_ = !lean_is_exclusive(v___x_5127_);
if (v_isSharedCheck_5158_ == 0)
{
v___x_5153_ = v___x_5127_;
v_isShared_5154_ = v_isSharedCheck_5158_;
goto v_resetjp_5152_;
}
else
{
lean_inc(v_a_5151_);
lean_dec(v___x_5127_);
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
}
else
{
lean_object* v_a_5159_; lean_object* v___x_5161_; uint8_t v_isShared_5162_; uint8_t v_isSharedCheck_5166_; 
lean_dec_ref(v_b_5072_);
lean_dec_ref(v_a_5071_);
v_a_5159_ = lean_ctor_get(v___x_5087_, 0);
v_isSharedCheck_5166_ = !lean_is_exclusive(v___x_5087_);
if (v_isSharedCheck_5166_ == 0)
{
v___x_5161_ = v___x_5087_;
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
else
{
lean_inc(v_a_5159_);
lean_dec(v___x_5087_);
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
else
{
lean_object* v___x_5167_; lean_object* v___x_5168_; 
lean_dec_ref(v_b_5072_);
lean_dec_ref(v_a_5071_);
v___x_5167_ = lean_box(0);
v___x_5168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5168_, 0, v___x_5167_);
return v___x_5168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed(lean_object* v_a_5169_, lean_object* v_b_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_, lean_object* v_a_5181_){
_start:
{
lean_object* v_res_5182_; 
v_res_5182_ = l_Lean_Meta_Grind_Arith_Linear_processNewEq(v_a_5169_, v_b_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_, v_a_5175_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_, v_a_5180_);
lean_dec(v_a_5180_);
lean_dec_ref(v_a_5179_);
lean_dec(v_a_5178_);
lean_dec_ref(v_a_5177_);
lean_dec(v_a_5176_);
lean_dec_ref(v_a_5175_);
lean_dec(v_a_5174_);
lean_dec_ref(v_a_5173_);
lean_dec(v_a_5172_);
lean_dec(v_a_5171_);
return v_res_5182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object* v_a_5183_, lean_object* v_b_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_){
_start:
{
uint8_t v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; 
v___x_5197_ = 0;
v___x_5198_ = lean_box(v___x_5197_);
lean_inc_ref(v_a_5183_);
v___x_5199_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 2);
lean_closure_set(v___x_5199_, 0, v_a_5183_);
lean_closure_set(v___x_5199_, 1, v___x_5198_);
v___x_5200_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5199_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_);
if (lean_obj_tag(v___x_5200_) == 0)
{
lean_object* v_a_5201_; lean_object* v___x_5203_; uint8_t v_isShared_5204_; uint8_t v_isSharedCheck_5302_; 
v_a_5201_ = lean_ctor_get(v___x_5200_, 0);
v_isSharedCheck_5302_ = !lean_is_exclusive(v___x_5200_);
if (v_isSharedCheck_5302_ == 0)
{
v___x_5203_ = v___x_5200_;
v_isShared_5204_ = v_isSharedCheck_5302_;
goto v_resetjp_5202_;
}
else
{
lean_inc(v_a_5201_);
lean_dec(v___x_5200_);
v___x_5203_ = lean_box(0);
v_isShared_5204_ = v_isSharedCheck_5302_;
goto v_resetjp_5202_;
}
v_resetjp_5202_:
{
if (lean_obj_tag(v_a_5201_) == 1)
{
lean_object* v_val_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; 
lean_del_object(v___x_5203_);
v_val_5205_ = lean_ctor_get(v_a_5201_, 0);
lean_inc(v_val_5205_);
lean_dec_ref_known(v_a_5201_, 1);
v___x_5206_ = lean_box(v___x_5197_);
lean_inc_ref(v_b_5184_);
v___x_5207_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 14, 2);
lean_closure_set(v___x_5207_, 0, v_b_5184_);
lean_closure_set(v___x_5207_, 1, v___x_5206_);
v___x_5208_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5207_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_);
if (lean_obj_tag(v___x_5208_) == 0)
{
lean_object* v_a_5209_; lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5289_; 
v_a_5209_ = lean_ctor_get(v___x_5208_, 0);
v_isSharedCheck_5289_ = !lean_is_exclusive(v___x_5208_);
if (v_isSharedCheck_5289_ == 0)
{
v___x_5211_ = v___x_5208_;
v_isShared_5212_ = v_isSharedCheck_5289_;
goto v_resetjp_5210_;
}
else
{
lean_inc(v_a_5209_);
lean_dec(v___x_5208_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5289_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
if (lean_obj_tag(v_a_5209_) == 1)
{
lean_object* v_val_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; 
lean_del_object(v___x_5211_);
v_val_5213_ = lean_ctor_get(v_a_5209_, 0);
lean_inc_n(v_val_5213_, 2);
lean_dec_ref_known(v_a_5209_, 1);
lean_inc(v_val_5205_);
v___x_5214_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_5214_, 0, v_val_5205_);
lean_ctor_set(v___x_5214_, 1, v_val_5213_);
v___x_5215_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_5214_);
lean_inc_ref(v_b_5184_);
lean_inc_ref(v_a_5183_);
v___x_5216_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5216_, 0, v_a_5183_);
lean_ctor_set(v___x_5216_, 1, v_b_5184_);
lean_ctor_set(v___x_5216_, 2, v_val_5205_);
lean_ctor_set(v___x_5216_, 3, v_val_5213_);
v___x_5217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5217_, 0, v___x_5215_);
lean_ctor_set(v___x_5217_, 1, v___x_5216_);
v___x_5218_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(v___x_5217_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_);
if (lean_obj_tag(v___x_5218_) == 0)
{
lean_object* v_a_5219_; lean_object* v_p_5220_; lean_object* v___x_5221_; 
v_a_5219_ = lean_ctor_get(v___x_5218_, 0);
lean_inc(v_a_5219_);
lean_dec_ref_known(v___x_5218_, 1);
v_p_5220_ = lean_ctor_get(v_a_5219_, 0);
v___x_5221_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5183_, v_a_5186_);
lean_dec_ref(v_a_5183_);
if (lean_obj_tag(v___x_5221_) == 0)
{
lean_object* v_a_5222_; lean_object* v___x_5223_; 
v_a_5222_ = lean_ctor_get(v___x_5221_, 0);
lean_inc(v_a_5222_);
lean_dec_ref_known(v___x_5221_, 1);
v___x_5223_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5184_, v_a_5186_);
lean_dec_ref(v_b_5184_);
if (lean_obj_tag(v___x_5223_) == 0)
{
lean_object* v_a_5224_; lean_object* v___y_5226_; uint8_t v___x_5260_; 
v_a_5224_ = lean_ctor_get(v___x_5223_, 0);
lean_inc(v_a_5224_);
lean_dec_ref_known(v___x_5223_, 1);
v___x_5260_ = lean_nat_dec_le(v_a_5222_, v_a_5224_);
if (v___x_5260_ == 0)
{
lean_dec(v_a_5224_);
v___y_5226_ = v_a_5222_;
goto v___jp_5225_;
}
else
{
lean_dec(v_a_5222_);
v___y_5226_ = v_a_5224_;
goto v___jp_5225_;
}
v___jp_5225_:
{
lean_object* v___x_5227_; 
lean_inc_ref(v_p_5220_);
v___x_5227_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_5220_, v___y_5226_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_);
if (lean_obj_tag(v___x_5227_) == 0)
{
lean_object* v_a_5228_; lean_object* v___x_5229_; 
v_a_5228_ = lean_ctor_get(v___x_5227_, 0);
lean_inc(v_a_5228_);
lean_dec_ref_known(v___x_5227_, 1);
v___x_5229_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5228_, v___x_5197_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_);
if (lean_obj_tag(v___x_5229_) == 0)
{
lean_object* v_a_5230_; lean_object* v___x_5232_; uint8_t v_isShared_5233_; uint8_t v_isSharedCheck_5243_; 
v_a_5230_ = lean_ctor_get(v___x_5229_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___x_5229_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5232_ = v___x_5229_;
v_isShared_5233_ = v_isSharedCheck_5243_;
goto v_resetjp_5231_;
}
else
{
lean_inc(v_a_5230_);
lean_dec(v___x_5229_);
v___x_5232_ = lean_box(0);
v_isShared_5233_ = v_isSharedCheck_5243_;
goto v_resetjp_5231_;
}
v_resetjp_5231_:
{
if (lean_obj_tag(v_a_5230_) == 1)
{
lean_object* v_val_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; 
lean_del_object(v___x_5232_);
v_val_5234_ = lean_ctor_get(v_a_5230_, 0);
lean_inc_n(v_val_5234_, 2);
lean_dec_ref_known(v_a_5230_, 1);
v___x_5235_ = l_Lean_Grind_Linarith_Expr_norm(v_val_5234_);
v___x_5236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5236_, 0, v_a_5219_);
lean_ctor_set(v___x_5236_, 1, v_val_5234_);
v___x_5237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5237_, 0, v___x_5235_);
lean_ctor_set(v___x_5237_, 1, v___x_5236_);
v___x_5238_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5237_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_);
return v___x_5238_;
}
else
{
lean_object* v___x_5239_; lean_object* v___x_5241_; 
lean_dec(v_a_5230_);
lean_dec(v_a_5219_);
v___x_5239_ = lean_box(0);
if (v_isShared_5233_ == 0)
{
lean_ctor_set(v___x_5232_, 0, v___x_5239_);
v___x_5241_ = v___x_5232_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v___x_5239_);
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
else
{
lean_object* v_a_5244_; lean_object* v___x_5246_; uint8_t v_isShared_5247_; uint8_t v_isSharedCheck_5251_; 
lean_dec(v_a_5219_);
v_a_5244_ = lean_ctor_get(v___x_5229_, 0);
v_isSharedCheck_5251_ = !lean_is_exclusive(v___x_5229_);
if (v_isSharedCheck_5251_ == 0)
{
v___x_5246_ = v___x_5229_;
v_isShared_5247_ = v_isSharedCheck_5251_;
goto v_resetjp_5245_;
}
else
{
lean_inc(v_a_5244_);
lean_dec(v___x_5229_);
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
lean_object* v_a_5252_; lean_object* v___x_5254_; uint8_t v_isShared_5255_; uint8_t v_isSharedCheck_5259_; 
lean_dec(v_a_5219_);
v_a_5252_ = lean_ctor_get(v___x_5227_, 0);
v_isSharedCheck_5259_ = !lean_is_exclusive(v___x_5227_);
if (v_isSharedCheck_5259_ == 0)
{
v___x_5254_ = v___x_5227_;
v_isShared_5255_ = v_isSharedCheck_5259_;
goto v_resetjp_5253_;
}
else
{
lean_inc(v_a_5252_);
lean_dec(v___x_5227_);
v___x_5254_ = lean_box(0);
v_isShared_5255_ = v_isSharedCheck_5259_;
goto v_resetjp_5253_;
}
v_resetjp_5253_:
{
lean_object* v___x_5257_; 
if (v_isShared_5255_ == 0)
{
v___x_5257_ = v___x_5254_;
goto v_reusejp_5256_;
}
else
{
lean_object* v_reuseFailAlloc_5258_; 
v_reuseFailAlloc_5258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5258_, 0, v_a_5252_);
v___x_5257_ = v_reuseFailAlloc_5258_;
goto v_reusejp_5256_;
}
v_reusejp_5256_:
{
return v___x_5257_;
}
}
}
}
}
else
{
lean_object* v_a_5261_; lean_object* v___x_5263_; uint8_t v_isShared_5264_; uint8_t v_isSharedCheck_5268_; 
lean_dec(v_a_5222_);
lean_dec(v_a_5219_);
v_a_5261_ = lean_ctor_get(v___x_5223_, 0);
v_isSharedCheck_5268_ = !lean_is_exclusive(v___x_5223_);
if (v_isSharedCheck_5268_ == 0)
{
v___x_5263_ = v___x_5223_;
v_isShared_5264_ = v_isSharedCheck_5268_;
goto v_resetjp_5262_;
}
else
{
lean_inc(v_a_5261_);
lean_dec(v___x_5223_);
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
lean_object* v_a_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5276_; 
lean_dec(v_a_5219_);
lean_dec_ref(v_b_5184_);
v_a_5269_ = lean_ctor_get(v___x_5221_, 0);
v_isSharedCheck_5276_ = !lean_is_exclusive(v___x_5221_);
if (v_isSharedCheck_5276_ == 0)
{
v___x_5271_ = v___x_5221_;
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_a_5269_);
lean_dec(v___x_5221_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5274_; 
if (v_isShared_5272_ == 0)
{
v___x_5274_ = v___x_5271_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v_a_5269_);
v___x_5274_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
return v___x_5274_;
}
}
}
}
else
{
lean_object* v_a_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5284_; 
lean_dec_ref(v_b_5184_);
lean_dec_ref(v_a_5183_);
v_a_5277_ = lean_ctor_get(v___x_5218_, 0);
v_isSharedCheck_5284_ = !lean_is_exclusive(v___x_5218_);
if (v_isSharedCheck_5284_ == 0)
{
v___x_5279_ = v___x_5218_;
v_isShared_5280_ = v_isSharedCheck_5284_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_a_5277_);
lean_dec(v___x_5218_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5284_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v___x_5282_; 
if (v_isShared_5280_ == 0)
{
v___x_5282_ = v___x_5279_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v_a_5277_);
v___x_5282_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
return v___x_5282_;
}
}
}
}
else
{
lean_object* v___x_5285_; lean_object* v___x_5287_; 
lean_dec(v_a_5209_);
lean_dec(v_val_5205_);
lean_dec_ref(v_b_5184_);
lean_dec_ref(v_a_5183_);
v___x_5285_ = lean_box(0);
if (v_isShared_5212_ == 0)
{
lean_ctor_set(v___x_5211_, 0, v___x_5285_);
v___x_5287_ = v___x_5211_;
goto v_reusejp_5286_;
}
else
{
lean_object* v_reuseFailAlloc_5288_; 
v_reuseFailAlloc_5288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5288_, 0, v___x_5285_);
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
lean_object* v_a_5290_; lean_object* v___x_5292_; uint8_t v_isShared_5293_; uint8_t v_isSharedCheck_5297_; 
lean_dec(v_val_5205_);
lean_dec_ref(v_b_5184_);
lean_dec_ref(v_a_5183_);
v_a_5290_ = lean_ctor_get(v___x_5208_, 0);
v_isSharedCheck_5297_ = !lean_is_exclusive(v___x_5208_);
if (v_isSharedCheck_5297_ == 0)
{
v___x_5292_ = v___x_5208_;
v_isShared_5293_ = v_isSharedCheck_5297_;
goto v_resetjp_5291_;
}
else
{
lean_inc(v_a_5290_);
lean_dec(v___x_5208_);
v___x_5292_ = lean_box(0);
v_isShared_5293_ = v_isSharedCheck_5297_;
goto v_resetjp_5291_;
}
v_resetjp_5291_:
{
lean_object* v___x_5295_; 
if (v_isShared_5293_ == 0)
{
v___x_5295_ = v___x_5292_;
goto v_reusejp_5294_;
}
else
{
lean_object* v_reuseFailAlloc_5296_; 
v_reuseFailAlloc_5296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5296_, 0, v_a_5290_);
v___x_5295_ = v_reuseFailAlloc_5296_;
goto v_reusejp_5294_;
}
v_reusejp_5294_:
{
return v___x_5295_;
}
}
}
}
else
{
lean_object* v___x_5298_; lean_object* v___x_5300_; 
lean_dec(v_a_5201_);
lean_dec_ref(v_b_5184_);
lean_dec_ref(v_a_5183_);
v___x_5298_ = lean_box(0);
if (v_isShared_5204_ == 0)
{
lean_ctor_set(v___x_5203_, 0, v___x_5298_);
v___x_5300_ = v___x_5203_;
goto v_reusejp_5299_;
}
else
{
lean_object* v_reuseFailAlloc_5301_; 
v_reuseFailAlloc_5301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5301_, 0, v___x_5298_);
v___x_5300_ = v_reuseFailAlloc_5301_;
goto v_reusejp_5299_;
}
v_reusejp_5299_:
{
return v___x_5300_;
}
}
}
}
else
{
lean_object* v_a_5303_; lean_object* v___x_5305_; uint8_t v_isShared_5306_; uint8_t v_isSharedCheck_5310_; 
lean_dec_ref(v_b_5184_);
lean_dec_ref(v_a_5183_);
v_a_5303_ = lean_ctor_get(v___x_5200_, 0);
v_isSharedCheck_5310_ = !lean_is_exclusive(v___x_5200_);
if (v_isSharedCheck_5310_ == 0)
{
v___x_5305_ = v___x_5200_;
v_isShared_5306_ = v_isSharedCheck_5310_;
goto v_resetjp_5304_;
}
else
{
lean_inc(v_a_5303_);
lean_dec(v___x_5200_);
v___x_5305_ = lean_box(0);
v_isShared_5306_ = v_isSharedCheck_5310_;
goto v_resetjp_5304_;
}
v_resetjp_5304_:
{
lean_object* v___x_5308_; 
if (v_isShared_5306_ == 0)
{
v___x_5308_ = v___x_5305_;
goto v_reusejp_5307_;
}
else
{
lean_object* v_reuseFailAlloc_5309_; 
v_reuseFailAlloc_5309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5309_, 0, v_a_5303_);
v___x_5308_ = v_reuseFailAlloc_5309_;
goto v_reusejp_5307_;
}
v_reusejp_5307_:
{
return v___x_5308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq___boxed(lean_object* v_a_5311_, lean_object* v_b_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_, lean_object* v_a_5324_){
_start:
{
lean_object* v_res_5325_; 
v_res_5325_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5311_, v_b_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_);
lean_dec(v_a_5323_);
lean_dec_ref(v_a_5322_);
lean_dec(v_a_5321_);
lean_dec_ref(v_a_5320_);
lean_dec(v_a_5319_);
lean_dec_ref(v_a_5318_);
lean_dec(v_a_5317_);
lean_dec_ref(v_a_5316_);
lean_dec(v_a_5315_);
lean_dec(v_a_5314_);
lean_dec(v_a_5313_);
return v_res_5325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(lean_object* v_a_5326_, lean_object* v_b_5327_, lean_object* v_a_5328_, lean_object* v_a_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_, lean_object* v_a_5336_, lean_object* v_a_5337_, lean_object* v_a_5338_){
_start:
{
uint8_t v___x_5340_; lean_object* v___x_5341_; 
v___x_5340_ = 0;
lean_inc_ref(v_a_5326_);
v___x_5341_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5326_, v___x_5340_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_, v_a_5337_, v_a_5338_);
if (lean_obj_tag(v___x_5341_) == 0)
{
lean_object* v_a_5342_; lean_object* v___x_5344_; uint8_t v_isShared_5345_; uint8_t v_isSharedCheck_5375_; 
v_a_5342_ = lean_ctor_get(v___x_5341_, 0);
v_isSharedCheck_5375_ = !lean_is_exclusive(v___x_5341_);
if (v_isSharedCheck_5375_ == 0)
{
v___x_5344_ = v___x_5341_;
v_isShared_5345_ = v_isSharedCheck_5375_;
goto v_resetjp_5343_;
}
else
{
lean_inc(v_a_5342_);
lean_dec(v___x_5341_);
v___x_5344_ = lean_box(0);
v_isShared_5345_ = v_isSharedCheck_5375_;
goto v_resetjp_5343_;
}
v_resetjp_5343_:
{
if (lean_obj_tag(v_a_5342_) == 1)
{
lean_object* v_val_5346_; lean_object* v___x_5347_; 
lean_del_object(v___x_5344_);
v_val_5346_ = lean_ctor_get(v_a_5342_, 0);
lean_inc(v_val_5346_);
lean_dec_ref_known(v_a_5342_, 1);
lean_inc_ref(v_b_5327_);
v___x_5347_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_5327_, v___x_5340_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_, v_a_5337_, v_a_5338_);
if (lean_obj_tag(v___x_5347_) == 0)
{
lean_object* v_a_5348_; lean_object* v___x_5350_; uint8_t v_isShared_5351_; uint8_t v_isSharedCheck_5362_; 
v_a_5348_ = lean_ctor_get(v___x_5347_, 0);
v_isSharedCheck_5362_ = !lean_is_exclusive(v___x_5347_);
if (v_isSharedCheck_5362_ == 0)
{
v___x_5350_ = v___x_5347_;
v_isShared_5351_ = v_isSharedCheck_5362_;
goto v_resetjp_5349_;
}
else
{
lean_inc(v_a_5348_);
lean_dec(v___x_5347_);
v___x_5350_ = lean_box(0);
v_isShared_5351_ = v_isSharedCheck_5362_;
goto v_resetjp_5349_;
}
v_resetjp_5349_:
{
if (lean_obj_tag(v_a_5348_) == 1)
{
lean_object* v_val_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; 
lean_del_object(v___x_5350_);
v_val_5352_ = lean_ctor_get(v_a_5348_, 0);
lean_inc_n(v_val_5352_, 2);
lean_dec_ref_known(v_a_5348_, 1);
lean_inc(v_val_5346_);
v___x_5353_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5353_, 0, v_val_5346_);
lean_ctor_set(v___x_5353_, 1, v_val_5352_);
v___x_5354_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5353_);
v___x_5355_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5355_, 0, v_a_5326_);
lean_ctor_set(v___x_5355_, 1, v_b_5327_);
lean_ctor_set(v___x_5355_, 2, v_val_5346_);
lean_ctor_set(v___x_5355_, 3, v_val_5352_);
v___x_5356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5356_, 0, v___x_5354_);
lean_ctor_set(v___x_5356_, 1, v___x_5355_);
v___x_5357_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5356_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_, v_a_5337_, v_a_5338_);
return v___x_5357_;
}
else
{
lean_object* v___x_5358_; lean_object* v___x_5360_; 
lean_dec(v_a_5348_);
lean_dec(v_val_5346_);
lean_dec_ref(v_b_5327_);
lean_dec_ref(v_a_5326_);
v___x_5358_ = lean_box(0);
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 0, v___x_5358_);
v___x_5360_ = v___x_5350_;
goto v_reusejp_5359_;
}
else
{
lean_object* v_reuseFailAlloc_5361_; 
v_reuseFailAlloc_5361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5361_, 0, v___x_5358_);
v___x_5360_ = v_reuseFailAlloc_5361_;
goto v_reusejp_5359_;
}
v_reusejp_5359_:
{
return v___x_5360_;
}
}
}
}
else
{
lean_object* v_a_5363_; lean_object* v___x_5365_; uint8_t v_isShared_5366_; uint8_t v_isSharedCheck_5370_; 
lean_dec(v_val_5346_);
lean_dec_ref(v_b_5327_);
lean_dec_ref(v_a_5326_);
v_a_5363_ = lean_ctor_get(v___x_5347_, 0);
v_isSharedCheck_5370_ = !lean_is_exclusive(v___x_5347_);
if (v_isSharedCheck_5370_ == 0)
{
v___x_5365_ = v___x_5347_;
v_isShared_5366_ = v_isSharedCheck_5370_;
goto v_resetjp_5364_;
}
else
{
lean_inc(v_a_5363_);
lean_dec(v___x_5347_);
v___x_5365_ = lean_box(0);
v_isShared_5366_ = v_isSharedCheck_5370_;
goto v_resetjp_5364_;
}
v_resetjp_5364_:
{
lean_object* v___x_5368_; 
if (v_isShared_5366_ == 0)
{
v___x_5368_ = v___x_5365_;
goto v_reusejp_5367_;
}
else
{
lean_object* v_reuseFailAlloc_5369_; 
v_reuseFailAlloc_5369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5369_, 0, v_a_5363_);
v___x_5368_ = v_reuseFailAlloc_5369_;
goto v_reusejp_5367_;
}
v_reusejp_5367_:
{
return v___x_5368_;
}
}
}
}
else
{
lean_object* v___x_5371_; lean_object* v___x_5373_; 
lean_dec(v_a_5342_);
lean_dec_ref(v_b_5327_);
lean_dec_ref(v_a_5326_);
v___x_5371_ = lean_box(0);
if (v_isShared_5345_ == 0)
{
lean_ctor_set(v___x_5344_, 0, v___x_5371_);
v___x_5373_ = v___x_5344_;
goto v_reusejp_5372_;
}
else
{
lean_object* v_reuseFailAlloc_5374_; 
v_reuseFailAlloc_5374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5374_, 0, v___x_5371_);
v___x_5373_ = v_reuseFailAlloc_5374_;
goto v_reusejp_5372_;
}
v_reusejp_5372_:
{
return v___x_5373_;
}
}
}
}
else
{
lean_object* v_a_5376_; lean_object* v___x_5378_; uint8_t v_isShared_5379_; uint8_t v_isSharedCheck_5383_; 
lean_dec_ref(v_b_5327_);
lean_dec_ref(v_a_5326_);
v_a_5376_ = lean_ctor_get(v___x_5341_, 0);
v_isSharedCheck_5383_ = !lean_is_exclusive(v___x_5341_);
if (v_isSharedCheck_5383_ == 0)
{
v___x_5378_ = v___x_5341_;
v_isShared_5379_ = v_isSharedCheck_5383_;
goto v_resetjp_5377_;
}
else
{
lean_inc(v_a_5376_);
lean_dec(v___x_5341_);
v___x_5378_ = lean_box(0);
v_isShared_5379_ = v_isSharedCheck_5383_;
goto v_resetjp_5377_;
}
v_resetjp_5377_:
{
lean_object* v___x_5381_; 
if (v_isShared_5379_ == 0)
{
v___x_5381_ = v___x_5378_;
goto v_reusejp_5380_;
}
else
{
lean_object* v_reuseFailAlloc_5382_; 
v_reuseFailAlloc_5382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5382_, 0, v_a_5376_);
v___x_5381_ = v_reuseFailAlloc_5382_;
goto v_reusejp_5380_;
}
v_reusejp_5380_:
{
return v___x_5381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq___boxed(lean_object* v_a_5384_, lean_object* v_b_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_, lean_object* v_a_5388_, lean_object* v_a_5389_, lean_object* v_a_5390_, lean_object* v_a_5391_, lean_object* v_a_5392_, lean_object* v_a_5393_, lean_object* v_a_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_){
_start:
{
lean_object* v_res_5398_; 
v_res_5398_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5384_, v_b_5385_, v_a_5386_, v_a_5387_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_, v_a_5392_, v_a_5393_, v_a_5394_, v_a_5395_, v_a_5396_);
lean_dec(v_a_5396_);
lean_dec_ref(v_a_5395_);
lean_dec(v_a_5394_);
lean_dec_ref(v_a_5393_);
lean_dec(v_a_5392_);
lean_dec_ref(v_a_5391_);
lean_dec(v_a_5390_);
lean_dec_ref(v_a_5389_);
lean_dec(v_a_5388_);
lean_dec(v_a_5387_);
lean_dec(v_a_5386_);
return v_res_5398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(lean_object* v_a_5399_, lean_object* v_b_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_){
_start:
{
lean_object* v___x_5413_; 
v___x_5413_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_);
if (lean_obj_tag(v___x_5413_) == 0)
{
lean_object* v_a_5414_; lean_object* v_addRightCancelInst_x3f_5415_; 
v_a_5414_ = lean_ctor_get(v___x_5413_, 0);
lean_inc(v_a_5414_);
lean_dec_ref_known(v___x_5413_, 1);
v_addRightCancelInst_x3f_5415_ = lean_ctor_get(v_a_5414_, 11);
if (lean_obj_tag(v_addRightCancelInst_x3f_5415_) == 0)
{
lean_object* v___x_5416_; 
lean_dec(v_a_5414_);
v___x_5416_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(v_a_5399_, v_b_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_);
return v___x_5416_;
}
else
{
lean_object* v_id_5417_; lean_object* v_structId_5418_; lean_object* v___x_5419_; 
v_id_5417_ = lean_ctor_get(v_a_5414_, 0);
lean_inc(v_id_5417_);
v_structId_5418_ = lean_ctor_get(v_a_5414_, 1);
lean_inc(v_structId_5418_);
lean_dec(v_a_5414_);
lean_inc_ref(v_a_5399_);
v___x_5419_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5399_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_);
if (lean_obj_tag(v___x_5419_) == 0)
{
lean_object* v_a_5420_; lean_object* v_fst_5421_; lean_object* v___x_5423_; uint8_t v_isShared_5424_; uint8_t v_isSharedCheck_5489_; 
v_a_5420_ = lean_ctor_get(v___x_5419_, 0);
lean_inc(v_a_5420_);
lean_dec_ref_known(v___x_5419_, 1);
v_fst_5421_ = lean_ctor_get(v_a_5420_, 0);
v_isSharedCheck_5489_ = !lean_is_exclusive(v_a_5420_);
if (v_isSharedCheck_5489_ == 0)
{
lean_object* v_unused_5490_; 
v_unused_5490_ = lean_ctor_get(v_a_5420_, 1);
lean_dec(v_unused_5490_);
v___x_5423_ = v_a_5420_;
v_isShared_5424_ = v_isSharedCheck_5489_;
goto v_resetjp_5422_;
}
else
{
lean_inc(v_fst_5421_);
lean_dec(v_a_5420_);
v___x_5423_ = lean_box(0);
v_isShared_5424_ = v_isSharedCheck_5489_;
goto v_resetjp_5422_;
}
v_resetjp_5422_:
{
lean_object* v___x_5425_; 
lean_inc_ref(v_b_5400_);
v___x_5425_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_);
if (lean_obj_tag(v___x_5425_) == 0)
{
lean_object* v_a_5426_; lean_object* v_fst_5427_; lean_object* v___x_5429_; uint8_t v_isShared_5430_; uint8_t v_isSharedCheck_5479_; 
v_a_5426_ = lean_ctor_get(v___x_5425_, 0);
lean_inc(v_a_5426_);
lean_dec_ref_known(v___x_5425_, 1);
v_fst_5427_ = lean_ctor_get(v_a_5426_, 0);
v_isSharedCheck_5479_ = !lean_is_exclusive(v_a_5426_);
if (v_isSharedCheck_5479_ == 0)
{
lean_object* v_unused_5480_; 
v_unused_5480_ = lean_ctor_get(v_a_5426_, 1);
lean_dec(v_unused_5480_);
v___x_5429_ = v_a_5426_;
v_isShared_5430_ = v_isSharedCheck_5479_;
goto v_resetjp_5428_;
}
else
{
lean_inc(v_fst_5427_);
lean_dec(v_a_5426_);
v___x_5429_ = lean_box(0);
v_isShared_5430_ = v_isSharedCheck_5479_;
goto v_resetjp_5428_;
}
v_resetjp_5428_:
{
uint8_t v___x_5431_; lean_object* v___x_5432_; 
v___x_5431_ = 0;
v___x_5432_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5421_, v___x_5431_, v_structId_5418_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_);
if (lean_obj_tag(v___x_5432_) == 0)
{
lean_object* v_a_5433_; lean_object* v___x_5435_; uint8_t v_isShared_5436_; uint8_t v_isSharedCheck_5470_; 
v_a_5433_ = lean_ctor_get(v___x_5432_, 0);
v_isSharedCheck_5470_ = !lean_is_exclusive(v___x_5432_);
if (v_isSharedCheck_5470_ == 0)
{
v___x_5435_ = v___x_5432_;
v_isShared_5436_ = v_isSharedCheck_5470_;
goto v_resetjp_5434_;
}
else
{
lean_inc(v_a_5433_);
lean_dec(v___x_5432_);
v___x_5435_ = lean_box(0);
v_isShared_5436_ = v_isSharedCheck_5470_;
goto v_resetjp_5434_;
}
v_resetjp_5434_:
{
if (lean_obj_tag(v_a_5433_) == 1)
{
lean_object* v_val_5437_; lean_object* v___x_5438_; 
lean_del_object(v___x_5435_);
v_val_5437_ = lean_ctor_get(v_a_5433_, 0);
lean_inc(v_val_5437_);
lean_dec_ref_known(v_a_5433_, 1);
v___x_5438_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5427_, v___x_5431_, v_structId_5418_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_);
if (lean_obj_tag(v___x_5438_) == 0)
{
lean_object* v_a_5439_; lean_object* v___x_5441_; uint8_t v_isShared_5442_; uint8_t v_isSharedCheck_5457_; 
v_a_5439_ = lean_ctor_get(v___x_5438_, 0);
v_isSharedCheck_5457_ = !lean_is_exclusive(v___x_5438_);
if (v_isSharedCheck_5457_ == 0)
{
v___x_5441_ = v___x_5438_;
v_isShared_5442_ = v_isSharedCheck_5457_;
goto v_resetjp_5440_;
}
else
{
lean_inc(v_a_5439_);
lean_dec(v___x_5438_);
v___x_5441_ = lean_box(0);
v_isShared_5442_ = v_isSharedCheck_5457_;
goto v_resetjp_5440_;
}
v_resetjp_5440_:
{
if (lean_obj_tag(v_a_5439_) == 1)
{
lean_object* v_val_5443_; lean_object* v___x_5445_; 
lean_del_object(v___x_5441_);
v_val_5443_ = lean_ctor_get(v_a_5439_, 0);
lean_inc_n(v_val_5443_, 2);
lean_dec_ref_known(v_a_5439_, 1);
lean_inc(v_val_5437_);
if (v_isShared_5430_ == 0)
{
lean_ctor_set_tag(v___x_5429_, 3);
lean_ctor_set(v___x_5429_, 1, v_val_5443_);
lean_ctor_set(v___x_5429_, 0, v_val_5437_);
v___x_5445_ = v___x_5429_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5452_; 
v_reuseFailAlloc_5452_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5452_, 0, v_val_5437_);
lean_ctor_set(v_reuseFailAlloc_5452_, 1, v_val_5443_);
v___x_5445_ = v_reuseFailAlloc_5452_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5449_; 
v___x_5446_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5445_);
v___x_5447_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5447_, 0, v_a_5399_);
lean_ctor_set(v___x_5447_, 1, v_b_5400_);
lean_ctor_set(v___x_5447_, 2, v_id_5417_);
lean_ctor_set(v___x_5447_, 3, v_val_5437_);
lean_ctor_set(v___x_5447_, 4, v_val_5443_);
if (v_isShared_5424_ == 0)
{
lean_ctor_set(v___x_5423_, 1, v___x_5447_);
lean_ctor_set(v___x_5423_, 0, v___x_5446_);
v___x_5449_ = v___x_5423_;
goto v_reusejp_5448_;
}
else
{
lean_object* v_reuseFailAlloc_5451_; 
v_reuseFailAlloc_5451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5451_, 0, v___x_5446_);
lean_ctor_set(v_reuseFailAlloc_5451_, 1, v___x_5447_);
v___x_5449_ = v_reuseFailAlloc_5451_;
goto v_reusejp_5448_;
}
v_reusejp_5448_:
{
lean_object* v___x_5450_; 
v___x_5450_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5449_, v_structId_5418_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_);
lean_dec(v_structId_5418_);
return v___x_5450_;
}
}
}
else
{
lean_object* v___x_5453_; lean_object* v___x_5455_; 
lean_dec(v_a_5439_);
lean_dec(v_val_5437_);
lean_del_object(v___x_5429_);
lean_del_object(v___x_5423_);
lean_dec(v_structId_5418_);
lean_dec(v_id_5417_);
lean_dec_ref(v_b_5400_);
lean_dec_ref(v_a_5399_);
v___x_5453_ = lean_box(0);
if (v_isShared_5442_ == 0)
{
lean_ctor_set(v___x_5441_, 0, v___x_5453_);
v___x_5455_ = v___x_5441_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5456_; 
v_reuseFailAlloc_5456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5456_, 0, v___x_5453_);
v___x_5455_ = v_reuseFailAlloc_5456_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
return v___x_5455_;
}
}
}
}
else
{
lean_object* v_a_5458_; lean_object* v___x_5460_; uint8_t v_isShared_5461_; uint8_t v_isSharedCheck_5465_; 
lean_dec(v_val_5437_);
lean_del_object(v___x_5429_);
lean_del_object(v___x_5423_);
lean_dec(v_structId_5418_);
lean_dec(v_id_5417_);
lean_dec_ref(v_b_5400_);
lean_dec_ref(v_a_5399_);
v_a_5458_ = lean_ctor_get(v___x_5438_, 0);
v_isSharedCheck_5465_ = !lean_is_exclusive(v___x_5438_);
if (v_isSharedCheck_5465_ == 0)
{
v___x_5460_ = v___x_5438_;
v_isShared_5461_ = v_isSharedCheck_5465_;
goto v_resetjp_5459_;
}
else
{
lean_inc(v_a_5458_);
lean_dec(v___x_5438_);
v___x_5460_ = lean_box(0);
v_isShared_5461_ = v_isSharedCheck_5465_;
goto v_resetjp_5459_;
}
v_resetjp_5459_:
{
lean_object* v___x_5463_; 
if (v_isShared_5461_ == 0)
{
v___x_5463_ = v___x_5460_;
goto v_reusejp_5462_;
}
else
{
lean_object* v_reuseFailAlloc_5464_; 
v_reuseFailAlloc_5464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5464_, 0, v_a_5458_);
v___x_5463_ = v_reuseFailAlloc_5464_;
goto v_reusejp_5462_;
}
v_reusejp_5462_:
{
return v___x_5463_;
}
}
}
}
else
{
lean_object* v___x_5466_; lean_object* v___x_5468_; 
lean_dec(v_a_5433_);
lean_del_object(v___x_5429_);
lean_dec(v_fst_5427_);
lean_del_object(v___x_5423_);
lean_dec(v_structId_5418_);
lean_dec(v_id_5417_);
lean_dec_ref(v_b_5400_);
lean_dec_ref(v_a_5399_);
v___x_5466_ = lean_box(0);
if (v_isShared_5436_ == 0)
{
lean_ctor_set(v___x_5435_, 0, v___x_5466_);
v___x_5468_ = v___x_5435_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5469_; 
v_reuseFailAlloc_5469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5469_, 0, v___x_5466_);
v___x_5468_ = v_reuseFailAlloc_5469_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
return v___x_5468_;
}
}
}
}
else
{
lean_object* v_a_5471_; lean_object* v___x_5473_; uint8_t v_isShared_5474_; uint8_t v_isSharedCheck_5478_; 
lean_del_object(v___x_5429_);
lean_dec(v_fst_5427_);
lean_del_object(v___x_5423_);
lean_dec(v_structId_5418_);
lean_dec(v_id_5417_);
lean_dec_ref(v_b_5400_);
lean_dec_ref(v_a_5399_);
v_a_5471_ = lean_ctor_get(v___x_5432_, 0);
v_isSharedCheck_5478_ = !lean_is_exclusive(v___x_5432_);
if (v_isSharedCheck_5478_ == 0)
{
v___x_5473_ = v___x_5432_;
v_isShared_5474_ = v_isSharedCheck_5478_;
goto v_resetjp_5472_;
}
else
{
lean_inc(v_a_5471_);
lean_dec(v___x_5432_);
v___x_5473_ = lean_box(0);
v_isShared_5474_ = v_isSharedCheck_5478_;
goto v_resetjp_5472_;
}
v_resetjp_5472_:
{
lean_object* v___x_5476_; 
if (v_isShared_5474_ == 0)
{
v___x_5476_ = v___x_5473_;
goto v_reusejp_5475_;
}
else
{
lean_object* v_reuseFailAlloc_5477_; 
v_reuseFailAlloc_5477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5477_, 0, v_a_5471_);
v___x_5476_ = v_reuseFailAlloc_5477_;
goto v_reusejp_5475_;
}
v_reusejp_5475_:
{
return v___x_5476_;
}
}
}
}
}
else
{
lean_object* v_a_5481_; lean_object* v___x_5483_; uint8_t v_isShared_5484_; uint8_t v_isSharedCheck_5488_; 
lean_del_object(v___x_5423_);
lean_dec(v_fst_5421_);
lean_dec(v_structId_5418_);
lean_dec(v_id_5417_);
lean_dec_ref(v_b_5400_);
lean_dec_ref(v_a_5399_);
v_a_5481_ = lean_ctor_get(v___x_5425_, 0);
v_isSharedCheck_5488_ = !lean_is_exclusive(v___x_5425_);
if (v_isSharedCheck_5488_ == 0)
{
v___x_5483_ = v___x_5425_;
v_isShared_5484_ = v_isSharedCheck_5488_;
goto v_resetjp_5482_;
}
else
{
lean_inc(v_a_5481_);
lean_dec(v___x_5425_);
v___x_5483_ = lean_box(0);
v_isShared_5484_ = v_isSharedCheck_5488_;
goto v_resetjp_5482_;
}
v_resetjp_5482_:
{
lean_object* v___x_5486_; 
if (v_isShared_5484_ == 0)
{
v___x_5486_ = v___x_5483_;
goto v_reusejp_5485_;
}
else
{
lean_object* v_reuseFailAlloc_5487_; 
v_reuseFailAlloc_5487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5487_, 0, v_a_5481_);
v___x_5486_ = v_reuseFailAlloc_5487_;
goto v_reusejp_5485_;
}
v_reusejp_5485_:
{
return v___x_5486_;
}
}
}
}
}
else
{
lean_object* v_a_5491_; lean_object* v___x_5493_; uint8_t v_isShared_5494_; uint8_t v_isSharedCheck_5498_; 
lean_dec(v_structId_5418_);
lean_dec(v_id_5417_);
lean_dec_ref(v_b_5400_);
lean_dec_ref(v_a_5399_);
v_a_5491_ = lean_ctor_get(v___x_5419_, 0);
v_isSharedCheck_5498_ = !lean_is_exclusive(v___x_5419_);
if (v_isSharedCheck_5498_ == 0)
{
v___x_5493_ = v___x_5419_;
v_isShared_5494_ = v_isSharedCheck_5498_;
goto v_resetjp_5492_;
}
else
{
lean_inc(v_a_5491_);
lean_dec(v___x_5419_);
v___x_5493_ = lean_box(0);
v_isShared_5494_ = v_isSharedCheck_5498_;
goto v_resetjp_5492_;
}
v_resetjp_5492_:
{
lean_object* v___x_5496_; 
if (v_isShared_5494_ == 0)
{
v___x_5496_ = v___x_5493_;
goto v_reusejp_5495_;
}
else
{
lean_object* v_reuseFailAlloc_5497_; 
v_reuseFailAlloc_5497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5497_, 0, v_a_5491_);
v___x_5496_ = v_reuseFailAlloc_5497_;
goto v_reusejp_5495_;
}
v_reusejp_5495_:
{
return v___x_5496_;
}
}
}
}
}
else
{
lean_object* v_a_5499_; lean_object* v___x_5501_; uint8_t v_isShared_5502_; uint8_t v_isSharedCheck_5506_; 
lean_dec_ref(v_b_5400_);
lean_dec_ref(v_a_5399_);
v_a_5499_ = lean_ctor_get(v___x_5413_, 0);
v_isSharedCheck_5506_ = !lean_is_exclusive(v___x_5413_);
if (v_isSharedCheck_5506_ == 0)
{
v___x_5501_ = v___x_5413_;
v_isShared_5502_ = v_isSharedCheck_5506_;
goto v_resetjp_5500_;
}
else
{
lean_inc(v_a_5499_);
lean_dec(v___x_5413_);
v___x_5501_ = lean_box(0);
v_isShared_5502_ = v_isSharedCheck_5506_;
goto v_resetjp_5500_;
}
v_resetjp_5500_:
{
lean_object* v___x_5504_; 
if (v_isShared_5502_ == 0)
{
v___x_5504_ = v___x_5501_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v_a_5499_);
v___x_5504_ = v_reuseFailAlloc_5505_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
return v___x_5504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq___boxed(lean_object* v_a_5507_, lean_object* v_b_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_, lean_object* v_a_5516_, lean_object* v_a_5517_, lean_object* v_a_5518_, lean_object* v_a_5519_, lean_object* v_a_5520_){
_start:
{
lean_object* v_res_5521_; 
v_res_5521_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5507_, v_b_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_, v_a_5518_, v_a_5519_);
lean_dec(v_a_5519_);
lean_dec_ref(v_a_5518_);
lean_dec(v_a_5517_);
lean_dec_ref(v_a_5516_);
lean_dec(v_a_5515_);
lean_dec_ref(v_a_5514_);
lean_dec(v_a_5513_);
lean_dec_ref(v_a_5512_);
lean_dec(v_a_5511_);
lean_dec(v_a_5510_);
lean_dec(v_a_5509_);
return v_res_5521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(lean_object* v_a_5522_, lean_object* v_b_5523_, lean_object* v_a_5524_, lean_object* v_a_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_, lean_object* v_a_5530_, lean_object* v_a_5531_, lean_object* v_a_5532_, lean_object* v_a_5533_){
_start:
{
lean_object* v___x_5535_; 
v___x_5535_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5522_, v_b_5523_, v_a_5524_, v_a_5532_);
if (lean_obj_tag(v___x_5535_) == 0)
{
lean_object* v_a_5536_; 
v_a_5536_ = lean_ctor_get(v___x_5535_, 0);
lean_inc(v_a_5536_);
lean_dec_ref_known(v___x_5535_, 1);
if (lean_obj_tag(v_a_5536_) == 1)
{
lean_object* v_val_5537_; lean_object* v___x_5538_; 
v_val_5537_ = lean_ctor_get(v_a_5536_, 0);
lean_inc(v_val_5537_);
lean_dec_ref_known(v_a_5536_, 1);
v___x_5538_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5537_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_);
if (lean_obj_tag(v___x_5538_) == 0)
{
lean_object* v_a_5539_; uint8_t v___x_5540_; 
v_a_5539_ = lean_ctor_get(v___x_5538_, 0);
lean_inc(v_a_5539_);
lean_dec_ref_known(v___x_5538_, 1);
v___x_5540_ = lean_unbox(v_a_5539_);
lean_dec(v_a_5539_);
if (v___x_5540_ == 0)
{
lean_object* v___x_5541_; 
v___x_5541_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5522_, v_b_5523_, v_val_5537_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_);
lean_dec(v_val_5537_);
return v___x_5541_;
}
else
{
lean_object* v___x_5542_; 
v___x_5542_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5522_, v_b_5523_, v_val_5537_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_);
lean_dec(v_val_5537_);
return v___x_5542_;
}
}
else
{
lean_object* v_a_5543_; lean_object* v___x_5545_; uint8_t v_isShared_5546_; uint8_t v_isSharedCheck_5550_; 
lean_dec(v_val_5537_);
lean_dec_ref(v_b_5523_);
lean_dec_ref(v_a_5522_);
v_a_5543_ = lean_ctor_get(v___x_5538_, 0);
v_isSharedCheck_5550_ = !lean_is_exclusive(v___x_5538_);
if (v_isSharedCheck_5550_ == 0)
{
v___x_5545_ = v___x_5538_;
v_isShared_5546_ = v_isSharedCheck_5550_;
goto v_resetjp_5544_;
}
else
{
lean_inc(v_a_5543_);
lean_dec(v___x_5538_);
v___x_5545_ = lean_box(0);
v_isShared_5546_ = v_isSharedCheck_5550_;
goto v_resetjp_5544_;
}
v_resetjp_5544_:
{
lean_object* v___x_5548_; 
if (v_isShared_5546_ == 0)
{
v___x_5548_ = v___x_5545_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v_a_5543_);
v___x_5548_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5547_;
}
v_reusejp_5547_:
{
return v___x_5548_;
}
}
}
}
else
{
lean_object* v___x_5551_; 
lean_dec(v_a_5536_);
v___x_5551_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5522_, v_b_5523_, v_a_5524_, v_a_5532_);
if (lean_obj_tag(v___x_5551_) == 0)
{
lean_object* v_a_5552_; lean_object* v___x_5554_; uint8_t v_isShared_5555_; uint8_t v_isSharedCheck_5562_; 
v_a_5552_ = lean_ctor_get(v___x_5551_, 0);
v_isSharedCheck_5562_ = !lean_is_exclusive(v___x_5551_);
if (v_isSharedCheck_5562_ == 0)
{
v___x_5554_ = v___x_5551_;
v_isShared_5555_ = v_isSharedCheck_5562_;
goto v_resetjp_5553_;
}
else
{
lean_inc(v_a_5552_);
lean_dec(v___x_5551_);
v___x_5554_ = lean_box(0);
v_isShared_5555_ = v_isSharedCheck_5562_;
goto v_resetjp_5553_;
}
v_resetjp_5553_:
{
if (lean_obj_tag(v_a_5552_) == 1)
{
lean_object* v_val_5556_; lean_object* v___x_5557_; 
lean_del_object(v___x_5554_);
v_val_5556_ = lean_ctor_get(v_a_5552_, 0);
lean_inc(v_val_5556_);
lean_dec_ref_known(v_a_5552_, 1);
v___x_5557_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5522_, v_b_5523_, v_val_5556_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_);
lean_dec(v_val_5556_);
return v___x_5557_;
}
else
{
lean_object* v___x_5558_; lean_object* v___x_5560_; 
lean_dec(v_a_5552_);
lean_dec_ref(v_b_5523_);
lean_dec_ref(v_a_5522_);
v___x_5558_ = lean_box(0);
if (v_isShared_5555_ == 0)
{
lean_ctor_set(v___x_5554_, 0, v___x_5558_);
v___x_5560_ = v___x_5554_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v___x_5558_);
v___x_5560_ = v_reuseFailAlloc_5561_;
goto v_reusejp_5559_;
}
v_reusejp_5559_:
{
return v___x_5560_;
}
}
}
}
else
{
lean_object* v_a_5563_; lean_object* v___x_5565_; uint8_t v_isShared_5566_; uint8_t v_isSharedCheck_5570_; 
lean_dec_ref(v_b_5523_);
lean_dec_ref(v_a_5522_);
v_a_5563_ = lean_ctor_get(v___x_5551_, 0);
v_isSharedCheck_5570_ = !lean_is_exclusive(v___x_5551_);
if (v_isSharedCheck_5570_ == 0)
{
v___x_5565_ = v___x_5551_;
v_isShared_5566_ = v_isSharedCheck_5570_;
goto v_resetjp_5564_;
}
else
{
lean_inc(v_a_5563_);
lean_dec(v___x_5551_);
v___x_5565_ = lean_box(0);
v_isShared_5566_ = v_isSharedCheck_5570_;
goto v_resetjp_5564_;
}
v_resetjp_5564_:
{
lean_object* v___x_5568_; 
if (v_isShared_5566_ == 0)
{
v___x_5568_ = v___x_5565_;
goto v_reusejp_5567_;
}
else
{
lean_object* v_reuseFailAlloc_5569_; 
v_reuseFailAlloc_5569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5569_, 0, v_a_5563_);
v___x_5568_ = v_reuseFailAlloc_5569_;
goto v_reusejp_5567_;
}
v_reusejp_5567_:
{
return v___x_5568_;
}
}
}
}
}
else
{
lean_object* v_a_5571_; lean_object* v___x_5573_; uint8_t v_isShared_5574_; uint8_t v_isSharedCheck_5578_; 
lean_dec_ref(v_b_5523_);
lean_dec_ref(v_a_5522_);
v_a_5571_ = lean_ctor_get(v___x_5535_, 0);
v_isSharedCheck_5578_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5578_ == 0)
{
v___x_5573_ = v___x_5535_;
v_isShared_5574_ = v_isSharedCheck_5578_;
goto v_resetjp_5572_;
}
else
{
lean_inc(v_a_5571_);
lean_dec(v___x_5535_);
v___x_5573_ = lean_box(0);
v_isShared_5574_ = v_isSharedCheck_5578_;
goto v_resetjp_5572_;
}
v_resetjp_5572_:
{
lean_object* v___x_5576_; 
if (v_isShared_5574_ == 0)
{
v___x_5576_ = v___x_5573_;
goto v_reusejp_5575_;
}
else
{
lean_object* v_reuseFailAlloc_5577_; 
v_reuseFailAlloc_5577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5577_, 0, v_a_5571_);
v___x_5576_ = v_reuseFailAlloc_5577_;
goto v_reusejp_5575_;
}
v_reusejp_5575_:
{
return v___x_5576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed(lean_object* v_a_5579_, lean_object* v_b_5580_, lean_object* v_a_5581_, lean_object* v_a_5582_, lean_object* v_a_5583_, lean_object* v_a_5584_, lean_object* v_a_5585_, lean_object* v_a_5586_, lean_object* v_a_5587_, lean_object* v_a_5588_, lean_object* v_a_5589_, lean_object* v_a_5590_, lean_object* v_a_5591_){
_start:
{
lean_object* v_res_5592_; 
v_res_5592_ = l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(v_a_5579_, v_b_5580_, v_a_5581_, v_a_5582_, v_a_5583_, v_a_5584_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_);
lean_dec(v_a_5590_);
lean_dec_ref(v_a_5589_);
lean_dec(v_a_5588_);
lean_dec_ref(v_a_5587_);
lean_dec(v_a_5586_);
lean_dec_ref(v_a_5585_);
lean_dec(v_a_5584_);
lean_dec_ref(v_a_5583_);
lean_dec(v_a_5582_);
lean_dec(v_a_5581_);
return v_res_5592_;
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
