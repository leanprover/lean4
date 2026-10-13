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
uint8_t v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_884_ = 0;
v___x_885_ = lean_unsigned_to_nat(0u);
v___x_886_ = lean_box(v___x_884_);
lean_inc_ref(v_a_870_);
v___x_887_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_887_, 0, v_a_870_);
lean_closure_set(v___x_887_, 1, v___x_886_);
lean_closure_set(v___x_887_, 2, v___x_885_);
v___x_888_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_887_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_1040_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_1040_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_1040_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
if (lean_obj_tag(v_a_889_) == 1)
{
lean_object* v_val_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
lean_del_object(v___x_891_);
v_val_893_ = lean_ctor_get(v_a_889_, 0);
lean_inc(v_val_893_);
lean_dec_ref_known(v_a_889_, 1);
v___x_894_ = lean_box(v___x_884_);
lean_inc_ref(v_b_871_);
v___x_895_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_895_, 0, v_b_871_);
lean_closure_set(v___x_895_, 1, v___x_894_);
lean_closure_set(v___x_895_, 2, v___x_885_);
v___x_896_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_895_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_1027_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_1027_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_1027_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
if (lean_obj_tag(v_a_897_) == 1)
{
lean_object* v_val_901_; lean_object* v___x_902_; 
lean_del_object(v___x_899_);
v_val_901_ = lean_ctor_get(v_a_897_, 0);
lean_inc(v_val_901_);
lean_dec_ref_known(v_a_897_, 1);
v___x_902_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_870_, v_a_873_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_904_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref_known(v___x_902_, 1);
v___x_904_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_871_, v_a_873_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___y_907_; uint8_t v___x_1006_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_904_, 1);
v___x_1006_ = lean_nat_dec_le(v_a_903_, v_a_905_);
if (v___x_1006_ == 0)
{
lean_dec(v_a_905_);
v___y_907_ = v_a_903_;
goto v___jp_906_;
}
else
{
lean_dec(v_a_903_);
v___y_907_ = v_a_905_;
goto v___jp_906_;
}
v___jp_906_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
lean_inc(v_val_901_);
lean_inc(v_val_893_);
v___x_908_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_908_, 0, v_val_893_);
lean_ctor_set(v___x_908_, 1, v_val_901_);
v___x_909_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_908_);
v___x_910_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_910_, 0, v_a_870_);
lean_ctor_set(v___x_910_, 1, v_b_871_);
lean_ctor_set(v___x_910_, 2, v_val_893_);
lean_ctor_set(v___x_910_, 3, v_val_901_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(v___x_911_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v_p_914_; lean_object* v___x_915_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
v_p_914_ = lean_ctor_get(v_a_913_, 0);
lean_inc(v___y_907_);
lean_inc_ref(v_p_914_);
v___x_915_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_914_, v___y_907_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_917_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_916_);
lean_dec_ref_known(v___x_915_, 1);
lean_inc(v___y_907_);
v___x_917_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_916_, v___x_884_, v___y_907_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_981_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_981_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_981_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_981_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
if (lean_obj_tag(v_a_918_) == 1)
{
lean_object* v_val_922_; lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v_val_922_ = lean_ctor_get(v_a_918_, 0);
lean_inc_n(v_val_922_, 2);
lean_dec_ref_known(v_a_918_, 1);
v___x_923_ = l_Lean_Grind_Linarith_Expr_norm(v_val_922_);
v___x_924_ = lean_box(0);
v___x_925_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_923_, v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
lean_del_object(v___x_920_);
lean_inc(v_a_913_);
v___x_926_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_926_, 0, v_a_913_);
lean_ctor_set(v___x_926_, 1, v_val_922_);
lean_inc(v___x_923_);
v___x_927_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_927_, 0, v___x_923_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
lean_ctor_set_uint8(v___x_927_, sizeof(void*)*2, v___x_884_);
v___x_928_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_927_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_971_; 
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; 
v_unused_972_ = lean_ctor_get(v___x_928_, 0);
lean_dec(v_unused_972_);
v___x_930_ = v___x_928_;
v_isShared_931_ = v_isSharedCheck_971_;
goto v_resetjp_929_;
}
else
{
lean_dec(v___x_928_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_971_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_914_);
v___x_933_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_932_, v_p_914_);
if (v_isShared_931_ == 0)
{
lean_ctor_set_tag(v___x_930_, 1);
lean_ctor_set(v___x_930_, 0, v_a_913_);
v___x_935_ = v___x_930_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_913_);
v___x_935_ = v_reuseFailAlloc_970_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
lean_inc_ref(v___x_933_);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_933_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = l_Lean_Grind_Linarith_Poly_mul(v___x_923_, v___x_932_);
lean_inc(v___y_907_);
v___x_938_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v___x_933_, v___y_907_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_940_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_939_);
lean_dec_ref_known(v___x_938_, 1);
v___x_940_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_939_, v___x_884_, v___y_907_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_953_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_953_ == 0)
{
v___x_943_ = v___x_940_;
v_isShared_944_ = v_isSharedCheck_953_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_940_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_953_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
if (lean_obj_tag(v_a_941_) == 1)
{
lean_object* v_val_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
lean_del_object(v___x_943_);
v_val_945_ = lean_ctor_get(v_a_941_, 0);
lean_inc(v_val_945_);
lean_dec_ref_known(v_a_941_, 1);
v___x_946_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_936_);
lean_ctor_set(v___x_946_, 1, v_val_945_);
v___x_947_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_947_, 0, v___x_937_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
lean_ctor_set_uint8(v___x_947_, sizeof(void*)*2, v___x_884_);
v___x_948_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_947_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
return v___x_948_;
}
else
{
lean_object* v___x_949_; lean_object* v___x_951_; 
lean_dec(v_a_941_);
lean_dec(v___x_937_);
lean_dec_ref_known(v___x_936_, 2);
v___x_949_ = lean_box(0);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_949_);
v___x_951_ = v___x_943_;
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
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec(v___x_937_);
lean_dec_ref_known(v___x_936_, 2);
v_a_954_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_940_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_940_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec(v___x_937_);
lean_dec_ref_known(v___x_936_, 2);
lean_dec(v___y_907_);
v_a_962_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_938_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_938_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
}
else
{
lean_dec(v___x_923_);
lean_dec(v_a_913_);
lean_dec(v___y_907_);
return v___x_928_;
}
}
else
{
lean_object* v___x_973_; lean_object* v___x_975_; 
lean_dec(v___x_923_);
lean_dec(v_val_922_);
lean_dec(v_a_913_);
lean_dec(v___y_907_);
v___x_973_ = lean_box(0);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_973_);
v___x_975_ = v___x_920_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
else
{
lean_object* v___x_977_; lean_object* v___x_979_; 
lean_dec(v_a_918_);
lean_dec(v_a_913_);
lean_dec(v___y_907_);
v___x_977_ = lean_box(0);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_977_);
v___x_979_ = v___x_920_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
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
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_dec(v_a_913_);
lean_dec(v___y_907_);
v_a_982_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_917_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_917_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v_a_913_);
lean_dec(v___y_907_);
v_a_990_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_915_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_915_);
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
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec(v___y_907_);
v_a_998_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_912_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_912_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec(v_a_903_);
lean_dec(v_val_901_);
lean_dec(v_val_893_);
lean_dec_ref(v_b_871_);
lean_dec_ref(v_a_870_);
v_a_1007_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_904_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_904_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec(v_val_901_);
lean_dec(v_val_893_);
lean_dec_ref(v_b_871_);
lean_dec_ref(v_a_870_);
v_a_1015_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_902_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_902_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
else
{
lean_object* v___x_1023_; lean_object* v___x_1025_; 
lean_dec(v_a_897_);
lean_dec(v_val_893_);
lean_dec_ref(v_b_871_);
lean_dec_ref(v_a_870_);
v___x_1023_ = lean_box(0);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_1023_);
v___x_1025_ = v___x_899_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1023_);
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
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec(v_val_893_);
lean_dec_ref(v_b_871_);
lean_dec_ref(v_a_870_);
v_a_1028_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_896_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_896_);
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
else
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
lean_dec(v_a_889_);
lean_dec_ref(v_b_871_);
lean_dec_ref(v_a_870_);
v___x_1036_ = lean_box(0);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_1036_);
v___x_1038_ = v___x_891_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec_ref(v_b_871_);
lean_dec_ref(v_a_870_);
v_a_1041_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_888_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_888_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___boxed(lean_object* v_a_1049_, lean_object* v_b_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_1049_, v_b_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec(v_a_1051_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(lean_object* v_a_1064_, lean_object* v_b_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1064_, v_a_1067_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; uint8_t v___x_1080_; lean_object* v___x_1081_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1078_, 1);
v___x_1080_ = 0;
lean_inc_ref(v_a_1064_);
v___x_1081_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1064_, v___x_1080_, v_a_1079_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1136_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1136_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1136_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
if (lean_obj_tag(v_a_1082_) == 1)
{
lean_object* v_val_1086_; lean_object* v___x_1087_; 
lean_del_object(v___x_1084_);
v_val_1086_ = lean_ctor_get(v_a_1082_, 0);
lean_inc(v_val_1086_);
lean_dec_ref_known(v_a_1082_, 1);
v___x_1087_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1065_, v_a_1067_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1089_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
lean_inc_ref(v_b_1065_);
v___x_1089_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_1065_, v___x_1080_, v_a_1088_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1115_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1115_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1115_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
if (lean_obj_tag(v_a_1090_) == 1)
{
lean_object* v_val_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; 
v_val_1094_ = lean_ctor_get(v_a_1090_, 0);
lean_inc_n(v_val_1094_, 2);
lean_dec_ref_known(v_a_1090_, 1);
lean_inc(v_val_1086_);
v___x_1095_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1095_, 0, v_val_1086_);
lean_ctor_set(v___x_1095_, 1, v_val_1094_);
v___x_1096_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1095_);
v___x_1097_ = lean_box(0);
v___x_1098_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_1096_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_del_object(v___x_1092_);
lean_inc(v_val_1094_);
lean_inc(v_val_1086_);
lean_inc_ref(v_b_1065_);
lean_inc_ref(v_a_1064_);
v___x_1099_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1099_, 0, v_a_1064_);
lean_ctor_set(v___x_1099_, 1, v_b_1065_);
lean_ctor_set(v___x_1099_, 2, v_val_1086_);
lean_ctor_set(v___x_1099_, 3, v_val_1094_);
lean_inc(v___x_1096_);
v___x_1100_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1100_, 0, v___x_1096_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
lean_ctor_set_uint8(v___x_1100_, sizeof(void*)*2, v___x_1080_);
v___x_1101_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1100_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_dec_ref_known(v___x_1101_, 1);
v___x_1102_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_1103_ = l_Lean_Grind_Linarith_Poly_mul(v___x_1096_, v___x_1102_);
v___x_1104_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1104_, 0, v_b_1065_);
lean_ctor_set(v___x_1104_, 1, v_a_1064_);
lean_ctor_set(v___x_1104_, 2, v_val_1094_);
lean_ctor_set(v___x_1104_, 3, v_val_1086_);
v___x_1105_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1105_, 0, v___x_1103_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
lean_ctor_set_uint8(v___x_1105_, sizeof(void*)*2, v___x_1080_);
v___x_1106_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1105_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
return v___x_1106_;
}
else
{
lean_dec(v___x_1096_);
lean_dec(v_val_1094_);
lean_dec(v_val_1086_);
lean_dec_ref(v_b_1065_);
lean_dec_ref(v_a_1064_);
return v___x_1101_;
}
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1109_; 
lean_dec(v___x_1096_);
lean_dec(v_val_1094_);
lean_dec(v_val_1086_);
lean_dec_ref(v_b_1065_);
lean_dec_ref(v_a_1064_);
v___x_1107_ = lean_box(0);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1107_);
v___x_1109_ = v___x_1092_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
else
{
lean_object* v___x_1111_; lean_object* v___x_1113_; 
lean_dec(v_a_1090_);
lean_dec(v_val_1086_);
lean_dec_ref(v_b_1065_);
lean_dec_ref(v_a_1064_);
v___x_1111_ = lean_box(0);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1111_);
v___x_1113_ = v___x_1092_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec(v_val_1086_);
lean_dec_ref(v_b_1065_);
lean_dec_ref(v_a_1064_);
v_a_1116_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1089_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1089_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
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
lean_dec(v_val_1086_);
lean_dec_ref(v_b_1065_);
lean_dec_ref(v_a_1064_);
v_a_1124_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1087_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1087_);
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
else
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
lean_dec(v_a_1082_);
lean_dec_ref(v_b_1065_);
lean_dec_ref(v_a_1064_);
v___x_1132_ = lean_box(0);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1132_);
v___x_1134_ = v___x_1084_;
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
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec_ref(v_b_1065_);
lean_dec_ref(v_a_1064_);
v_a_1137_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1081_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1081_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec_ref(v_b_1065_);
lean_dec_ref(v_a_1064_);
v_a_1145_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1078_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1078_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27___boxed(lean_object* v_a_1153_, lean_object* v_b_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_1153_, v_b_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec(v_a_1155_);
return v_res_1167_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(lean_object* v_msg_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1182_; lean_object* v___f_1183_; lean_object* v___x_2795__overap_1184_; lean_object* v___x_1185_; 
v___x_1182_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0);
v___f_1183_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1183_, 0, v___x_1182_);
v___x_2795__overap_1184_ = lean_panic_fn_borrowed(v___f_1183_, v_msg_1169_);
lean_dec_ref(v___f_1183_);
lean_inc(v___y_1180_);
lean_inc_ref(v___y_1179_);
lean_inc(v___y_1178_);
lean_inc_ref(v___y_1177_);
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
lean_inc(v___y_1174_);
lean_inc_ref(v___y_1173_);
lean_inc(v___y_1172_);
lean_inc(v___y_1171_);
lean_inc(v___y_1170_);
v___x_1185_ = lean_apply_12(v___x_2795__overap_1184_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, lean_box(0));
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___boxed(lean_object* v_msg_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v_msg_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec(v___y_1187_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__1(lean_object* v_a_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_nat_to_int(v_a_1200_);
return v___x_1201_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2));
v___x_1206_ = lean_unsigned_to_nat(42u);
v___x_1207_ = lean_unsigned_to_nat(87u);
v___x_1208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1));
v___x_1209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0));
v___x_1210_ = l_mkPanicMessageWithDecl(v___x_1209_, v___x_1208_, v___x_1207_, v___x_1206_, v___x_1205_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(lean_object* v_c_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v_c_1227_; lean_object* v_c_1233_; lean_object* v_p_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; uint8_t v___x_1272_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v___x_1270_, 1);
v___x_1272_ = lean_unbox(v_a_1271_);
lean_dec(v_a_1271_);
if (v___x_1272_ == 0)
{
lean_object* v_p_1273_; 
v_p_1273_ = lean_ctor_get(v_c_1211_, 0);
lean_inc(v_p_1273_);
v_c_1233_ = v_c_1211_;
v_p_1234_ = v_p_1273_;
v___y_1235_ = v_a_1212_;
v___y_1236_ = v_a_1213_;
v___y_1237_ = v_a_1214_;
v___y_1238_ = v_a_1215_;
v___y_1239_ = v_a_1216_;
v___y_1240_ = v_a_1217_;
v___y_1241_ = v_a_1218_;
v___y_1242_ = v_a_1219_;
v___y_1243_ = v_a_1220_;
v___y_1244_ = v_a_1221_;
v___y_1245_ = v_a_1222_;
goto v___jp_1232_;
}
else
{
lean_object* v_p_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v_p_1274_ = lean_ctor_get(v_c_1211_, 0);
v___x_1275_ = l_Lean_Grind_Linarith_Poly_gcdCoeffs(v_p_1274_);
v___x_1276_ = lean_unsigned_to_nat(1u);
v___x_1277_ = lean_nat_dec_eq(v___x_1275_, v___x_1276_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_inc(v___x_1275_);
v___x_1278_ = lean_nat_to_int(v___x_1275_);
lean_inc(v_p_1274_);
v___x_1279_ = l_Lean_Grind_Linarith_Poly_div(v_p_1274_, v___x_1278_);
lean_dec(v___x_1278_);
v___x_1280_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1275_);
lean_ctor_set(v___x_1280_, 1, v_c_1211_);
lean_inc(v___x_1279_);
v___x_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v_c_1233_ = v___x_1281_;
v_p_1234_ = v___x_1279_;
v___y_1235_ = v_a_1212_;
v___y_1236_ = v_a_1213_;
v___y_1237_ = v_a_1214_;
v___y_1238_ = v_a_1215_;
v___y_1239_ = v_a_1216_;
v___y_1240_ = v_a_1217_;
v___y_1241_ = v_a_1218_;
v___y_1242_ = v_a_1219_;
v___y_1243_ = v_a_1220_;
v___y_1244_ = v_a_1221_;
v___y_1245_ = v_a_1222_;
goto v___jp_1232_;
}
else
{
lean_inc(v_p_1274_);
lean_dec(v___x_1275_);
v_c_1233_ = v_c_1211_;
v_p_1234_ = v_p_1274_;
v___y_1235_ = v_a_1212_;
v___y_1236_ = v_a_1213_;
v___y_1237_ = v_a_1214_;
v___y_1238_ = v_a_1215_;
v___y_1239_ = v_a_1216_;
v___y_1240_ = v_a_1217_;
v___y_1241_ = v_a_1218_;
v___y_1242_ = v_a_1219_;
v___y_1243_ = v_a_1220_;
v___y_1244_ = v_a_1221_;
v___y_1245_ = v_a_1222_;
goto v___jp_1232_;
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec_ref(v_c_1211_);
v_a_1282_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1270_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1270_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
v___jp_1224_:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1228_ = lean_nat_abs(v___y_1225_);
lean_dec(v___y_1225_);
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___y_1226_);
lean_ctor_set(v___x_1229_, 1, v_c_1227_);
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1228_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
return v___x_1231_;
}
v___jp_1232_:
{
lean_object* v___x_1246_; 
lean_inc(v_p_1234_);
v___x_1246_ = l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(v_p_1234_);
if (lean_obj_tag(v___x_1246_) == 1)
{
lean_object* v_val_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1267_; 
v_val_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1267_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_val_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1267_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v_fst_1251_; lean_object* v_snd_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1266_; 
v_fst_1251_ = lean_ctor_get(v_val_1247_, 0);
v_snd_1252_ = lean_ctor_get(v_val_1247_, 1);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_val_1247_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1254_ = v_val_1247_;
v_isShared_1255_ = v_isSharedCheck_1266_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_snd_1252_);
lean_inc(v_fst_1251_);
lean_dec(v_val_1247_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1266_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; uint8_t v___x_1257_; 
v___x_1256_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_1257_ = lean_int_dec_lt(v_fst_1251_, v___x_1256_);
if (v___x_1257_ == 0)
{
lean_del_object(v___x_1254_);
lean_del_object(v___x_1249_);
lean_dec(v_p_1234_);
v___y_1225_ = v_fst_1251_;
v___y_1226_ = v_snd_1252_;
v_c_1227_ = v_c_1233_;
goto v___jp_1224_;
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1258_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_1259_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1234_, v___x_1258_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set_tag(v___x_1249_, 3);
lean_ctor_set(v___x_1249_, 0, v_c_1233_);
v___x_1261_ = v___x_1249_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_c_1233_);
v___x_1261_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1263_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 1, v___x_1261_);
lean_ctor_set(v___x_1254_, 0, v___x_1259_);
v___x_1263_ = v___x_1254_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
v___y_1225_ = v_fst_1251_;
v___y_1226_ = v_snd_1252_;
v_c_1227_ = v___x_1263_;
goto v___jp_1224_;
}
}
}
}
}
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec(v___x_1246_);
lean_dec(v_p_1234_);
lean_dec_ref(v_c_1233_);
v___x_1268_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3);
v___x_1269_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v___x_1268_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1269_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___boxed(lean_object* v_c_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_c_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec(v_a_1292_);
lean_dec(v_a_1291_);
return v_res_1303_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = l_Lean_maxRecDepthErrorMessage;
v___x_1310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
return v___x_1310_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_1312_ = l_Lean_MessageData_ofFormat(v___x_1311_);
return v___x_1312_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_1314_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_1315_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v___x_1313_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_1316_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1318_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1319_, 0, v_ref_1316_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1321_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_1324_, lean_object* v_ref_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1325_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_1339_, lean_object* v_ref_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(v_00_u03b1_1339_, v_ref_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec(v___y_1341_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(lean_object* v_c_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v_toCold_1385_; lean_object* v_p_1386_; lean_object* v_currRecDepth_1387_; lean_object* v_ref_1388_; uint16_t v_optionFlags_1389_; uint8_t v_suppressElabErrors_1390_; uint8_t v_isRecordingDeps_1391_; lean_object* v_options_1392_; lean_object* v_maxRecDepth_1393_; lean_object* v_inheritedTraceOptions_1394_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v_toCold_1385_ = lean_ctor_get(v_a_1364_, 0);
lean_inc_ref(v_toCold_1385_);
v_p_1386_ = lean_ctor_get(v_c_1354_, 0);
v_currRecDepth_1387_ = lean_ctor_get(v_a_1364_, 1);
lean_inc(v_currRecDepth_1387_);
v_ref_1388_ = lean_ctor_get(v_a_1364_, 2);
lean_inc(v_ref_1388_);
v_optionFlags_1389_ = lean_ctor_get_uint16(v_a_1364_, sizeof(void*)*3);
v_suppressElabErrors_1390_ = lean_ctor_get_uint8(v_a_1364_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1391_ = lean_ctor_get_uint8(v_a_1364_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_1364_);
v_options_1392_ = lean_ctor_get(v_toCold_1385_, 2);
lean_inc_ref(v_options_1392_);
v_maxRecDepth_1393_ = lean_ctor_get(v_toCold_1385_, 3);
v_inheritedTraceOptions_1394_ = lean_ctor_get(v_toCold_1385_, 11);
lean_inc_ref(v_inheritedTraceOptions_1394_);
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = lean_nat_dec_eq(v_maxRecDepth_1393_, v___x_1488_);
if (v___x_1489_ == 0)
{
uint8_t v___x_1490_; 
v___x_1490_ = lean_nat_dec_eq(v_currRecDepth_1387_, v_maxRecDepth_1393_);
if (v___x_1490_ == 0)
{
goto v___jp_1395_;
}
else
{
lean_object* v___x_1491_; 
lean_dec_ref(v_inheritedTraceOptions_1394_);
lean_dec_ref(v_options_1392_);
lean_dec(v_currRecDepth_1387_);
lean_dec_ref(v_toCold_1385_);
lean_dec_ref(v_c_1354_);
v___x_1491_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1388_);
return v___x_1491_;
}
}
else
{
goto v___jp_1395_;
}
v___jp_1367_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_1382_, 0, v___y_1368_);
lean_ctor_set(v___x_1382_, 1, v___y_1369_);
lean_ctor_set(v___x_1382_, 2, v_c_1354_);
v___x_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___y_1370_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v_c_1354_ = v___x_1383_;
v_a_1355_ = v___y_1371_;
v_a_1356_ = v___y_1372_;
v_a_1357_ = v___y_1373_;
v_a_1358_ = v___y_1374_;
v_a_1359_ = v___y_1375_;
v_a_1360_ = v___y_1376_;
v_a_1361_ = v___y_1377_;
v_a_1362_ = v___y_1378_;
v_a_1363_ = v___y_1379_;
v_a_1364_ = v___y_1380_;
v_a_1365_ = v___y_1381_;
goto _start;
}
v___jp_1395_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1396_ = lean_unsigned_to_nat(1u);
v___x_1397_ = lean_nat_add(v_currRecDepth_1387_, v___x_1396_);
lean_dec(v_currRecDepth_1387_);
v___x_1398_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1398_, 0, v_toCold_1385_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
lean_ctor_set(v___x_1398_, 2, v_ref_1388_);
lean_ctor_set_uint16(v___x_1398_, sizeof(void*)*3, v_optionFlags_1389_);
lean_ctor_set_uint8(v___x_1398_, sizeof(void*)*3 + 2, v_suppressElabErrors_1390_);
lean_ctor_set_uint8(v___x_1398_, sizeof(void*)*3 + 3, v_isRecordingDeps_1391_);
lean_inc(v_p_1386_);
v___x_1399_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_1386_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v___x_1398_, v_a_1365_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1479_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1479_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1479_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
if (lean_obj_tag(v_a_1400_) == 1)
{
lean_object* v_val_1404_; lean_object* v_snd_1405_; uint8_t v_hasTrace_1406_; 
lean_del_object(v___x_1402_);
v_val_1404_ = lean_ctor_get(v_a_1400_, 0);
lean_inc(v_val_1404_);
lean_dec_ref_known(v_a_1400_, 1);
v_snd_1405_ = lean_ctor_get(v_val_1404_, 1);
lean_inc(v_snd_1405_);
v_hasTrace_1406_ = lean_ctor_get_uint8(v_options_1392_, sizeof(void*)*1);
if (v_hasTrace_1406_ == 0)
{
lean_object* v_fst_1407_; lean_object* v_fst_1408_; lean_object* v_snd_1409_; 
lean_dec_ref(v_inheritedTraceOptions_1394_);
lean_dec_ref(v_options_1392_);
v_fst_1407_ = lean_ctor_get(v_val_1404_, 0);
lean_inc(v_fst_1407_);
lean_dec(v_val_1404_);
v_fst_1408_ = lean_ctor_get(v_snd_1405_, 0);
lean_inc(v_fst_1408_);
v_snd_1409_ = lean_ctor_get(v_snd_1405_, 1);
lean_inc(v_snd_1409_);
lean_dec(v_snd_1405_);
v___y_1368_ = v_fst_1407_;
v___y_1369_ = v_fst_1408_;
v___y_1370_ = v_snd_1409_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v_a_1359_;
v___y_1376_ = v_a_1360_;
v___y_1377_ = v_a_1361_;
v___y_1378_ = v_a_1362_;
v___y_1379_ = v_a_1363_;
v___y_1380_ = v___x_1398_;
v___y_1381_ = v_a_1365_;
goto v___jp_1367_;
}
else
{
lean_object* v_fst_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1474_; 
v_fst_1410_ = lean_ctor_get(v_val_1404_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_val_1404_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; 
v_unused_1475_ = lean_ctor_get(v_val_1404_, 1);
lean_dec(v_unused_1475_);
v___x_1412_ = v_val_1404_;
v_isShared_1413_ = v_isSharedCheck_1474_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_fst_1410_);
lean_dec(v_val_1404_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1474_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v_fst_1414_; lean_object* v_snd_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1473_; 
v_fst_1414_ = lean_ctor_get(v_snd_1405_, 0);
v_snd_1415_ = lean_ctor_get(v_snd_1405_, 1);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_snd_1405_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1417_ = v_snd_1405_;
v_isShared_1418_ = v_isSharedCheck_1473_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_snd_1415_);
lean_inc(v_fst_1414_);
lean_dec(v_snd_1405_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1473_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___x_1419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_1420_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_1421_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1394_, v_options_1392_, v___x_1420_);
lean_dec_ref(v_options_1392_);
lean_dec_ref(v_inheritedTraceOptions_1394_);
if (v___x_1421_ == 0)
{
lean_del_object(v___x_1417_);
lean_del_object(v___x_1412_);
v___y_1368_ = v_fst_1410_;
v___y_1369_ = v_fst_1414_;
v___y_1370_ = v_snd_1415_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v_a_1359_;
v___y_1376_ = v_a_1360_;
v___y_1377_ = v_a_1361_;
v___y_1378_ = v_a_1362_;
v___y_1379_ = v_a_1363_;
v___y_1380_ = v___x_1398_;
v___y_1381_ = v_a_1365_;
goto v___jp_1367_;
}
else
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_1410_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v___x_1398_, v_a_1365_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1424_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
v___x_1424_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v___x_1398_, v_a_1365_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1426_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v___x_1426_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_fst_1414_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v___x_1398_, v_a_1365_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1431_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = l_Lean_MessageData_ofExpr(v_a_1423_);
v___x_1429_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_1418_ == 0)
{
lean_ctor_set_tag(v___x_1417_, 7);
lean_ctor_set(v___x_1417_, 1, v___x_1429_);
lean_ctor_set(v___x_1417_, 0, v___x_1428_);
v___x_1431_ = v___x_1417_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = l_Lean_MessageData_ofExpr(v_a_1425_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set_tag(v___x_1412_, 7);
lean_ctor_set(v___x_1412_, 1, v___x_1432_);
lean_ctor_set(v___x_1412_, 0, v___x_1431_);
v___x_1434_ = v___x_1412_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
lean_ctor_set(v___x_1435_, 1, v___x_1429_);
v___x_1436_ = l_Lean_MessageData_ofExpr(v_a_1427_);
v___x_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1435_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_1419_, v___x_1437_, v_a_1362_, v_a_1363_, v___x_1398_, v_a_1365_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_dec_ref_known(v___x_1438_, 1);
v___y_1368_ = v_fst_1410_;
v___y_1369_ = v_fst_1414_;
v___y_1370_ = v_snd_1415_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v_a_1359_;
v___y_1376_ = v_a_1360_;
v___y_1377_ = v_a_1361_;
v___y_1378_ = v_a_1362_;
v___y_1379_ = v_a_1363_;
v___y_1380_ = v___x_1398_;
v___y_1381_ = v_a_1365_;
goto v___jp_1367_;
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec(v_snd_1415_);
lean_dec(v_fst_1414_);
lean_dec(v_fst_1410_);
lean_dec_ref_known(v___x_1398_, 3);
lean_dec_ref(v_c_1354_);
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec(v_a_1425_);
lean_dec(v_a_1423_);
lean_del_object(v___x_1417_);
lean_dec(v_snd_1415_);
lean_dec(v_fst_1414_);
lean_del_object(v___x_1412_);
lean_dec(v_fst_1410_);
lean_dec_ref_known(v___x_1398_, 3);
lean_dec_ref(v_c_1354_);
v_a_1449_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1426_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1426_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec(v_a_1423_);
lean_del_object(v___x_1417_);
lean_dec(v_snd_1415_);
lean_dec(v_fst_1414_);
lean_del_object(v___x_1412_);
lean_dec(v_fst_1410_);
lean_dec_ref_known(v___x_1398_, 3);
lean_dec_ref(v_c_1354_);
v_a_1457_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1424_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1424_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_del_object(v___x_1417_);
lean_dec(v_snd_1415_);
lean_dec(v_fst_1414_);
lean_del_object(v___x_1412_);
lean_dec(v_fst_1410_);
lean_dec_ref_known(v___x_1398_, 3);
lean_dec_ref(v_c_1354_);
v_a_1465_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1422_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1422_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
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
lean_object* v___x_1477_; 
lean_dec(v_a_1400_);
lean_dec_ref_known(v___x_1398_, 3);
lean_dec_ref(v_inheritedTraceOptions_1394_);
lean_dec_ref(v_options_1392_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v_c_1354_);
v___x_1477_ = v___x_1402_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_c_1354_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref_known(v___x_1398_, 3);
lean_dec_ref(v_inheritedTraceOptions_1394_);
lean_dec_ref(v_options_1392_);
lean_dec_ref(v_c_1354_);
v_a_1480_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1399_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1399_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object* v_c_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
lean_dec(v_a_1503_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec(v_a_1493_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_ref_1512_; lean_object* v___x_1513_; lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1522_; 
v_ref_1512_ = lean_ctor_get(v___y_1509_, 2);
v___x_1513_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msg_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1522_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1522_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v___x_1520_; 
lean_inc(v_ref_1512_);
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v_ref_1512_);
lean_ctor_set(v___x_1518_, 1, v_a_1514_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set_tag(v___x_1516_, 1);
lean_ctor_set(v___x_1516_, 0, v___x_1518_);
v___x_1520_ = v___x_1516_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___boxed(lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec(v___y_1566_);
return v_res_1578_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0));
v___x_1581_ = l_Lean_stringToMessageData(v___x_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1606_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1597_ = v___x_1594_;
v_isShared_1598_ = v_isSharedCheck_1606_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1594_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1606_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v_ltFn_x3f_1599_; 
v_ltFn_x3f_1599_ = lean_ctor_get(v_a_1595_, 21);
lean_inc(v_ltFn_x3f_1599_);
lean_dec(v_a_1595_);
if (lean_obj_tag(v_ltFn_x3f_1599_) == 1)
{
lean_object* v_val_1600_; lean_object* v___x_1602_; 
v_val_1600_ = lean_ctor_get(v_ltFn_x3f_1599_, 0);
lean_inc(v_val_1600_);
lean_dec_ref_known(v_ltFn_x3f_1599_, 1);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v_val_1600_);
v___x_1602_ = v___x_1597_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_val_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
lean_dec(v_ltFn_x3f_1599_);
lean_del_object(v___x_1597_);
v___x_1604_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1);
v___x_1605_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1604_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
return v___x_1605_;
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
v_a_1607_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1594_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1594_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___boxed(lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec(v___y_1615_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(lean_object* v_p_1628_, uint8_t v_strict_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
if (v_strict_1629_ == 0)
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1644_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_a_1643_);
lean_dec_ref_known(v___x_1642_, 1);
v___x_1644_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1628_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1646_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v___x_1644_, 1);
v___x_1646_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1656_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1656_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1656_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v_ofNatZero_1651_; lean_object* v___x_1652_; lean_object* v___x_1654_; 
v_ofNatZero_1651_ = lean_ctor_get(v_a_1647_, 18);
lean_inc_ref(v_ofNatZero_1651_);
lean_dec(v_a_1647_);
v___x_1652_ = l_Lean_mkAppB(v_a_1643_, v_a_1645_, v_ofNatZero_1651_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1652_);
v___x_1654_ = v___x_1649_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec(v_a_1645_);
lean_dec(v_a_1643_);
v_a_1657_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1646_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1646_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_dec(v_a_1643_);
return v___x_1644_;
}
}
else
{
return v___x_1642_;
}
}
else
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1665_, 1);
v___x_1667_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1628_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1669_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1667_, 1);
v___x_1669_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1679_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1679_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1679_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v_ofNatZero_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
v_ofNatZero_1674_ = lean_ctor_get(v_a_1670_, 18);
lean_inc_ref(v_ofNatZero_1674_);
lean_dec(v_a_1670_);
v___x_1675_ = l_Lean_mkAppB(v_a_1666_, v_a_1668_, v_ofNatZero_1674_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1675_);
v___x_1677_ = v___x_1672_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_dec(v_a_1668_);
lean_dec(v_a_1666_);
v_a_1680_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1669_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1669_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_dec(v_a_1666_);
return v___x_1667_;
}
}
else
{
return v___x_1665_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_p_1688_, lean_object* v_strict_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
uint8_t v_strict_boxed_1702_; lean_object* v_res_1703_; 
v_strict_boxed_1702_ = lean_unbox(v_strict_1689_);
v_res_1703_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1688_, v_strict_boxed_1702_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec(v_p_1688_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(lean_object* v_c_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_p_1717_; uint8_t v_strict_1718_; lean_object* v___x_1719_; 
v_p_1717_ = lean_ctor_get(v_c_1704_, 0);
v_strict_1718_ = lean_ctor_get_uint8(v_c_1704_, sizeof(void*)*2);
v___x_1719_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1717_, v_strict_1718_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0___boxed(lean_object* v_c_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v_c_1720_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object* v_a_1734_, lean_object* v_x_1735_, lean_object* v_c_u2081_1736_, lean_object* v_b_1737_, lean_object* v_c_u2082_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_toCold_1751_; lean_object* v_options_1752_; lean_object* v_p_1753_; lean_object* v_p_1754_; uint8_t v_strict_1755_; lean_object* v_inheritedTraceOptions_1756_; uint8_t v_hasTrace_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v_p_1762_; 
v_toCold_1751_ = lean_ctor_get(v_a_1748_, 0);
v_options_1752_ = lean_ctor_get(v_toCold_1751_, 2);
v_p_1753_ = lean_ctor_get(v_c_u2081_1736_, 0);
v_p_1754_ = lean_ctor_get(v_c_u2082_1738_, 0);
v_strict_1755_ = lean_ctor_get_uint8(v_c_u2082_1738_, sizeof(void*)*2);
v_inheritedTraceOptions_1756_ = lean_ctor_get(v_toCold_1751_, 11);
v_hasTrace_1757_ = lean_ctor_get_uint8(v_options_1752_, sizeof(void*)*1);
v___x_1758_ = lean_nat_to_int(v_a_1734_);
lean_inc(v_p_1754_);
v___x_1759_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1754_, v___x_1758_);
lean_dec(v___x_1758_);
v___x_1760_ = lean_int_neg(v_b_1737_);
lean_inc(v_p_1753_);
v___x_1761_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1753_, v___x_1760_);
lean_dec(v___x_1760_);
v_p_1762_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1759_, v___x_1761_);
if (v_hasTrace_1757_ == 0)
{
goto v___jp_1763_;
}
else
{
lean_object* v_cls_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v_cls_1767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_1768_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2);
v___x_1769_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1756_, v_options_1752_, v___x_1768_);
if (v___x_1769_ == 0)
{
goto v___jp_1763_;
}
else
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1735_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v___x_1772_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_1736_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v___x_1774_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_u2082_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref_known(v___x_1774_, 1);
v___x_1776_ = l_Lean_MessageData_ofExpr(v_a_1771_);
v___x_1777_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_1778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1776_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___x_1779_ = l_Lean_MessageData_ofExpr(v_a_1773_);
v___x_1780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1778_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
lean_ctor_set(v___x_1781_, 1, v___x_1777_);
v___x_1782_ = l_Lean_MessageData_ofExpr(v_a_1775_);
v___x_1783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1781_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_1767_, v___x_1783_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_dec_ref_known(v___x_1784_, 1);
goto v___jp_1763_;
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec(v_p_1762_);
lean_dec_ref(v_c_u2082_1738_);
lean_dec_ref(v_c_u2081_1736_);
lean_dec(v_x_1735_);
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v_a_1773_);
lean_dec(v_a_1771_);
lean_dec(v_p_1762_);
lean_dec_ref(v_c_u2082_1738_);
lean_dec_ref(v_c_u2081_1736_);
lean_dec(v_x_1735_);
v_a_1793_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1774_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1774_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec(v_a_1771_);
lean_dec(v_p_1762_);
lean_dec_ref(v_c_u2082_1738_);
lean_dec_ref(v_c_u2081_1736_);
lean_dec(v_x_1735_);
v_a_1801_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1772_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1772_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec(v_p_1762_);
lean_dec_ref(v_c_u2082_1738_);
lean_dec_ref(v_c_u2081_1736_);
lean_dec(v_x_1735_);
v_a_1809_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1770_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1770_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
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
v___jp_1763_:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = lean_alloc_ctor(13, 3, 0);
lean_ctor_set(v___x_1764_, 0, v_x_1735_);
lean_ctor_set(v___x_1764_, 1, v_c_u2081_1736_);
lean_ctor_set(v___x_1764_, 2, v_c_u2082_1738_);
v___x_1765_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1765_, 0, v_p_1762_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
lean_ctor_set_uint8(v___x_1765_, sizeof(void*)*2, v_strict_1755_);
v___x_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
return v___x_1766_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object** _args){
lean_object* v_a_1817_ = _args[0];
lean_object* v_x_1818_ = _args[1];
lean_object* v_c_u2081_1819_ = _args[2];
lean_object* v_b_1820_ = _args[3];
lean_object* v_c_u2082_1821_ = _args[4];
lean_object* v_a_1822_ = _args[5];
lean_object* v_a_1823_ = _args[6];
lean_object* v_a_1824_ = _args[7];
lean_object* v_a_1825_ = _args[8];
lean_object* v_a_1826_ = _args[9];
lean_object* v_a_1827_ = _args[10];
lean_object* v_a_1828_ = _args[11];
lean_object* v_a_1829_ = _args[12];
lean_object* v_a_1830_ = _args[13];
lean_object* v_a_1831_ = _args[14];
lean_object* v_a_1832_ = _args[15];
lean_object* v_a_1833_ = _args[16];
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1817_, v_x_1818_, v_c_u2081_1819_, v_b_1820_, v_c_u2082_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_a_1824_);
lean_dec(v_a_1823_);
lean_dec(v_a_1822_);
lean_dec(v_b_1820_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1835_, lean_object* v_msg_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1836_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1850_, lean_object* v_msg_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1850_, v_msg_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec(v___y_1852_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(lean_object* v_a_1873_, lean_object* v_x_1874_, lean_object* v_c_u2081_1875_, lean_object* v_as_1876_, size_t v_sz_1877_, size_t v_i_1878_, lean_object* v_b_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
uint8_t v___x_1892_; 
v___x_1892_ = lean_usize_dec_lt(v_i_1878_, v_sz_1877_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; 
lean_dec_ref(v_c_u2081_1875_);
lean_dec(v_x_1874_);
lean_dec(v_a_1873_);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v_b_1879_);
return v___x_1893_;
}
else
{
lean_object* v_a_1894_; lean_object* v_fst_1895_; lean_object* v_snd_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
lean_dec_ref(v_b_1879_);
v_a_1894_ = lean_array_uget_borrowed(v_as_1876_, v_i_1878_);
v_fst_1895_ = lean_ctor_get(v_a_1894_, 0);
v_snd_1896_ = lean_ctor_get(v_a_1894_, 1);
v___x_1897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
lean_inc(v_snd_1896_);
lean_inc_ref(v_c_u2081_1875_);
lean_inc(v_x_1874_);
lean_inc(v_a_1873_);
v___x_1898_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1873_, v_x_1874_, v_c_u2081_1875_, v_fst_1895_, v_snd_1896_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1900_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1898_, 1);
v___x_1900_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_a_1899_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v___x_1901_; 
lean_dec_ref_known(v___x_1900_, 1);
v___x_1901_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1914_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1914_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1914_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
uint8_t v___x_1906_; 
v___x_1906_ = lean_unbox(v_a_1902_);
lean_dec(v_a_1902_);
if (v___x_1906_ == 0)
{
size_t v___x_1907_; size_t v___x_1908_; 
lean_del_object(v___x_1904_);
v___x_1907_ = ((size_t)1ULL);
v___x_1908_ = lean_usize_add(v_i_1878_, v___x_1907_);
v_i_1878_ = v___x_1908_;
v_b_1879_ = v___x_1897_;
goto _start;
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1912_; 
lean_dec_ref(v_c_u2081_1875_);
lean_dec(v_x_1874_);
lean_dec(v_a_1873_);
v___x_1910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1910_);
v___x_1912_ = v___x_1904_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec_ref(v_c_u2081_1875_);
lean_dec(v_x_1874_);
lean_dec(v_a_1873_);
v_a_1915_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1901_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1901_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec_ref(v_c_u2081_1875_);
lean_dec(v_x_1874_);
lean_dec(v_a_1873_);
v_a_1923_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1900_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1900_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec_ref(v_c_u2081_1875_);
lean_dec(v_x_1874_);
lean_dec(v_a_1873_);
v_a_1931_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1898_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1898_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___boxed(lean_object** _args){
lean_object* v_a_1939_ = _args[0];
lean_object* v_x_1940_ = _args[1];
lean_object* v_c_u2081_1941_ = _args[2];
lean_object* v_as_1942_ = _args[3];
lean_object* v_sz_1943_ = _args[4];
lean_object* v_i_1944_ = _args[5];
lean_object* v_b_1945_ = _args[6];
lean_object* v___y_1946_ = _args[7];
lean_object* v___y_1947_ = _args[8];
lean_object* v___y_1948_ = _args[9];
lean_object* v___y_1949_ = _args[10];
lean_object* v___y_1950_ = _args[11];
lean_object* v___y_1951_ = _args[12];
lean_object* v___y_1952_ = _args[13];
lean_object* v___y_1953_ = _args[14];
lean_object* v___y_1954_ = _args[15];
lean_object* v___y_1955_ = _args[16];
lean_object* v___y_1956_ = _args[17];
lean_object* v___y_1957_ = _args[18];
_start:
{
size_t v_sz_boxed_1958_; size_t v_i_boxed_1959_; lean_object* v_res_1960_; 
v_sz_boxed_1958_ = lean_unbox_usize(v_sz_1943_);
lean_dec(v_sz_1943_);
v_i_boxed_1959_ = lean_unbox_usize(v_i_1944_);
lean_dec(v_i_1944_);
v_res_1960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1939_, v_x_1940_, v_c_u2081_1941_, v_as_1942_, v_sz_boxed_1958_, v_i_boxed_1959_, v_b_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v_as_1942_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(lean_object* v_a_1961_, lean_object* v_x_1962_, lean_object* v_c_u2081_1963_, lean_object* v_todo_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; size_t v_sz_1979_; size_t v___x_1980_; lean_object* v___x_1981_; 
v___x_1977_ = lean_box(0);
v___x_1978_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_1979_ = lean_array_size(v_todo_1964_);
v___x_1980_ = ((size_t)0ULL);
v___x_1981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1961_, v_x_1962_, v_c_u2081_1963_, v_todo_1964_, v_sz_1979_, v___x_1980_, v___x_1978_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1994_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_1994_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1994_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v_fst_1986_; 
v_fst_1986_ = lean_ctor_get(v_a_1982_, 0);
lean_inc(v_fst_1986_);
lean_dec(v_a_1982_);
if (lean_obj_tag(v_fst_1986_) == 0)
{
lean_object* v___x_1988_; 
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1977_);
v___x_1988_ = v___x_1984_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1977_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
else
{
lean_object* v_val_1990_; lean_object* v___x_1992_; 
v_val_1990_ = lean_ctor_get(v_fst_1986_, 0);
lean_inc(v_val_1990_);
lean_dec_ref_known(v_fst_1986_, 1);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v_val_1990_);
v___x_1992_ = v___x_1984_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_val_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
v_a_1995_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1981_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1981_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object* v_a_2003_, lean_object* v_x_2004_, lean_object* v_c_u2081_2005_, lean_object* v_todo_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2003_, v_x_2004_, v_c_u2081_2005_, v_todo_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_todo_2006_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_2020_, lean_object* v_as_2021_, size_t v_sz_2022_, size_t v_i_2023_, lean_object* v_b_2024_){
_start:
{
uint8_t v___x_2025_; 
v___x_2025_ = lean_usize_dec_lt(v_i_2023_, v_sz_2022_);
if (v___x_2025_ == 0)
{
return v_b_2024_;
}
else
{
lean_object* v_snd_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2059_; 
v_snd_2026_ = lean_ctor_get(v_b_2024_, 1);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_b_2024_);
if (v_isSharedCheck_2059_ == 0)
{
lean_object* v_unused_2060_; 
v_unused_2060_ = lean_ctor_get(v_b_2024_, 0);
lean_dec(v_unused_2060_);
v___x_2028_ = v_b_2024_;
v_isShared_2029_ = v_isSharedCheck_2059_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_snd_2026_);
lean_dec(v_b_2024_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2059_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v_fst_2030_; lean_object* v_snd_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2058_; 
v_fst_2030_ = lean_ctor_get(v_snd_2026_, 0);
v_snd_2031_ = lean_ctor_get(v_snd_2026_, 1);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_snd_2026_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2033_ = v_snd_2026_;
v_isShared_2034_ = v_isSharedCheck_2058_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_snd_2031_);
lean_inc(v_fst_2030_);
lean_dec(v_snd_2026_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2058_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v_a_2035_; lean_object* v_p_2036_; lean_object* v___x_2037_; lean_object* v_a_2039_; lean_object* v_b_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; 
v_a_2035_ = lean_array_uget_borrowed(v_as_2021_, v_i_2023_);
v_p_2036_ = lean_ctor_get(v_a_2035_, 0);
v___x_2037_ = lean_box(0);
v_b_2046_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2036_, v_x_2020_);
v___x_2047_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2048_ = lean_int_dec_eq(v_b_2046_, v___x_2047_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2050_; 
lean_inc(v_a_2035_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 1, v_a_2035_);
lean_ctor_set(v___x_2028_, 0, v_b_2046_);
v___x_2050_ = v___x_2028_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_b_2046_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_a_2035_);
v___x_2050_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v_todo_2051_; lean_object* v___x_2052_; 
v_todo_2051_ = lean_array_push(v_snd_2031_, v___x_2050_);
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v_fst_2030_);
lean_ctor_set(v___x_2052_, 1, v_todo_2051_);
v_a_2039_ = v___x_2052_;
goto v___jp_2038_;
}
}
else
{
lean_object* v_cs_x27_2054_; lean_object* v___x_2056_; 
lean_dec(v_b_2046_);
lean_inc(v_a_2035_);
v_cs_x27_2054_ = l_Lean_PersistentArray_push___redArg(v_fst_2030_, v_a_2035_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 1, v_snd_2031_);
lean_ctor_set(v___x_2028_, 0, v_cs_x27_2054_);
v___x_2056_ = v___x_2028_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_cs_x27_2054_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_snd_2031_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
v_a_2039_ = v___x_2056_;
goto v___jp_2038_;
}
}
v___jp_2038_:
{
lean_object* v___x_2041_; 
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 1, v_a_2039_);
lean_ctor_set(v___x_2033_, 0, v___x_2037_);
v___x_2041_ = v___x_2033_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v_a_2039_);
v___x_2041_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
size_t v___x_2042_; size_t v___x_2043_; 
v___x_2042_ = ((size_t)1ULL);
v___x_2043_ = lean_usize_add(v_i_2023_, v___x_2042_);
v_i_2023_ = v___x_2043_;
v_b_2024_ = v___x_2041_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_2061_, lean_object* v_as_2062_, lean_object* v_sz_2063_, lean_object* v_i_2064_, lean_object* v_b_2065_){
_start:
{
size_t v_sz_boxed_2066_; size_t v_i_boxed_2067_; lean_object* v_res_2068_; 
v_sz_boxed_2066_ = lean_unbox_usize(v_sz_2063_);
lean_dec(v_sz_2063_);
v_i_boxed_2067_ = lean_unbox_usize(v_i_2064_);
lean_dec(v_i_2064_);
v_res_2068_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2061_, v_as_2062_, v_sz_boxed_2066_, v_i_boxed_2067_, v_b_2065_);
lean_dec_ref(v_as_2062_);
lean_dec(v_x_2061_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(lean_object* v_x_2069_, lean_object* v_as_2070_, size_t v_sz_2071_, size_t v_i_2072_, lean_object* v_b_2073_){
_start:
{
uint8_t v___x_2074_; 
v___x_2074_ = lean_usize_dec_lt(v_i_2072_, v_sz_2071_);
if (v___x_2074_ == 0)
{
return v_b_2073_;
}
else
{
lean_object* v_snd_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2108_; 
v_snd_2075_ = lean_ctor_get(v_b_2073_, 1);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_b_2073_);
if (v_isSharedCheck_2108_ == 0)
{
lean_object* v_unused_2109_; 
v_unused_2109_ = lean_ctor_get(v_b_2073_, 0);
lean_dec(v_unused_2109_);
v___x_2077_ = v_b_2073_;
v_isShared_2078_ = v_isSharedCheck_2108_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_snd_2075_);
lean_dec(v_b_2073_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2108_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v_fst_2079_; lean_object* v_snd_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2107_; 
v_fst_2079_ = lean_ctor_get(v_snd_2075_, 0);
v_snd_2080_ = lean_ctor_get(v_snd_2075_, 1);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_snd_2075_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2082_ = v_snd_2075_;
v_isShared_2083_ = v_isSharedCheck_2107_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_snd_2080_);
lean_inc(v_fst_2079_);
lean_dec(v_snd_2075_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2107_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v_a_2084_; lean_object* v_p_2085_; lean_object* v___x_2086_; lean_object* v_a_2088_; lean_object* v_b_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; 
v_a_2084_ = lean_array_uget_borrowed(v_as_2070_, v_i_2072_);
v_p_2085_ = lean_ctor_get(v_a_2084_, 0);
v___x_2086_ = lean_box(0);
v_b_2095_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2085_, v_x_2069_);
v___x_2096_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2097_ = lean_int_dec_eq(v_b_2095_, v___x_2096_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2099_; 
lean_inc(v_a_2084_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 1, v_a_2084_);
lean_ctor_set(v___x_2077_, 0, v_b_2095_);
v___x_2099_ = v___x_2077_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_b_2095_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_a_2084_);
v___x_2099_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v_todo_2100_; lean_object* v___x_2101_; 
v_todo_2100_ = lean_array_push(v_snd_2080_, v___x_2099_);
v___x_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2101_, 0, v_fst_2079_);
lean_ctor_set(v___x_2101_, 1, v_todo_2100_);
v_a_2088_ = v___x_2101_;
goto v___jp_2087_;
}
}
else
{
lean_object* v_cs_x27_2103_; lean_object* v___x_2105_; 
lean_dec(v_b_2095_);
lean_inc(v_a_2084_);
v_cs_x27_2103_ = l_Lean_PersistentArray_push___redArg(v_fst_2079_, v_a_2084_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 1, v_snd_2080_);
lean_ctor_set(v___x_2077_, 0, v_cs_x27_2103_);
v___x_2105_ = v___x_2077_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_cs_x27_2103_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_snd_2080_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
v_a_2088_ = v___x_2105_;
goto v___jp_2087_;
}
}
v___jp_2087_:
{
lean_object* v___x_2090_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 1, v_a_2088_);
lean_ctor_set(v___x_2082_, 0, v___x_2086_);
v___x_2090_ = v___x_2082_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_a_2088_);
v___x_2090_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
size_t v___x_2091_; size_t v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = ((size_t)1ULL);
v___x_2092_ = lean_usize_add(v_i_2072_, v___x_2091_);
v___x_2093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2069_, v_as_2070_, v_sz_2071_, v___x_2092_, v___x_2090_);
return v___x_2093_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2110_, lean_object* v_as_2111_, lean_object* v_sz_2112_, lean_object* v_i_2113_, lean_object* v_b_2114_){
_start:
{
size_t v_sz_boxed_2115_; size_t v_i_boxed_2116_; lean_object* v_res_2117_; 
v_sz_boxed_2115_ = lean_unbox_usize(v_sz_2112_);
lean_dec(v_sz_2112_);
v_i_boxed_2116_ = lean_unbox_usize(v_i_2113_);
lean_dec(v_i_2113_);
v_res_2117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2110_, v_as_2111_, v_sz_boxed_2115_, v_i_boxed_2116_, v_b_2114_);
lean_dec_ref(v_as_2111_);
lean_dec(v_x_2110_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_2118_, lean_object* v_as_2119_, size_t v_sz_2120_, size_t v_i_2121_, lean_object* v_b_2122_){
_start:
{
uint8_t v___x_2123_; 
v___x_2123_ = lean_usize_dec_lt(v_i_2121_, v_sz_2120_);
if (v___x_2123_ == 0)
{
return v_b_2122_;
}
else
{
lean_object* v_snd_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2157_; 
v_snd_2124_ = lean_ctor_get(v_b_2122_, 1);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_b_2122_);
if (v_isSharedCheck_2157_ == 0)
{
lean_object* v_unused_2158_; 
v_unused_2158_ = lean_ctor_get(v_b_2122_, 0);
lean_dec(v_unused_2158_);
v___x_2126_ = v_b_2122_;
v_isShared_2127_ = v_isSharedCheck_2157_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_snd_2124_);
lean_dec(v_b_2122_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2157_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v_fst_2128_; lean_object* v_snd_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2156_; 
v_fst_2128_ = lean_ctor_get(v_snd_2124_, 0);
v_snd_2129_ = lean_ctor_get(v_snd_2124_, 1);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_snd_2124_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2131_ = v_snd_2124_;
v_isShared_2132_ = v_isSharedCheck_2156_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_snd_2129_);
lean_inc(v_fst_2128_);
lean_dec(v_snd_2124_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2156_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v_a_2133_; lean_object* v_p_2134_; lean_object* v___x_2135_; lean_object* v_a_2137_; lean_object* v_b_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v_a_2133_ = lean_array_uget_borrowed(v_as_2119_, v_i_2121_);
v_p_2134_ = lean_ctor_get(v_a_2133_, 0);
v___x_2135_ = lean_box(0);
v_b_2144_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2134_, v_x_2118_);
v___x_2145_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2146_ = lean_int_dec_eq(v_b_2144_, v___x_2145_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2148_; 
lean_inc(v_a_2133_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 1, v_a_2133_);
lean_ctor_set(v___x_2126_, 0, v_b_2144_);
v___x_2148_ = v___x_2126_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_b_2144_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v_a_2133_);
v___x_2148_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v_todo_2149_; lean_object* v___x_2150_; 
v_todo_2149_ = lean_array_push(v_snd_2129_, v___x_2148_);
v___x_2150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2150_, 0, v_fst_2128_);
lean_ctor_set(v___x_2150_, 1, v_todo_2149_);
v_a_2137_ = v___x_2150_;
goto v___jp_2136_;
}
}
else
{
lean_object* v_cs_x27_2152_; lean_object* v___x_2154_; 
lean_dec(v_b_2144_);
lean_inc(v_a_2133_);
v_cs_x27_2152_ = l_Lean_PersistentArray_push___redArg(v_fst_2128_, v_a_2133_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 1, v_snd_2129_);
lean_ctor_set(v___x_2126_, 0, v_cs_x27_2152_);
v___x_2154_ = v___x_2126_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_cs_x27_2152_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_snd_2129_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
v_a_2137_ = v___x_2154_;
goto v___jp_2136_;
}
}
v___jp_2136_:
{
lean_object* v___x_2139_; 
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 1, v_a_2137_);
lean_ctor_set(v___x_2131_, 0, v___x_2135_);
v___x_2139_ = v___x_2131_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2135_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_a_2137_);
v___x_2139_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
size_t v___x_2140_; size_t v___x_2141_; 
v___x_2140_ = ((size_t)1ULL);
v___x_2141_ = lean_usize_add(v_i_2121_, v___x_2140_);
v_i_2121_ = v___x_2141_;
v_b_2122_ = v___x_2139_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_2159_, lean_object* v_as_2160_, lean_object* v_sz_2161_, lean_object* v_i_2162_, lean_object* v_b_2163_){
_start:
{
size_t v_sz_boxed_2164_; size_t v_i_boxed_2165_; lean_object* v_res_2166_; 
v_sz_boxed_2164_ = lean_unbox_usize(v_sz_2161_);
lean_dec(v_sz_2161_);
v_i_boxed_2165_ = lean_unbox_usize(v_i_2162_);
lean_dec(v_i_2162_);
v_res_2166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2159_, v_as_2160_, v_sz_boxed_2164_, v_i_boxed_2165_, v_b_2163_);
lean_dec_ref(v_as_2160_);
lean_dec(v_x_2159_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2167_, lean_object* v_as_2168_, size_t v_sz_2169_, size_t v_i_2170_, lean_object* v_b_2171_){
_start:
{
uint8_t v___x_2172_; 
v___x_2172_ = lean_usize_dec_lt(v_i_2170_, v_sz_2169_);
if (v___x_2172_ == 0)
{
return v_b_2171_;
}
else
{
lean_object* v_snd_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2206_; 
v_snd_2173_ = lean_ctor_get(v_b_2171_, 1);
v_isSharedCheck_2206_ = !lean_is_exclusive(v_b_2171_);
if (v_isSharedCheck_2206_ == 0)
{
lean_object* v_unused_2207_; 
v_unused_2207_ = lean_ctor_get(v_b_2171_, 0);
lean_dec(v_unused_2207_);
v___x_2175_ = v_b_2171_;
v_isShared_2176_ = v_isSharedCheck_2206_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_snd_2173_);
lean_dec(v_b_2171_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2206_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v_fst_2177_; lean_object* v_snd_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2205_; 
v_fst_2177_ = lean_ctor_get(v_snd_2173_, 0);
v_snd_2178_ = lean_ctor_get(v_snd_2173_, 1);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_snd_2173_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2180_ = v_snd_2173_;
v_isShared_2181_ = v_isSharedCheck_2205_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_snd_2178_);
lean_inc(v_fst_2177_);
lean_dec(v_snd_2173_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2205_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v_a_2182_; lean_object* v_p_2183_; lean_object* v___x_2184_; lean_object* v_a_2186_; lean_object* v_b_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
v_a_2182_ = lean_array_uget_borrowed(v_as_2168_, v_i_2170_);
v_p_2183_ = lean_ctor_get(v_a_2182_, 0);
v___x_2184_ = lean_box(0);
v_b_2193_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2183_, v_x_2167_);
v___x_2194_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2195_ = lean_int_dec_eq(v_b_2193_, v___x_2194_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2197_; 
lean_inc(v_a_2182_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 1, v_a_2182_);
lean_ctor_set(v___x_2175_, 0, v_b_2193_);
v___x_2197_ = v___x_2175_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_b_2193_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_a_2182_);
v___x_2197_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v_todo_2198_; lean_object* v___x_2199_; 
v_todo_2198_ = lean_array_push(v_snd_2178_, v___x_2197_);
v___x_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2199_, 0, v_fst_2177_);
lean_ctor_set(v___x_2199_, 1, v_todo_2198_);
v_a_2186_ = v___x_2199_;
goto v___jp_2185_;
}
}
else
{
lean_object* v_cs_x27_2201_; lean_object* v___x_2203_; 
lean_dec(v_b_2193_);
lean_inc(v_a_2182_);
v_cs_x27_2201_ = l_Lean_PersistentArray_push___redArg(v_fst_2177_, v_a_2182_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 1, v_snd_2178_);
lean_ctor_set(v___x_2175_, 0, v_cs_x27_2201_);
v___x_2203_ = v___x_2175_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_cs_x27_2201_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_snd_2178_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
v_a_2186_ = v___x_2203_;
goto v___jp_2185_;
}
}
v___jp_2185_:
{
lean_object* v___x_2188_; 
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 1, v_a_2186_);
lean_ctor_set(v___x_2180_, 0, v___x_2184_);
v___x_2188_ = v___x_2180_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2184_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_a_2186_);
v___x_2188_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
size_t v___x_2189_; size_t v___x_2190_; lean_object* v___x_2191_; 
v___x_2189_ = ((size_t)1ULL);
v___x_2190_ = lean_usize_add(v_i_2170_, v___x_2189_);
v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2167_, v_as_2168_, v_sz_2169_, v___x_2190_, v___x_2188_);
return v___x_2191_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_2208_, lean_object* v_as_2209_, lean_object* v_sz_2210_, lean_object* v_i_2211_, lean_object* v_b_2212_){
_start:
{
size_t v_sz_boxed_2213_; size_t v_i_boxed_2214_; lean_object* v_res_2215_; 
v_sz_boxed_2213_ = lean_unbox_usize(v_sz_2210_);
lean_dec(v_sz_2210_);
v_i_boxed_2214_ = lean_unbox_usize(v_i_2211_);
lean_dec(v_i_2211_);
v_res_2215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2208_, v_as_2209_, v_sz_boxed_2213_, v_i_boxed_2214_, v_b_2212_);
lean_dec_ref(v_as_2209_);
lean_dec(v_x_2208_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(lean_object* v_init_2216_, lean_object* v_x_2217_, lean_object* v_n_2218_, lean_object* v_b_2219_){
_start:
{
if (lean_obj_tag(v_n_2218_) == 0)
{
lean_object* v_cs_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; size_t v_sz_2223_; size_t v___x_2224_; lean_object* v___x_2225_; lean_object* v_fst_2226_; 
v_cs_2220_ = lean_ctor_get(v_n_2218_, 0);
v___x_2221_ = lean_box(0);
v___x_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
lean_ctor_set(v___x_2222_, 1, v_b_2219_);
v_sz_2223_ = lean_array_size(v_cs_2220_);
v___x_2224_ = ((size_t)0ULL);
v___x_2225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2216_, v_x_2217_, v_cs_2220_, v_sz_2223_, v___x_2224_, v___x_2222_);
v_fst_2226_ = lean_ctor_get(v___x_2225_, 0);
if (lean_obj_tag(v_fst_2226_) == 0)
{
lean_object* v_snd_2227_; lean_object* v___x_2228_; 
v_snd_2227_ = lean_ctor_get(v___x_2225_, 1);
lean_inc(v_snd_2227_);
lean_dec_ref(v___x_2225_);
v___x_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2228_, 0, v_snd_2227_);
return v___x_2228_;
}
else
{
lean_object* v_val_2229_; 
lean_inc_ref(v_fst_2226_);
lean_dec_ref(v___x_2225_);
v_val_2229_ = lean_ctor_get(v_fst_2226_, 0);
lean_inc(v_val_2229_);
lean_dec_ref_known(v_fst_2226_, 1);
return v_val_2229_;
}
}
else
{
lean_object* v_vs_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; size_t v_sz_2233_; size_t v___x_2234_; lean_object* v___x_2235_; lean_object* v_fst_2236_; 
v_vs_2230_ = lean_ctor_get(v_n_2218_, 0);
v___x_2231_ = lean_box(0);
v___x_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v_b_2219_);
v_sz_2233_ = lean_array_size(v_vs_2230_);
v___x_2234_ = ((size_t)0ULL);
v___x_2235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2217_, v_vs_2230_, v_sz_2233_, v___x_2234_, v___x_2232_);
v_fst_2236_ = lean_ctor_get(v___x_2235_, 0);
if (lean_obj_tag(v_fst_2236_) == 0)
{
lean_object* v_snd_2237_; lean_object* v___x_2238_; 
v_snd_2237_ = lean_ctor_get(v___x_2235_, 1);
lean_inc(v_snd_2237_);
lean_dec_ref(v___x_2235_);
v___x_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2238_, 0, v_snd_2237_);
return v___x_2238_;
}
else
{
lean_object* v_val_2239_; 
lean_inc_ref(v_fst_2236_);
lean_dec_ref(v___x_2235_);
v_val_2239_ = lean_ctor_get(v_fst_2236_, 0);
lean_inc(v_val_2239_);
lean_dec_ref_known(v_fst_2236_, 1);
return v_val_2239_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_2240_, lean_object* v_x_2241_, lean_object* v_as_2242_, size_t v_sz_2243_, size_t v_i_2244_, lean_object* v_b_2245_){
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
lean_object* v_snd_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2265_; 
v_snd_2247_ = lean_ctor_get(v_b_2245_, 1);
v_isSharedCheck_2265_ = !lean_is_exclusive(v_b_2245_);
if (v_isSharedCheck_2265_ == 0)
{
lean_object* v_unused_2266_; 
v_unused_2266_ = lean_ctor_get(v_b_2245_, 0);
lean_dec(v_unused_2266_);
v___x_2249_ = v_b_2245_;
v_isShared_2250_ = v_isSharedCheck_2265_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_snd_2247_);
lean_dec(v_b_2245_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2265_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v_a_2251_; lean_object* v___x_2252_; 
v_a_2251_ = lean_array_uget_borrowed(v_as_2242_, v_i_2244_);
lean_inc(v_snd_2247_);
v___x_2252_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2240_, v_x_2241_, v_a_2251_, v_snd_2247_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v___x_2253_; lean_object* v___x_2255_; 
v___x_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 0, v___x_2253_);
v___x_2255_ = v___x_2249_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2253_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_snd_2247_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2258_; lean_object* v___x_2260_; 
lean_dec(v_snd_2247_);
v_a_2257_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___x_2252_, 1);
v___x_2258_ = lean_box(0);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 1, v_a_2257_);
lean_ctor_set(v___x_2249_, 0, v___x_2258_);
v___x_2260_ = v___x_2249_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_a_2257_);
v___x_2260_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
size_t v___x_2261_; size_t v___x_2262_; 
v___x_2261_ = ((size_t)1ULL);
v___x_2262_ = lean_usize_add(v_i_2244_, v___x_2261_);
v_i_2244_ = v___x_2262_;
v_b_2245_ = v___x_2260_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_2267_, lean_object* v_x_2268_, lean_object* v_as_2269_, lean_object* v_sz_2270_, lean_object* v_i_2271_, lean_object* v_b_2272_){
_start:
{
size_t v_sz_boxed_2273_; size_t v_i_boxed_2274_; lean_object* v_res_2275_; 
v_sz_boxed_2273_ = lean_unbox_usize(v_sz_2270_);
lean_dec(v_sz_2270_);
v_i_boxed_2274_ = lean_unbox_usize(v_i_2271_);
lean_dec(v_i_2271_);
v_res_2275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2267_, v_x_2268_, v_as_2269_, v_sz_boxed_2273_, v_i_boxed_2274_, v_b_2272_);
lean_dec_ref(v_as_2269_);
lean_dec(v_x_2268_);
lean_dec_ref(v_init_2267_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_2276_, lean_object* v_x_2277_, lean_object* v_n_2278_, lean_object* v_b_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2276_, v_x_2277_, v_n_2278_, v_b_2279_);
lean_dec_ref(v_n_2278_);
lean_dec(v_x_2277_);
lean_dec_ref(v_init_2276_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(lean_object* v_x_2281_, lean_object* v_t_2282_, lean_object* v_init_2283_){
_start:
{
lean_object* v_root_2284_; lean_object* v_tail_2285_; lean_object* v___x_2286_; 
v_root_2284_ = lean_ctor_get(v_t_2282_, 0);
v_tail_2285_ = lean_ctor_get(v_t_2282_, 1);
lean_inc_ref(v_init_2283_);
v___x_2286_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2283_, v_x_2281_, v_root_2284_, v_init_2283_);
lean_dec_ref(v_init_2283_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v___x_2286_, 1);
return v_a_2287_;
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; size_t v_sz_2291_; size_t v___x_2292_; lean_object* v___x_2293_; lean_object* v_fst_2294_; 
v_a_2288_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2286_, 1);
v___x_2289_ = lean_box(0);
v___x_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
lean_ctor_set(v___x_2290_, 1, v_a_2288_);
v_sz_2291_ = lean_array_size(v_tail_2285_);
v___x_2292_ = ((size_t)0ULL);
v___x_2293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2281_, v_tail_2285_, v_sz_2291_, v___x_2292_, v___x_2290_);
v_fst_2294_ = lean_ctor_get(v___x_2293_, 0);
if (lean_obj_tag(v_fst_2294_) == 0)
{
lean_object* v_snd_2295_; 
v_snd_2295_ = lean_ctor_get(v___x_2293_, 1);
lean_inc(v_snd_2295_);
lean_dec_ref(v___x_2293_);
return v_snd_2295_;
}
else
{
lean_object* v_val_2296_; 
lean_inc_ref(v_fst_2294_);
lean_dec_ref(v___x_2293_);
v_val_2296_ = lean_ctor_get(v_fst_2294_, 0);
lean_inc(v_val_2296_);
lean_dec_ref_known(v_fst_2294_, 1);
return v_val_2296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0___boxed(lean_object* v_x_2297_, lean_object* v_t_2298_, lean_object* v_init_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2297_, v_t_2298_, v_init_2299_);
lean_dec_ref(v_t_2298_);
lean_dec(v_x_2297_);
return v_res_2300_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2301_ = lean_unsigned_to_nat(32u);
v___x_2302_ = lean_mk_empty_array_with_capacity(v___x_2301_);
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
return v___x_2303_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1(void){
_start:
{
size_t v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v_cs_x27_2309_; 
v___x_2304_ = ((size_t)5ULL);
v___x_2305_ = lean_unsigned_to_nat(0u);
v___x_2306_ = lean_unsigned_to_nat(32u);
v___x_2307_ = lean_mk_empty_array_with_capacity(v___x_2306_);
v___x_2308_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0);
v_cs_x27_2309_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_2309_, 0, v___x_2308_);
lean_ctor_set(v_cs_x27_2309_, 1, v___x_2307_);
lean_ctor_set(v_cs_x27_2309_, 2, v___x_2305_);
lean_ctor_set(v_cs_x27_2309_, 3, v___x_2305_);
lean_ctor_set_usize(v_cs_x27_2309_, 4, v___x_2304_);
return v_cs_x27_2309_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_2312_; lean_object* v_cs_x27_2313_; lean_object* v___x_2314_; 
v_todo_2312_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2));
v_cs_x27_2313_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1);
v___x_2314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2314_, 0, v_cs_x27_2313_);
lean_ctor_set(v___x_2314_, 1, v_todo_2312_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(lean_object* v_x_2315_, lean_object* v_cs_2316_){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v_fst_2319_; lean_object* v_snd_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
v___x_2317_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3);
v___x_2318_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2315_, v_cs_2316_, v___x_2317_);
v_fst_2319_ = lean_ctor_get(v___x_2318_, 0);
v_snd_2320_ = lean_ctor_get(v___x_2318_, 1);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2318_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_snd_2320_);
lean_inc(v_fst_2319_);
lean_dec(v___x_2318_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_fst_2319_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_snd_2320_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___boxed(lean_object* v_x_2328_, lean_object* v_cs_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2328_, v_cs_2329_);
lean_dec_ref(v_cs_2329_);
lean_dec(v_x_2328_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object* v_x_2331_, lean_object* v_cs_2332_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2331_, v_cs_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___boxed(lean_object* v_x_2334_, lean_object* v_cs_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(v_x_2334_, v_cs_2335_);
lean_dec_ref(v_cs_2335_);
lean_dec(v_x_2334_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(lean_object* v_a_2337_, lean_object* v_y_2338_, lean_object* v_fst_2339_, lean_object* v_s_2340_){
_start:
{
lean_object* v_structs_2341_; lean_object* v_typeIdOf_2342_; lean_object* v_exprToStructId_2343_; lean_object* v_exprToStructIdEntries_2344_; lean_object* v_forbiddenNatModules_2345_; lean_object* v_natStructs_2346_; lean_object* v_natTypeIdOf_2347_; lean_object* v_exprToNatStructId_2348_; lean_object* v___x_2349_; uint8_t v___x_2350_; 
v_structs_2341_ = lean_ctor_get(v_s_2340_, 0);
v_typeIdOf_2342_ = lean_ctor_get(v_s_2340_, 1);
v_exprToStructId_2343_ = lean_ctor_get(v_s_2340_, 2);
v_exprToStructIdEntries_2344_ = lean_ctor_get(v_s_2340_, 3);
v_forbiddenNatModules_2345_ = lean_ctor_get(v_s_2340_, 4);
v_natStructs_2346_ = lean_ctor_get(v_s_2340_, 5);
v_natTypeIdOf_2347_ = lean_ctor_get(v_s_2340_, 6);
v_exprToNatStructId_2348_ = lean_ctor_get(v_s_2340_, 7);
v___x_2349_ = lean_array_get_size(v_structs_2341_);
v___x_2350_ = lean_nat_dec_lt(v_a_2337_, v___x_2349_);
if (v___x_2350_ == 0)
{
lean_dec_ref(v_fst_2339_);
return v_s_2340_;
}
else
{
lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2412_; 
lean_inc_ref(v_exprToNatStructId_2348_);
lean_inc_ref(v_natTypeIdOf_2347_);
lean_inc_ref(v_natStructs_2346_);
lean_inc_ref(v_forbiddenNatModules_2345_);
lean_inc_ref(v_exprToStructIdEntries_2344_);
lean_inc_ref(v_exprToStructId_2343_);
lean_inc_ref(v_typeIdOf_2342_);
lean_inc_ref(v_structs_2341_);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_s_2340_);
if (v_isSharedCheck_2412_ == 0)
{
lean_object* v_unused_2413_; lean_object* v_unused_2414_; lean_object* v_unused_2415_; lean_object* v_unused_2416_; lean_object* v_unused_2417_; lean_object* v_unused_2418_; lean_object* v_unused_2419_; lean_object* v_unused_2420_; 
v_unused_2413_ = lean_ctor_get(v_s_2340_, 7);
lean_dec(v_unused_2413_);
v_unused_2414_ = lean_ctor_get(v_s_2340_, 6);
lean_dec(v_unused_2414_);
v_unused_2415_ = lean_ctor_get(v_s_2340_, 5);
lean_dec(v_unused_2415_);
v_unused_2416_ = lean_ctor_get(v_s_2340_, 4);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v_s_2340_, 3);
lean_dec(v_unused_2417_);
v_unused_2418_ = lean_ctor_get(v_s_2340_, 2);
lean_dec(v_unused_2418_);
v_unused_2419_ = lean_ctor_get(v_s_2340_, 1);
lean_dec(v_unused_2419_);
v_unused_2420_ = lean_ctor_get(v_s_2340_, 0);
lean_dec(v_unused_2420_);
v___x_2352_ = v_s_2340_;
v_isShared_2353_ = v_isSharedCheck_2412_;
goto v_resetjp_2351_;
}
else
{
lean_dec(v_s_2340_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2412_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v_v_2354_; lean_object* v_id_2355_; lean_object* v_ringId_x3f_2356_; lean_object* v_type_2357_; lean_object* v_u_2358_; lean_object* v_intModuleInst_2359_; lean_object* v_leInst_x3f_2360_; lean_object* v_ltInst_x3f_2361_; lean_object* v_lawfulOrderLTInst_x3f_2362_; lean_object* v_isPreorderInst_x3f_2363_; lean_object* v_orderedAddInst_x3f_2364_; lean_object* v_isLinearInst_x3f_2365_; lean_object* v_noNatDivInst_x3f_2366_; lean_object* v_ringInst_x3f_2367_; lean_object* v_commRingInst_x3f_2368_; lean_object* v_orderedRingInst_x3f_2369_; lean_object* v_fieldInst_x3f_2370_; lean_object* v_charInst_x3f_2371_; lean_object* v_zero_2372_; lean_object* v_ofNatZero_2373_; lean_object* v_one_x3f_2374_; lean_object* v_leFn_x3f_2375_; lean_object* v_ltFn_x3f_2376_; lean_object* v_addFn_2377_; lean_object* v_zsmulFn_2378_; lean_object* v_nsmulFn_2379_; lean_object* v_zsmulFn_x3f_2380_; lean_object* v_nsmulFn_x3f_2381_; lean_object* v_homomulFn_x3f_2382_; lean_object* v_subFn_2383_; lean_object* v_negFn_2384_; lean_object* v_vars_2385_; lean_object* v_varMap_2386_; lean_object* v_lowers_2387_; lean_object* v_uppers_2388_; lean_object* v_diseqs_2389_; lean_object* v_assignment_2390_; uint8_t v_caseSplits_2391_; lean_object* v_conflict_x3f_2392_; lean_object* v_diseqSplits_2393_; lean_object* v_elimEqs_2394_; lean_object* v_elimStack_2395_; lean_object* v_occurs_2396_; lean_object* v_ignored_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2411_; 
v_v_2354_ = lean_array_fget(v_structs_2341_, v_a_2337_);
v_id_2355_ = lean_ctor_get(v_v_2354_, 0);
v_ringId_x3f_2356_ = lean_ctor_get(v_v_2354_, 1);
v_type_2357_ = lean_ctor_get(v_v_2354_, 2);
v_u_2358_ = lean_ctor_get(v_v_2354_, 3);
v_intModuleInst_2359_ = lean_ctor_get(v_v_2354_, 4);
v_leInst_x3f_2360_ = lean_ctor_get(v_v_2354_, 5);
v_ltInst_x3f_2361_ = lean_ctor_get(v_v_2354_, 6);
v_lawfulOrderLTInst_x3f_2362_ = lean_ctor_get(v_v_2354_, 7);
v_isPreorderInst_x3f_2363_ = lean_ctor_get(v_v_2354_, 8);
v_orderedAddInst_x3f_2364_ = lean_ctor_get(v_v_2354_, 9);
v_isLinearInst_x3f_2365_ = lean_ctor_get(v_v_2354_, 10);
v_noNatDivInst_x3f_2366_ = lean_ctor_get(v_v_2354_, 11);
v_ringInst_x3f_2367_ = lean_ctor_get(v_v_2354_, 12);
v_commRingInst_x3f_2368_ = lean_ctor_get(v_v_2354_, 13);
v_orderedRingInst_x3f_2369_ = lean_ctor_get(v_v_2354_, 14);
v_fieldInst_x3f_2370_ = lean_ctor_get(v_v_2354_, 15);
v_charInst_x3f_2371_ = lean_ctor_get(v_v_2354_, 16);
v_zero_2372_ = lean_ctor_get(v_v_2354_, 17);
v_ofNatZero_2373_ = lean_ctor_get(v_v_2354_, 18);
v_one_x3f_2374_ = lean_ctor_get(v_v_2354_, 19);
v_leFn_x3f_2375_ = lean_ctor_get(v_v_2354_, 20);
v_ltFn_x3f_2376_ = lean_ctor_get(v_v_2354_, 21);
v_addFn_2377_ = lean_ctor_get(v_v_2354_, 22);
v_zsmulFn_2378_ = lean_ctor_get(v_v_2354_, 23);
v_nsmulFn_2379_ = lean_ctor_get(v_v_2354_, 24);
v_zsmulFn_x3f_2380_ = lean_ctor_get(v_v_2354_, 25);
v_nsmulFn_x3f_2381_ = lean_ctor_get(v_v_2354_, 26);
v_homomulFn_x3f_2382_ = lean_ctor_get(v_v_2354_, 27);
v_subFn_2383_ = lean_ctor_get(v_v_2354_, 28);
v_negFn_2384_ = lean_ctor_get(v_v_2354_, 29);
v_vars_2385_ = lean_ctor_get(v_v_2354_, 30);
v_varMap_2386_ = lean_ctor_get(v_v_2354_, 31);
v_lowers_2387_ = lean_ctor_get(v_v_2354_, 32);
v_uppers_2388_ = lean_ctor_get(v_v_2354_, 33);
v_diseqs_2389_ = lean_ctor_get(v_v_2354_, 34);
v_assignment_2390_ = lean_ctor_get(v_v_2354_, 35);
v_caseSplits_2391_ = lean_ctor_get_uint8(v_v_2354_, sizeof(void*)*42);
v_conflict_x3f_2392_ = lean_ctor_get(v_v_2354_, 36);
v_diseqSplits_2393_ = lean_ctor_get(v_v_2354_, 37);
v_elimEqs_2394_ = lean_ctor_get(v_v_2354_, 38);
v_elimStack_2395_ = lean_ctor_get(v_v_2354_, 39);
v_occurs_2396_ = lean_ctor_get(v_v_2354_, 40);
v_ignored_2397_ = lean_ctor_get(v_v_2354_, 41);
v_isSharedCheck_2411_ = !lean_is_exclusive(v_v_2354_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2399_ = v_v_2354_;
v_isShared_2400_ = v_isSharedCheck_2411_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_ignored_2397_);
lean_inc(v_occurs_2396_);
lean_inc(v_elimStack_2395_);
lean_inc(v_elimEqs_2394_);
lean_inc(v_diseqSplits_2393_);
lean_inc(v_conflict_x3f_2392_);
lean_inc(v_assignment_2390_);
lean_inc(v_diseqs_2389_);
lean_inc(v_uppers_2388_);
lean_inc(v_lowers_2387_);
lean_inc(v_varMap_2386_);
lean_inc(v_vars_2385_);
lean_inc(v_negFn_2384_);
lean_inc(v_subFn_2383_);
lean_inc(v_homomulFn_x3f_2382_);
lean_inc(v_nsmulFn_x3f_2381_);
lean_inc(v_zsmulFn_x3f_2380_);
lean_inc(v_nsmulFn_2379_);
lean_inc(v_zsmulFn_2378_);
lean_inc(v_addFn_2377_);
lean_inc(v_ltFn_x3f_2376_);
lean_inc(v_leFn_x3f_2375_);
lean_inc(v_one_x3f_2374_);
lean_inc(v_ofNatZero_2373_);
lean_inc(v_zero_2372_);
lean_inc(v_charInst_x3f_2371_);
lean_inc(v_fieldInst_x3f_2370_);
lean_inc(v_orderedRingInst_x3f_2369_);
lean_inc(v_commRingInst_x3f_2368_);
lean_inc(v_ringInst_x3f_2367_);
lean_inc(v_noNatDivInst_x3f_2366_);
lean_inc(v_isLinearInst_x3f_2365_);
lean_inc(v_orderedAddInst_x3f_2364_);
lean_inc(v_isPreorderInst_x3f_2363_);
lean_inc(v_lawfulOrderLTInst_x3f_2362_);
lean_inc(v_ltInst_x3f_2361_);
lean_inc(v_leInst_x3f_2360_);
lean_inc(v_intModuleInst_2359_);
lean_inc(v_u_2358_);
lean_inc(v_type_2357_);
lean_inc(v_ringId_x3f_2356_);
lean_inc(v_id_2355_);
lean_dec(v_v_2354_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2411_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; lean_object* v_xs_x27_2402_; lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2401_ = lean_box(0);
v_xs_x27_2402_ = lean_array_fset(v_structs_2341_, v_a_2337_, v___x_2401_);
v___x_2403_ = l_Lean_PersistentArray_set___redArg(v_lowers_2387_, v_y_2338_, v_fst_2339_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 32, v___x_2403_);
v___x_2405_ = v___x_2399_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_id_2355_);
lean_ctor_set(v_reuseFailAlloc_2410_, 1, v_ringId_x3f_2356_);
lean_ctor_set(v_reuseFailAlloc_2410_, 2, v_type_2357_);
lean_ctor_set(v_reuseFailAlloc_2410_, 3, v_u_2358_);
lean_ctor_set(v_reuseFailAlloc_2410_, 4, v_intModuleInst_2359_);
lean_ctor_set(v_reuseFailAlloc_2410_, 5, v_leInst_x3f_2360_);
lean_ctor_set(v_reuseFailAlloc_2410_, 6, v_ltInst_x3f_2361_);
lean_ctor_set(v_reuseFailAlloc_2410_, 7, v_lawfulOrderLTInst_x3f_2362_);
lean_ctor_set(v_reuseFailAlloc_2410_, 8, v_isPreorderInst_x3f_2363_);
lean_ctor_set(v_reuseFailAlloc_2410_, 9, v_orderedAddInst_x3f_2364_);
lean_ctor_set(v_reuseFailAlloc_2410_, 10, v_isLinearInst_x3f_2365_);
lean_ctor_set(v_reuseFailAlloc_2410_, 11, v_noNatDivInst_x3f_2366_);
lean_ctor_set(v_reuseFailAlloc_2410_, 12, v_ringInst_x3f_2367_);
lean_ctor_set(v_reuseFailAlloc_2410_, 13, v_commRingInst_x3f_2368_);
lean_ctor_set(v_reuseFailAlloc_2410_, 14, v_orderedRingInst_x3f_2369_);
lean_ctor_set(v_reuseFailAlloc_2410_, 15, v_fieldInst_x3f_2370_);
lean_ctor_set(v_reuseFailAlloc_2410_, 16, v_charInst_x3f_2371_);
lean_ctor_set(v_reuseFailAlloc_2410_, 17, v_zero_2372_);
lean_ctor_set(v_reuseFailAlloc_2410_, 18, v_ofNatZero_2373_);
lean_ctor_set(v_reuseFailAlloc_2410_, 19, v_one_x3f_2374_);
lean_ctor_set(v_reuseFailAlloc_2410_, 20, v_leFn_x3f_2375_);
lean_ctor_set(v_reuseFailAlloc_2410_, 21, v_ltFn_x3f_2376_);
lean_ctor_set(v_reuseFailAlloc_2410_, 22, v_addFn_2377_);
lean_ctor_set(v_reuseFailAlloc_2410_, 23, v_zsmulFn_2378_);
lean_ctor_set(v_reuseFailAlloc_2410_, 24, v_nsmulFn_2379_);
lean_ctor_set(v_reuseFailAlloc_2410_, 25, v_zsmulFn_x3f_2380_);
lean_ctor_set(v_reuseFailAlloc_2410_, 26, v_nsmulFn_x3f_2381_);
lean_ctor_set(v_reuseFailAlloc_2410_, 27, v_homomulFn_x3f_2382_);
lean_ctor_set(v_reuseFailAlloc_2410_, 28, v_subFn_2383_);
lean_ctor_set(v_reuseFailAlloc_2410_, 29, v_negFn_2384_);
lean_ctor_set(v_reuseFailAlloc_2410_, 30, v_vars_2385_);
lean_ctor_set(v_reuseFailAlloc_2410_, 31, v_varMap_2386_);
lean_ctor_set(v_reuseFailAlloc_2410_, 32, v___x_2403_);
lean_ctor_set(v_reuseFailAlloc_2410_, 33, v_uppers_2388_);
lean_ctor_set(v_reuseFailAlloc_2410_, 34, v_diseqs_2389_);
lean_ctor_set(v_reuseFailAlloc_2410_, 35, v_assignment_2390_);
lean_ctor_set(v_reuseFailAlloc_2410_, 36, v_conflict_x3f_2392_);
lean_ctor_set(v_reuseFailAlloc_2410_, 37, v_diseqSplits_2393_);
lean_ctor_set(v_reuseFailAlloc_2410_, 38, v_elimEqs_2394_);
lean_ctor_set(v_reuseFailAlloc_2410_, 39, v_elimStack_2395_);
lean_ctor_set(v_reuseFailAlloc_2410_, 40, v_occurs_2396_);
lean_ctor_set(v_reuseFailAlloc_2410_, 41, v_ignored_2397_);
lean_ctor_set_uint8(v_reuseFailAlloc_2410_, sizeof(void*)*42, v_caseSplits_2391_);
v___x_2405_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2406_ = lean_array_fset(v_xs_x27_2402_, v_a_2337_, v___x_2405_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2406_);
v___x_2408_ = v___x_2352_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v_typeIdOf_2342_);
lean_ctor_set(v_reuseFailAlloc_2409_, 2, v_exprToStructId_2343_);
lean_ctor_set(v_reuseFailAlloc_2409_, 3, v_exprToStructIdEntries_2344_);
lean_ctor_set(v_reuseFailAlloc_2409_, 4, v_forbiddenNatModules_2345_);
lean_ctor_set(v_reuseFailAlloc_2409_, 5, v_natStructs_2346_);
lean_ctor_set(v_reuseFailAlloc_2409_, 6, v_natTypeIdOf_2347_);
lean_ctor_set(v_reuseFailAlloc_2409_, 7, v_exprToNatStructId_2348_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed(lean_object* v_a_2421_, lean_object* v_y_2422_, lean_object* v_fst_2423_, lean_object* v_s_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(v_a_2421_, v_y_2422_, v_fst_2423_, v_s_2424_);
lean_dec(v_y_2422_);
lean_dec(v_a_2421_);
return v_res_2425_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0(void){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object* v_a_2427_, lean_object* v_x_2428_, lean_object* v_c_2429_, lean_object* v_y_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2444_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2478_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2447_ = v___x_2444_;
v_isShared_2448_ = v_isSharedCheck_2478_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2478_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
uint8_t v___x_2449_; 
v___x_2449_ = lean_unbox(v_a_2445_);
lean_dec(v_a_2445_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; 
lean_del_object(v___x_2447_);
v___x_2450_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___y_2453_; lean_object* v_lowers_2461_; lean_object* v_size_2462_; uint8_t v___x_2463_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2451_);
lean_dec_ref_known(v___x_2450_, 1);
v_lowers_2461_ = lean_ctor_get(v_a_2451_, 32);
lean_inc_ref(v_lowers_2461_);
lean_dec(v_a_2451_);
v_size_2462_ = lean_ctor_get(v_lowers_2461_, 2);
v___x_2463_ = lean_nat_dec_lt(v_y_2430_, v_size_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; 
lean_dec_ref(v_lowers_2461_);
v___x_2464_ = l_outOfBounds___redArg(v___x_2443_);
v___y_2453_ = v___x_2464_;
goto v___jp_2452_;
}
else
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2443_, v_lowers_2461_, v_y_2430_);
lean_dec_ref(v_lowers_2461_);
v___y_2453_ = v___x_2465_;
goto v___jp_2452_;
}
v___jp_2452_:
{
lean_object* v___x_2454_; lean_object* v_fst_2455_; lean_object* v_snd_2456_; lean_object* v___f_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2454_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2428_, v___y_2453_);
lean_dec_ref(v___y_2453_);
v_fst_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_fst_2455_);
v_snd_2456_ = lean_ctor_get(v___x_2454_, 1);
lean_inc(v_snd_2456_);
lean_dec_ref(v___x_2454_);
lean_inc(v_a_2431_);
v___f_2457_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2457_, 0, v_a_2431_);
lean_closure_set(v___f_2457_, 1, v_y_2430_);
lean_closure_set(v___f_2457_, 2, v_fst_2455_);
v___x_2458_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2459_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2458_, v___f_2457_, v_a_2432_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v___x_2460_; 
lean_dec_ref_known(v___x_2459_, 1);
v___x_2460_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2427_, v_x_2428_, v_c_2429_, v_snd_2456_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_);
lean_dec(v_snd_2456_);
return v___x_2460_;
}
else
{
lean_dec(v_snd_2456_);
lean_dec_ref(v_c_2429_);
lean_dec(v_x_2428_);
lean_dec(v_a_2427_);
return v___x_2459_;
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec(v_y_2430_);
lean_dec_ref(v_c_2429_);
lean_dec(v_x_2428_);
lean_dec(v_a_2427_);
v_a_2466_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2450_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2450_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
else
{
lean_object* v___x_2474_; lean_object* v___x_2476_; 
lean_dec(v_y_2430_);
lean_dec_ref(v_c_2429_);
lean_dec(v_x_2428_);
lean_dec(v_a_2427_);
v___x_2474_ = lean_box(0);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v___x_2474_);
v___x_2476_ = v___x_2447_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec(v_y_2430_);
lean_dec_ref(v_c_2429_);
lean_dec(v_x_2428_);
lean_dec(v_a_2427_);
v_a_2479_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2444_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2444_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object* v_a_2487_, lean_object* v_x_2488_, lean_object* v_c_2489_, lean_object* v_y_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_2487_, v_x_2488_, v_c_2489_, v_y_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
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
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(lean_object* v_a_2504_, lean_object* v_y_2505_, lean_object* v_fst_2506_, lean_object* v_s_2507_){
_start:
{
lean_object* v_structs_2508_; lean_object* v_typeIdOf_2509_; lean_object* v_exprToStructId_2510_; lean_object* v_exprToStructIdEntries_2511_; lean_object* v_forbiddenNatModules_2512_; lean_object* v_natStructs_2513_; lean_object* v_natTypeIdOf_2514_; lean_object* v_exprToNatStructId_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; 
v_structs_2508_ = lean_ctor_get(v_s_2507_, 0);
v_typeIdOf_2509_ = lean_ctor_get(v_s_2507_, 1);
v_exprToStructId_2510_ = lean_ctor_get(v_s_2507_, 2);
v_exprToStructIdEntries_2511_ = lean_ctor_get(v_s_2507_, 3);
v_forbiddenNatModules_2512_ = lean_ctor_get(v_s_2507_, 4);
v_natStructs_2513_ = lean_ctor_get(v_s_2507_, 5);
v_natTypeIdOf_2514_ = lean_ctor_get(v_s_2507_, 6);
v_exprToNatStructId_2515_ = lean_ctor_get(v_s_2507_, 7);
v___x_2516_ = lean_array_get_size(v_structs_2508_);
v___x_2517_ = lean_nat_dec_lt(v_a_2504_, v___x_2516_);
if (v___x_2517_ == 0)
{
lean_dec_ref(v_fst_2506_);
return v_s_2507_;
}
else
{
lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2579_; 
lean_inc_ref(v_exprToNatStructId_2515_);
lean_inc_ref(v_natTypeIdOf_2514_);
lean_inc_ref(v_natStructs_2513_);
lean_inc_ref(v_forbiddenNatModules_2512_);
lean_inc_ref(v_exprToStructIdEntries_2511_);
lean_inc_ref(v_exprToStructId_2510_);
lean_inc_ref(v_typeIdOf_2509_);
lean_inc_ref(v_structs_2508_);
v_isSharedCheck_2579_ = !lean_is_exclusive(v_s_2507_);
if (v_isSharedCheck_2579_ == 0)
{
lean_object* v_unused_2580_; lean_object* v_unused_2581_; lean_object* v_unused_2582_; lean_object* v_unused_2583_; lean_object* v_unused_2584_; lean_object* v_unused_2585_; lean_object* v_unused_2586_; lean_object* v_unused_2587_; 
v_unused_2580_ = lean_ctor_get(v_s_2507_, 7);
lean_dec(v_unused_2580_);
v_unused_2581_ = lean_ctor_get(v_s_2507_, 6);
lean_dec(v_unused_2581_);
v_unused_2582_ = lean_ctor_get(v_s_2507_, 5);
lean_dec(v_unused_2582_);
v_unused_2583_ = lean_ctor_get(v_s_2507_, 4);
lean_dec(v_unused_2583_);
v_unused_2584_ = lean_ctor_get(v_s_2507_, 3);
lean_dec(v_unused_2584_);
v_unused_2585_ = lean_ctor_get(v_s_2507_, 2);
lean_dec(v_unused_2585_);
v_unused_2586_ = lean_ctor_get(v_s_2507_, 1);
lean_dec(v_unused_2586_);
v_unused_2587_ = lean_ctor_get(v_s_2507_, 0);
lean_dec(v_unused_2587_);
v___x_2519_ = v_s_2507_;
v_isShared_2520_ = v_isSharedCheck_2579_;
goto v_resetjp_2518_;
}
else
{
lean_dec(v_s_2507_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2579_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v_v_2521_; lean_object* v_id_2522_; lean_object* v_ringId_x3f_2523_; lean_object* v_type_2524_; lean_object* v_u_2525_; lean_object* v_intModuleInst_2526_; lean_object* v_leInst_x3f_2527_; lean_object* v_ltInst_x3f_2528_; lean_object* v_lawfulOrderLTInst_x3f_2529_; lean_object* v_isPreorderInst_x3f_2530_; lean_object* v_orderedAddInst_x3f_2531_; lean_object* v_isLinearInst_x3f_2532_; lean_object* v_noNatDivInst_x3f_2533_; lean_object* v_ringInst_x3f_2534_; lean_object* v_commRingInst_x3f_2535_; lean_object* v_orderedRingInst_x3f_2536_; lean_object* v_fieldInst_x3f_2537_; lean_object* v_charInst_x3f_2538_; lean_object* v_zero_2539_; lean_object* v_ofNatZero_2540_; lean_object* v_one_x3f_2541_; lean_object* v_leFn_x3f_2542_; lean_object* v_ltFn_x3f_2543_; lean_object* v_addFn_2544_; lean_object* v_zsmulFn_2545_; lean_object* v_nsmulFn_2546_; lean_object* v_zsmulFn_x3f_2547_; lean_object* v_nsmulFn_x3f_2548_; lean_object* v_homomulFn_x3f_2549_; lean_object* v_subFn_2550_; lean_object* v_negFn_2551_; lean_object* v_vars_2552_; lean_object* v_varMap_2553_; lean_object* v_lowers_2554_; lean_object* v_uppers_2555_; lean_object* v_diseqs_2556_; lean_object* v_assignment_2557_; uint8_t v_caseSplits_2558_; lean_object* v_conflict_x3f_2559_; lean_object* v_diseqSplits_2560_; lean_object* v_elimEqs_2561_; lean_object* v_elimStack_2562_; lean_object* v_occurs_2563_; lean_object* v_ignored_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2578_; 
v_v_2521_ = lean_array_fget(v_structs_2508_, v_a_2504_);
v_id_2522_ = lean_ctor_get(v_v_2521_, 0);
v_ringId_x3f_2523_ = lean_ctor_get(v_v_2521_, 1);
v_type_2524_ = lean_ctor_get(v_v_2521_, 2);
v_u_2525_ = lean_ctor_get(v_v_2521_, 3);
v_intModuleInst_2526_ = lean_ctor_get(v_v_2521_, 4);
v_leInst_x3f_2527_ = lean_ctor_get(v_v_2521_, 5);
v_ltInst_x3f_2528_ = lean_ctor_get(v_v_2521_, 6);
v_lawfulOrderLTInst_x3f_2529_ = lean_ctor_get(v_v_2521_, 7);
v_isPreorderInst_x3f_2530_ = lean_ctor_get(v_v_2521_, 8);
v_orderedAddInst_x3f_2531_ = lean_ctor_get(v_v_2521_, 9);
v_isLinearInst_x3f_2532_ = lean_ctor_get(v_v_2521_, 10);
v_noNatDivInst_x3f_2533_ = lean_ctor_get(v_v_2521_, 11);
v_ringInst_x3f_2534_ = lean_ctor_get(v_v_2521_, 12);
v_commRingInst_x3f_2535_ = lean_ctor_get(v_v_2521_, 13);
v_orderedRingInst_x3f_2536_ = lean_ctor_get(v_v_2521_, 14);
v_fieldInst_x3f_2537_ = lean_ctor_get(v_v_2521_, 15);
v_charInst_x3f_2538_ = lean_ctor_get(v_v_2521_, 16);
v_zero_2539_ = lean_ctor_get(v_v_2521_, 17);
v_ofNatZero_2540_ = lean_ctor_get(v_v_2521_, 18);
v_one_x3f_2541_ = lean_ctor_get(v_v_2521_, 19);
v_leFn_x3f_2542_ = lean_ctor_get(v_v_2521_, 20);
v_ltFn_x3f_2543_ = lean_ctor_get(v_v_2521_, 21);
v_addFn_2544_ = lean_ctor_get(v_v_2521_, 22);
v_zsmulFn_2545_ = lean_ctor_get(v_v_2521_, 23);
v_nsmulFn_2546_ = lean_ctor_get(v_v_2521_, 24);
v_zsmulFn_x3f_2547_ = lean_ctor_get(v_v_2521_, 25);
v_nsmulFn_x3f_2548_ = lean_ctor_get(v_v_2521_, 26);
v_homomulFn_x3f_2549_ = lean_ctor_get(v_v_2521_, 27);
v_subFn_2550_ = lean_ctor_get(v_v_2521_, 28);
v_negFn_2551_ = lean_ctor_get(v_v_2521_, 29);
v_vars_2552_ = lean_ctor_get(v_v_2521_, 30);
v_varMap_2553_ = lean_ctor_get(v_v_2521_, 31);
v_lowers_2554_ = lean_ctor_get(v_v_2521_, 32);
v_uppers_2555_ = lean_ctor_get(v_v_2521_, 33);
v_diseqs_2556_ = lean_ctor_get(v_v_2521_, 34);
v_assignment_2557_ = lean_ctor_get(v_v_2521_, 35);
v_caseSplits_2558_ = lean_ctor_get_uint8(v_v_2521_, sizeof(void*)*42);
v_conflict_x3f_2559_ = lean_ctor_get(v_v_2521_, 36);
v_diseqSplits_2560_ = lean_ctor_get(v_v_2521_, 37);
v_elimEqs_2561_ = lean_ctor_get(v_v_2521_, 38);
v_elimStack_2562_ = lean_ctor_get(v_v_2521_, 39);
v_occurs_2563_ = lean_ctor_get(v_v_2521_, 40);
v_ignored_2564_ = lean_ctor_get(v_v_2521_, 41);
v_isSharedCheck_2578_ = !lean_is_exclusive(v_v_2521_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2566_ = v_v_2521_;
v_isShared_2567_ = v_isSharedCheck_2578_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_ignored_2564_);
lean_inc(v_occurs_2563_);
lean_inc(v_elimStack_2562_);
lean_inc(v_elimEqs_2561_);
lean_inc(v_diseqSplits_2560_);
lean_inc(v_conflict_x3f_2559_);
lean_inc(v_assignment_2557_);
lean_inc(v_diseqs_2556_);
lean_inc(v_uppers_2555_);
lean_inc(v_lowers_2554_);
lean_inc(v_varMap_2553_);
lean_inc(v_vars_2552_);
lean_inc(v_negFn_2551_);
lean_inc(v_subFn_2550_);
lean_inc(v_homomulFn_x3f_2549_);
lean_inc(v_nsmulFn_x3f_2548_);
lean_inc(v_zsmulFn_x3f_2547_);
lean_inc(v_nsmulFn_2546_);
lean_inc(v_zsmulFn_2545_);
lean_inc(v_addFn_2544_);
lean_inc(v_ltFn_x3f_2543_);
lean_inc(v_leFn_x3f_2542_);
lean_inc(v_one_x3f_2541_);
lean_inc(v_ofNatZero_2540_);
lean_inc(v_zero_2539_);
lean_inc(v_charInst_x3f_2538_);
lean_inc(v_fieldInst_x3f_2537_);
lean_inc(v_orderedRingInst_x3f_2536_);
lean_inc(v_commRingInst_x3f_2535_);
lean_inc(v_ringInst_x3f_2534_);
lean_inc(v_noNatDivInst_x3f_2533_);
lean_inc(v_isLinearInst_x3f_2532_);
lean_inc(v_orderedAddInst_x3f_2531_);
lean_inc(v_isPreorderInst_x3f_2530_);
lean_inc(v_lawfulOrderLTInst_x3f_2529_);
lean_inc(v_ltInst_x3f_2528_);
lean_inc(v_leInst_x3f_2527_);
lean_inc(v_intModuleInst_2526_);
lean_inc(v_u_2525_);
lean_inc(v_type_2524_);
lean_inc(v_ringId_x3f_2523_);
lean_inc(v_id_2522_);
lean_dec(v_v_2521_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2578_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2568_; lean_object* v_xs_x27_2569_; lean_object* v___x_2570_; lean_object* v___x_2572_; 
v___x_2568_ = lean_box(0);
v_xs_x27_2569_ = lean_array_fset(v_structs_2508_, v_a_2504_, v___x_2568_);
v___x_2570_ = l_Lean_PersistentArray_set___redArg(v_uppers_2555_, v_y_2505_, v_fst_2506_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 33, v___x_2570_);
v___x_2572_ = v___x_2566_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_id_2522_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_ringId_x3f_2523_);
lean_ctor_set(v_reuseFailAlloc_2577_, 2, v_type_2524_);
lean_ctor_set(v_reuseFailAlloc_2577_, 3, v_u_2525_);
lean_ctor_set(v_reuseFailAlloc_2577_, 4, v_intModuleInst_2526_);
lean_ctor_set(v_reuseFailAlloc_2577_, 5, v_leInst_x3f_2527_);
lean_ctor_set(v_reuseFailAlloc_2577_, 6, v_ltInst_x3f_2528_);
lean_ctor_set(v_reuseFailAlloc_2577_, 7, v_lawfulOrderLTInst_x3f_2529_);
lean_ctor_set(v_reuseFailAlloc_2577_, 8, v_isPreorderInst_x3f_2530_);
lean_ctor_set(v_reuseFailAlloc_2577_, 9, v_orderedAddInst_x3f_2531_);
lean_ctor_set(v_reuseFailAlloc_2577_, 10, v_isLinearInst_x3f_2532_);
lean_ctor_set(v_reuseFailAlloc_2577_, 11, v_noNatDivInst_x3f_2533_);
lean_ctor_set(v_reuseFailAlloc_2577_, 12, v_ringInst_x3f_2534_);
lean_ctor_set(v_reuseFailAlloc_2577_, 13, v_commRingInst_x3f_2535_);
lean_ctor_set(v_reuseFailAlloc_2577_, 14, v_orderedRingInst_x3f_2536_);
lean_ctor_set(v_reuseFailAlloc_2577_, 15, v_fieldInst_x3f_2537_);
lean_ctor_set(v_reuseFailAlloc_2577_, 16, v_charInst_x3f_2538_);
lean_ctor_set(v_reuseFailAlloc_2577_, 17, v_zero_2539_);
lean_ctor_set(v_reuseFailAlloc_2577_, 18, v_ofNatZero_2540_);
lean_ctor_set(v_reuseFailAlloc_2577_, 19, v_one_x3f_2541_);
lean_ctor_set(v_reuseFailAlloc_2577_, 20, v_leFn_x3f_2542_);
lean_ctor_set(v_reuseFailAlloc_2577_, 21, v_ltFn_x3f_2543_);
lean_ctor_set(v_reuseFailAlloc_2577_, 22, v_addFn_2544_);
lean_ctor_set(v_reuseFailAlloc_2577_, 23, v_zsmulFn_2545_);
lean_ctor_set(v_reuseFailAlloc_2577_, 24, v_nsmulFn_2546_);
lean_ctor_set(v_reuseFailAlloc_2577_, 25, v_zsmulFn_x3f_2547_);
lean_ctor_set(v_reuseFailAlloc_2577_, 26, v_nsmulFn_x3f_2548_);
lean_ctor_set(v_reuseFailAlloc_2577_, 27, v_homomulFn_x3f_2549_);
lean_ctor_set(v_reuseFailAlloc_2577_, 28, v_subFn_2550_);
lean_ctor_set(v_reuseFailAlloc_2577_, 29, v_negFn_2551_);
lean_ctor_set(v_reuseFailAlloc_2577_, 30, v_vars_2552_);
lean_ctor_set(v_reuseFailAlloc_2577_, 31, v_varMap_2553_);
lean_ctor_set(v_reuseFailAlloc_2577_, 32, v_lowers_2554_);
lean_ctor_set(v_reuseFailAlloc_2577_, 33, v___x_2570_);
lean_ctor_set(v_reuseFailAlloc_2577_, 34, v_diseqs_2556_);
lean_ctor_set(v_reuseFailAlloc_2577_, 35, v_assignment_2557_);
lean_ctor_set(v_reuseFailAlloc_2577_, 36, v_conflict_x3f_2559_);
lean_ctor_set(v_reuseFailAlloc_2577_, 37, v_diseqSplits_2560_);
lean_ctor_set(v_reuseFailAlloc_2577_, 38, v_elimEqs_2561_);
lean_ctor_set(v_reuseFailAlloc_2577_, 39, v_elimStack_2562_);
lean_ctor_set(v_reuseFailAlloc_2577_, 40, v_occurs_2563_);
lean_ctor_set(v_reuseFailAlloc_2577_, 41, v_ignored_2564_);
lean_ctor_set_uint8(v_reuseFailAlloc_2577_, sizeof(void*)*42, v_caseSplits_2558_);
v___x_2572_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2573_ = lean_array_fset(v_xs_x27_2569_, v_a_2504_, v___x_2572_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 0, v___x_2573_);
v___x_2575_ = v___x_2519_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2573_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v_typeIdOf_2509_);
lean_ctor_set(v_reuseFailAlloc_2576_, 2, v_exprToStructId_2510_);
lean_ctor_set(v_reuseFailAlloc_2576_, 3, v_exprToStructIdEntries_2511_);
lean_ctor_set(v_reuseFailAlloc_2576_, 4, v_forbiddenNatModules_2512_);
lean_ctor_set(v_reuseFailAlloc_2576_, 5, v_natStructs_2513_);
lean_ctor_set(v_reuseFailAlloc_2576_, 6, v_natTypeIdOf_2514_);
lean_ctor_set(v_reuseFailAlloc_2576_, 7, v_exprToNatStructId_2515_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed(lean_object* v_a_2588_, lean_object* v_y_2589_, lean_object* v_fst_2590_, lean_object* v_s_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(v_a_2588_, v_y_2589_, v_fst_2590_, v_s_2591_);
lean_dec(v_y_2589_);
lean_dec(v_a_2588_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object* v_a_2593_, lean_object* v_x_2594_, lean_object* v_c_2595_, lean_object* v_y_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2610_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2644_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2613_ = v___x_2610_;
v_isShared_2614_ = v_isSharedCheck_2644_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2644_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
uint8_t v___x_2615_; 
v___x_2615_ = lean_unbox(v_a_2611_);
lean_dec(v_a_2611_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; 
lean_del_object(v___x_2613_);
v___x_2616_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___y_2619_; lean_object* v_uppers_2627_; lean_object* v_size_2628_; uint8_t v___x_2629_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v_uppers_2627_ = lean_ctor_get(v_a_2617_, 33);
lean_inc_ref(v_uppers_2627_);
lean_dec(v_a_2617_);
v_size_2628_ = lean_ctor_get(v_uppers_2627_, 2);
v___x_2629_ = lean_nat_dec_lt(v_y_2596_, v_size_2628_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2630_; 
lean_dec_ref(v_uppers_2627_);
v___x_2630_ = l_outOfBounds___redArg(v___x_2609_);
v___y_2619_ = v___x_2630_;
goto v___jp_2618_;
}
else
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2609_, v_uppers_2627_, v_y_2596_);
lean_dec_ref(v_uppers_2627_);
v___y_2619_ = v___x_2631_;
goto v___jp_2618_;
}
v___jp_2618_:
{
lean_object* v___x_2620_; lean_object* v_fst_2621_; lean_object* v_snd_2622_; lean_object* v___f_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2620_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2594_, v___y_2619_);
lean_dec_ref(v___y_2619_);
v_fst_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_fst_2621_);
v_snd_2622_ = lean_ctor_get(v___x_2620_, 1);
lean_inc(v_snd_2622_);
lean_dec_ref(v___x_2620_);
lean_inc(v_a_2597_);
v___f_2623_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2623_, 0, v_a_2597_);
lean_closure_set(v___f_2623_, 1, v_y_2596_);
lean_closure_set(v___f_2623_, 2, v_fst_2621_);
v___x_2624_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2625_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2624_, v___f_2623_, v_a_2598_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v___x_2626_; 
lean_dec_ref_known(v___x_2625_, 1);
v___x_2626_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2593_, v_x_2594_, v_c_2595_, v_snd_2622_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
lean_dec(v_snd_2622_);
return v___x_2626_;
}
else
{
lean_dec(v_snd_2622_);
lean_dec_ref(v_c_2595_);
lean_dec(v_x_2594_);
lean_dec(v_a_2593_);
return v___x_2625_;
}
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec(v_y_2596_);
lean_dec_ref(v_c_2595_);
lean_dec(v_x_2594_);
lean_dec(v_a_2593_);
v_a_2632_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2616_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2616_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
else
{
lean_object* v___x_2640_; lean_object* v___x_2642_; 
lean_dec(v_y_2596_);
lean_dec_ref(v_c_2595_);
lean_dec(v_x_2594_);
lean_dec(v_a_2593_);
v___x_2640_ = lean_box(0);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v___x_2640_);
v___x_2642_ = v___x_2613_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2640_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec(v_y_2596_);
lean_dec_ref(v_c_2595_);
lean_dec(v_x_2594_);
lean_dec(v_a_2593_);
v_a_2645_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2610_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2610_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object* v_a_2653_, lean_object* v_x_2654_, lean_object* v_c_2655_, lean_object* v_y_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_2653_, v_x_2654_, v_c_2655_, v_y_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
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
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(lean_object* v___y_2670_, lean_object* v_a_2671_, lean_object* v_s_2672_){
_start:
{
lean_object* v_structs_2673_; lean_object* v_typeIdOf_2674_; lean_object* v_exprToStructId_2675_; lean_object* v_exprToStructIdEntries_2676_; lean_object* v_forbiddenNatModules_2677_; lean_object* v_natStructs_2678_; lean_object* v_natTypeIdOf_2679_; lean_object* v_exprToNatStructId_2680_; lean_object* v___x_2681_; uint8_t v___x_2682_; 
v_structs_2673_ = lean_ctor_get(v_s_2672_, 0);
v_typeIdOf_2674_ = lean_ctor_get(v_s_2672_, 1);
v_exprToStructId_2675_ = lean_ctor_get(v_s_2672_, 2);
v_exprToStructIdEntries_2676_ = lean_ctor_get(v_s_2672_, 3);
v_forbiddenNatModules_2677_ = lean_ctor_get(v_s_2672_, 4);
v_natStructs_2678_ = lean_ctor_get(v_s_2672_, 5);
v_natTypeIdOf_2679_ = lean_ctor_get(v_s_2672_, 6);
v_exprToNatStructId_2680_ = lean_ctor_get(v_s_2672_, 7);
v___x_2681_ = lean_array_get_size(v_structs_2673_);
v___x_2682_ = lean_nat_dec_lt(v___y_2670_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_dec_ref(v_a_2671_);
return v_s_2672_;
}
else
{
lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2744_; 
lean_inc_ref(v_exprToNatStructId_2680_);
lean_inc_ref(v_natTypeIdOf_2679_);
lean_inc_ref(v_natStructs_2678_);
lean_inc_ref(v_forbiddenNatModules_2677_);
lean_inc_ref(v_exprToStructIdEntries_2676_);
lean_inc_ref(v_exprToStructId_2675_);
lean_inc_ref(v_typeIdOf_2674_);
lean_inc_ref(v_structs_2673_);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_s_2672_);
if (v_isSharedCheck_2744_ == 0)
{
lean_object* v_unused_2745_; lean_object* v_unused_2746_; lean_object* v_unused_2747_; lean_object* v_unused_2748_; lean_object* v_unused_2749_; lean_object* v_unused_2750_; lean_object* v_unused_2751_; lean_object* v_unused_2752_; 
v_unused_2745_ = lean_ctor_get(v_s_2672_, 7);
lean_dec(v_unused_2745_);
v_unused_2746_ = lean_ctor_get(v_s_2672_, 6);
lean_dec(v_unused_2746_);
v_unused_2747_ = lean_ctor_get(v_s_2672_, 5);
lean_dec(v_unused_2747_);
v_unused_2748_ = lean_ctor_get(v_s_2672_, 4);
lean_dec(v_unused_2748_);
v_unused_2749_ = lean_ctor_get(v_s_2672_, 3);
lean_dec(v_unused_2749_);
v_unused_2750_ = lean_ctor_get(v_s_2672_, 2);
lean_dec(v_unused_2750_);
v_unused_2751_ = lean_ctor_get(v_s_2672_, 1);
lean_dec(v_unused_2751_);
v_unused_2752_ = lean_ctor_get(v_s_2672_, 0);
lean_dec(v_unused_2752_);
v___x_2684_ = v_s_2672_;
v_isShared_2685_ = v_isSharedCheck_2744_;
goto v_resetjp_2683_;
}
else
{
lean_dec(v_s_2672_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2744_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v_v_2686_; lean_object* v_id_2687_; lean_object* v_ringId_x3f_2688_; lean_object* v_type_2689_; lean_object* v_u_2690_; lean_object* v_intModuleInst_2691_; lean_object* v_leInst_x3f_2692_; lean_object* v_ltInst_x3f_2693_; lean_object* v_lawfulOrderLTInst_x3f_2694_; lean_object* v_isPreorderInst_x3f_2695_; lean_object* v_orderedAddInst_x3f_2696_; lean_object* v_isLinearInst_x3f_2697_; lean_object* v_noNatDivInst_x3f_2698_; lean_object* v_ringInst_x3f_2699_; lean_object* v_commRingInst_x3f_2700_; lean_object* v_orderedRingInst_x3f_2701_; lean_object* v_fieldInst_x3f_2702_; lean_object* v_charInst_x3f_2703_; lean_object* v_zero_2704_; lean_object* v_ofNatZero_2705_; lean_object* v_one_x3f_2706_; lean_object* v_leFn_x3f_2707_; lean_object* v_ltFn_x3f_2708_; lean_object* v_addFn_2709_; lean_object* v_zsmulFn_2710_; lean_object* v_nsmulFn_2711_; lean_object* v_zsmulFn_x3f_2712_; lean_object* v_nsmulFn_x3f_2713_; lean_object* v_homomulFn_x3f_2714_; lean_object* v_subFn_2715_; lean_object* v_negFn_2716_; lean_object* v_vars_2717_; lean_object* v_varMap_2718_; lean_object* v_lowers_2719_; lean_object* v_uppers_2720_; lean_object* v_diseqs_2721_; lean_object* v_assignment_2722_; uint8_t v_caseSplits_2723_; lean_object* v_conflict_x3f_2724_; lean_object* v_diseqSplits_2725_; lean_object* v_elimEqs_2726_; lean_object* v_elimStack_2727_; lean_object* v_occurs_2728_; lean_object* v_ignored_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2743_; 
v_v_2686_ = lean_array_fget(v_structs_2673_, v___y_2670_);
v_id_2687_ = lean_ctor_get(v_v_2686_, 0);
v_ringId_x3f_2688_ = lean_ctor_get(v_v_2686_, 1);
v_type_2689_ = lean_ctor_get(v_v_2686_, 2);
v_u_2690_ = lean_ctor_get(v_v_2686_, 3);
v_intModuleInst_2691_ = lean_ctor_get(v_v_2686_, 4);
v_leInst_x3f_2692_ = lean_ctor_get(v_v_2686_, 5);
v_ltInst_x3f_2693_ = lean_ctor_get(v_v_2686_, 6);
v_lawfulOrderLTInst_x3f_2694_ = lean_ctor_get(v_v_2686_, 7);
v_isPreorderInst_x3f_2695_ = lean_ctor_get(v_v_2686_, 8);
v_orderedAddInst_x3f_2696_ = lean_ctor_get(v_v_2686_, 9);
v_isLinearInst_x3f_2697_ = lean_ctor_get(v_v_2686_, 10);
v_noNatDivInst_x3f_2698_ = lean_ctor_get(v_v_2686_, 11);
v_ringInst_x3f_2699_ = lean_ctor_get(v_v_2686_, 12);
v_commRingInst_x3f_2700_ = lean_ctor_get(v_v_2686_, 13);
v_orderedRingInst_x3f_2701_ = lean_ctor_get(v_v_2686_, 14);
v_fieldInst_x3f_2702_ = lean_ctor_get(v_v_2686_, 15);
v_charInst_x3f_2703_ = lean_ctor_get(v_v_2686_, 16);
v_zero_2704_ = lean_ctor_get(v_v_2686_, 17);
v_ofNatZero_2705_ = lean_ctor_get(v_v_2686_, 18);
v_one_x3f_2706_ = lean_ctor_get(v_v_2686_, 19);
v_leFn_x3f_2707_ = lean_ctor_get(v_v_2686_, 20);
v_ltFn_x3f_2708_ = lean_ctor_get(v_v_2686_, 21);
v_addFn_2709_ = lean_ctor_get(v_v_2686_, 22);
v_zsmulFn_2710_ = lean_ctor_get(v_v_2686_, 23);
v_nsmulFn_2711_ = lean_ctor_get(v_v_2686_, 24);
v_zsmulFn_x3f_2712_ = lean_ctor_get(v_v_2686_, 25);
v_nsmulFn_x3f_2713_ = lean_ctor_get(v_v_2686_, 26);
v_homomulFn_x3f_2714_ = lean_ctor_get(v_v_2686_, 27);
v_subFn_2715_ = lean_ctor_get(v_v_2686_, 28);
v_negFn_2716_ = lean_ctor_get(v_v_2686_, 29);
v_vars_2717_ = lean_ctor_get(v_v_2686_, 30);
v_varMap_2718_ = lean_ctor_get(v_v_2686_, 31);
v_lowers_2719_ = lean_ctor_get(v_v_2686_, 32);
v_uppers_2720_ = lean_ctor_get(v_v_2686_, 33);
v_diseqs_2721_ = lean_ctor_get(v_v_2686_, 34);
v_assignment_2722_ = lean_ctor_get(v_v_2686_, 35);
v_caseSplits_2723_ = lean_ctor_get_uint8(v_v_2686_, sizeof(void*)*42);
v_conflict_x3f_2724_ = lean_ctor_get(v_v_2686_, 36);
v_diseqSplits_2725_ = lean_ctor_get(v_v_2686_, 37);
v_elimEqs_2726_ = lean_ctor_get(v_v_2686_, 38);
v_elimStack_2727_ = lean_ctor_get(v_v_2686_, 39);
v_occurs_2728_ = lean_ctor_get(v_v_2686_, 40);
v_ignored_2729_ = lean_ctor_get(v_v_2686_, 41);
v_isSharedCheck_2743_ = !lean_is_exclusive(v_v_2686_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2731_ = v_v_2686_;
v_isShared_2732_ = v_isSharedCheck_2743_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_ignored_2729_);
lean_inc(v_occurs_2728_);
lean_inc(v_elimStack_2727_);
lean_inc(v_elimEqs_2726_);
lean_inc(v_diseqSplits_2725_);
lean_inc(v_conflict_x3f_2724_);
lean_inc(v_assignment_2722_);
lean_inc(v_diseqs_2721_);
lean_inc(v_uppers_2720_);
lean_inc(v_lowers_2719_);
lean_inc(v_varMap_2718_);
lean_inc(v_vars_2717_);
lean_inc(v_negFn_2716_);
lean_inc(v_subFn_2715_);
lean_inc(v_homomulFn_x3f_2714_);
lean_inc(v_nsmulFn_x3f_2713_);
lean_inc(v_zsmulFn_x3f_2712_);
lean_inc(v_nsmulFn_2711_);
lean_inc(v_zsmulFn_2710_);
lean_inc(v_addFn_2709_);
lean_inc(v_ltFn_x3f_2708_);
lean_inc(v_leFn_x3f_2707_);
lean_inc(v_one_x3f_2706_);
lean_inc(v_ofNatZero_2705_);
lean_inc(v_zero_2704_);
lean_inc(v_charInst_x3f_2703_);
lean_inc(v_fieldInst_x3f_2702_);
lean_inc(v_orderedRingInst_x3f_2701_);
lean_inc(v_commRingInst_x3f_2700_);
lean_inc(v_ringInst_x3f_2699_);
lean_inc(v_noNatDivInst_x3f_2698_);
lean_inc(v_isLinearInst_x3f_2697_);
lean_inc(v_orderedAddInst_x3f_2696_);
lean_inc(v_isPreorderInst_x3f_2695_);
lean_inc(v_lawfulOrderLTInst_x3f_2694_);
lean_inc(v_ltInst_x3f_2693_);
lean_inc(v_leInst_x3f_2692_);
lean_inc(v_intModuleInst_2691_);
lean_inc(v_u_2690_);
lean_inc(v_type_2689_);
lean_inc(v_ringId_x3f_2688_);
lean_inc(v_id_2687_);
lean_dec(v_v_2686_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2743_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2733_; lean_object* v_xs_x27_2734_; lean_object* v___x_2735_; lean_object* v___x_2737_; 
v___x_2733_ = lean_box(0);
v_xs_x27_2734_ = lean_array_fset(v_structs_2673_, v___y_2670_, v___x_2733_);
v___x_2735_ = l_Lean_PersistentArray_push___redArg(v_ignored_2729_, v_a_2671_);
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 41, v___x_2735_);
v___x_2737_ = v___x_2731_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_id_2687_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_ringId_x3f_2688_);
lean_ctor_set(v_reuseFailAlloc_2742_, 2, v_type_2689_);
lean_ctor_set(v_reuseFailAlloc_2742_, 3, v_u_2690_);
lean_ctor_set(v_reuseFailAlloc_2742_, 4, v_intModuleInst_2691_);
lean_ctor_set(v_reuseFailAlloc_2742_, 5, v_leInst_x3f_2692_);
lean_ctor_set(v_reuseFailAlloc_2742_, 6, v_ltInst_x3f_2693_);
lean_ctor_set(v_reuseFailAlloc_2742_, 7, v_lawfulOrderLTInst_x3f_2694_);
lean_ctor_set(v_reuseFailAlloc_2742_, 8, v_isPreorderInst_x3f_2695_);
lean_ctor_set(v_reuseFailAlloc_2742_, 9, v_orderedAddInst_x3f_2696_);
lean_ctor_set(v_reuseFailAlloc_2742_, 10, v_isLinearInst_x3f_2697_);
lean_ctor_set(v_reuseFailAlloc_2742_, 11, v_noNatDivInst_x3f_2698_);
lean_ctor_set(v_reuseFailAlloc_2742_, 12, v_ringInst_x3f_2699_);
lean_ctor_set(v_reuseFailAlloc_2742_, 13, v_commRingInst_x3f_2700_);
lean_ctor_set(v_reuseFailAlloc_2742_, 14, v_orderedRingInst_x3f_2701_);
lean_ctor_set(v_reuseFailAlloc_2742_, 15, v_fieldInst_x3f_2702_);
lean_ctor_set(v_reuseFailAlloc_2742_, 16, v_charInst_x3f_2703_);
lean_ctor_set(v_reuseFailAlloc_2742_, 17, v_zero_2704_);
lean_ctor_set(v_reuseFailAlloc_2742_, 18, v_ofNatZero_2705_);
lean_ctor_set(v_reuseFailAlloc_2742_, 19, v_one_x3f_2706_);
lean_ctor_set(v_reuseFailAlloc_2742_, 20, v_leFn_x3f_2707_);
lean_ctor_set(v_reuseFailAlloc_2742_, 21, v_ltFn_x3f_2708_);
lean_ctor_set(v_reuseFailAlloc_2742_, 22, v_addFn_2709_);
lean_ctor_set(v_reuseFailAlloc_2742_, 23, v_zsmulFn_2710_);
lean_ctor_set(v_reuseFailAlloc_2742_, 24, v_nsmulFn_2711_);
lean_ctor_set(v_reuseFailAlloc_2742_, 25, v_zsmulFn_x3f_2712_);
lean_ctor_set(v_reuseFailAlloc_2742_, 26, v_nsmulFn_x3f_2713_);
lean_ctor_set(v_reuseFailAlloc_2742_, 27, v_homomulFn_x3f_2714_);
lean_ctor_set(v_reuseFailAlloc_2742_, 28, v_subFn_2715_);
lean_ctor_set(v_reuseFailAlloc_2742_, 29, v_negFn_2716_);
lean_ctor_set(v_reuseFailAlloc_2742_, 30, v_vars_2717_);
lean_ctor_set(v_reuseFailAlloc_2742_, 31, v_varMap_2718_);
lean_ctor_set(v_reuseFailAlloc_2742_, 32, v_lowers_2719_);
lean_ctor_set(v_reuseFailAlloc_2742_, 33, v_uppers_2720_);
lean_ctor_set(v_reuseFailAlloc_2742_, 34, v_diseqs_2721_);
lean_ctor_set(v_reuseFailAlloc_2742_, 35, v_assignment_2722_);
lean_ctor_set(v_reuseFailAlloc_2742_, 36, v_conflict_x3f_2724_);
lean_ctor_set(v_reuseFailAlloc_2742_, 37, v_diseqSplits_2725_);
lean_ctor_set(v_reuseFailAlloc_2742_, 38, v_elimEqs_2726_);
lean_ctor_set(v_reuseFailAlloc_2742_, 39, v_elimStack_2727_);
lean_ctor_set(v_reuseFailAlloc_2742_, 40, v_occurs_2728_);
lean_ctor_set(v_reuseFailAlloc_2742_, 41, v___x_2735_);
lean_ctor_set_uint8(v_reuseFailAlloc_2742_, sizeof(void*)*42, v_caseSplits_2723_);
v___x_2737_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2738_; lean_object* v___x_2740_; 
v___x_2738_ = lean_array_fset(v_xs_x27_2734_, v___y_2670_, v___x_2737_);
if (v_isShared_2685_ == 0)
{
lean_ctor_set(v___x_2684_, 0, v___x_2738_);
v___x_2740_ = v___x_2684_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2738_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_typeIdOf_2674_);
lean_ctor_set(v_reuseFailAlloc_2741_, 2, v_exprToStructId_2675_);
lean_ctor_set(v_reuseFailAlloc_2741_, 3, v_exprToStructIdEntries_2676_);
lean_ctor_set(v_reuseFailAlloc_2741_, 4, v_forbiddenNatModules_2677_);
lean_ctor_set(v_reuseFailAlloc_2741_, 5, v_natStructs_2678_);
lean_ctor_set(v_reuseFailAlloc_2741_, 6, v_natTypeIdOf_2679_);
lean_ctor_set(v_reuseFailAlloc_2741_, 7, v_exprToNatStructId_2680_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed(lean_object* v___y_2753_, lean_object* v_a_2754_, lean_object* v_s_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(v___y_2753_, v_a_2754_, v_s_2755_);
lean_dec(v___y_2753_);
return v_res_2756_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3(void){
_start:
{
lean_object* v_cls_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v_cls_2764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_2766_ = l_Lean_Name_append(v___x_2765_, v_cls_2764_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object* v_c_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v_toCold_2805_; lean_object* v_options_2806_; uint8_t v_hasTrace_2807_; 
v_toCold_2805_ = lean_ctor_get(v_a_2777_, 0);
v_options_2806_ = lean_ctor_get(v_toCold_2805_, 2);
v_hasTrace_2807_ = lean_ctor_get_uint8(v_options_2806_, sizeof(void*)*1);
if (v_hasTrace_2807_ == 0)
{
v___y_2781_ = v_a_2768_;
v___y_2782_ = v_a_2769_;
v___y_2783_ = v_a_2770_;
v___y_2784_ = v_a_2771_;
v___y_2785_ = v_a_2772_;
v___y_2786_ = v_a_2773_;
v___y_2787_ = v_a_2774_;
v___y_2788_ = v_a_2775_;
v___y_2789_ = v_a_2776_;
v___y_2790_ = v_a_2777_;
v___y_2791_ = v_a_2778_;
goto v___jp_2780_;
}
else
{
lean_object* v_inheritedTraceOptions_2808_; lean_object* v_cls_2809_; lean_object* v___x_2810_; uint8_t v___x_2811_; 
v_inheritedTraceOptions_2808_ = lean_ctor_get(v_toCold_2805_, 11);
v_cls_2809_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2810_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3);
v___x_2811_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2808_, v_options_2806_, v___x_2810_);
if (v___x_2811_ == 0)
{
v___y_2781_ = v_a_2768_;
v___y_2782_ = v_a_2769_;
v___y_2783_ = v_a_2770_;
v___y_2784_ = v_a_2771_;
v___y_2785_ = v_a_2772_;
v___y_2786_ = v_a_2773_;
v___y_2787_ = v_a_2774_;
v___y_2788_ = v_a_2775_;
v___y_2789_ = v_a_2776_;
v___y_2790_ = v_a_2777_;
v___y_2791_ = v_a_2778_;
goto v___jp_2780_;
}
else
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2812_, 1);
v___x_2814_ = l_Lean_MessageData_ofExpr(v_a_2813_);
v___x_2815_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_2809_, v___x_2814_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_dec_ref_known(v___x_2815_, 1);
v___y_2781_ = v_a_2768_;
v___y_2782_ = v_a_2769_;
v___y_2783_ = v_a_2770_;
v___y_2784_ = v_a_2771_;
v___y_2785_ = v_a_2772_;
v___y_2786_ = v_a_2773_;
v___y_2787_ = v_a_2774_;
v___y_2788_ = v_a_2775_;
v___y_2789_ = v_a_2776_;
v___y_2790_ = v_a_2777_;
v___y_2791_ = v_a_2778_;
goto v___jp_2780_;
}
else
{
return v___x_2815_;
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
v_a_2816_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2812_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2812_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
v___jp_2780_:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2767_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___f_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2792_, 1);
lean_inc(v___y_2781_);
v___f_2794_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2794_, 0, v___y_2781_);
lean_closure_set(v___f_2794_, 1, v_a_2793_);
v___x_2795_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2796_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2795_, v___f_2794_, v___y_2782_);
return v___x_2796_;
}
else
{
lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2804_; 
v_a_2797_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2799_ = v___x_2792_;
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v___x_2792_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2802_; 
if (v_isShared_2800_ == 0)
{
v___x_2802_ = v___x_2799_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_a_2797_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object* v_c_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
lean_dec(v_a_2829_);
lean_dec_ref(v_a_2828_);
lean_dec(v_a_2827_);
lean_dec(v_a_2826_);
lean_dec(v_a_2825_);
lean_dec_ref(v_c_2824_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object* v_c_u2082_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v_p_2851_; lean_object* v_toCold_2852_; lean_object* v_currRecDepth_2853_; lean_object* v_ref_2854_; uint16_t v_optionFlags_2855_; uint8_t v_suppressElabErrors_2856_; uint8_t v_isRecordingDeps_2857_; lean_object* v_maxRecDepth_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; 
v_p_2851_ = lean_ctor_get(v_c_u2082_2838_, 0);
v_toCold_2852_ = lean_ctor_get(v_a_2848_, 0);
lean_inc_ref(v_toCold_2852_);
v_currRecDepth_2853_ = lean_ctor_get(v_a_2848_, 1);
lean_inc(v_currRecDepth_2853_);
v_ref_2854_ = lean_ctor_get(v_a_2848_, 2);
lean_inc(v_ref_2854_);
v_optionFlags_2855_ = lean_ctor_get_uint16(v_a_2848_, sizeof(void*)*3);
v_suppressElabErrors_2856_ = lean_ctor_get_uint8(v_a_2848_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2857_ = lean_ctor_get_uint8(v_a_2848_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_2848_);
v_maxRecDepth_2909_ = lean_ctor_get(v_toCold_2852_, 3);
v___x_2910_ = lean_unsigned_to_nat(0u);
v___x_2911_ = lean_nat_dec_eq(v_maxRecDepth_2909_, v___x_2910_);
if (v___x_2911_ == 0)
{
uint8_t v___x_2912_; 
v___x_2912_ = lean_nat_dec_eq(v_currRecDepth_2853_, v_maxRecDepth_2909_);
if (v___x_2912_ == 0)
{
goto v___jp_2858_;
}
else
{
lean_object* v___x_2913_; 
lean_dec(v_currRecDepth_2853_);
lean_dec_ref(v_toCold_2852_);
lean_dec_ref(v_c_u2082_2838_);
v___x_2913_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_2854_);
return v___x_2913_;
}
}
else
{
goto v___jp_2858_;
}
v___jp_2858_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2859_ = lean_unsigned_to_nat(1u);
v___x_2860_ = lean_nat_add(v_currRecDepth_2853_, v___x_2859_);
lean_dec(v_currRecDepth_2853_);
v___x_2861_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2861_, 0, v_toCold_2852_);
lean_ctor_set(v___x_2861_, 1, v___x_2860_);
lean_ctor_set(v___x_2861_, 2, v_ref_2854_);
lean_ctor_set_uint16(v___x_2861_, sizeof(void*)*3, v_optionFlags_2855_);
lean_ctor_set_uint8(v___x_2861_, sizeof(void*)*3 + 2, v_suppressElabErrors_2856_);
lean_ctor_set_uint8(v___x_2861_, sizeof(void*)*3 + 3, v_isRecordingDeps_2857_);
v___x_2862_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2851_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v___x_2861_, v_a_2849_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2900_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2865_ = v___x_2862_;
v_isShared_2866_ = v_isSharedCheck_2900_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2862_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2900_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
if (lean_obj_tag(v_a_2863_) == 1)
{
lean_object* v_val_2867_; lean_object* v_snd_2868_; lean_object* v_snd_2869_; lean_object* v_fst_2870_; lean_object* v_fst_2871_; lean_object* v_p_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
lean_del_object(v___x_2865_);
v_val_2867_ = lean_ctor_get(v_a_2863_, 0);
lean_inc(v_val_2867_);
lean_dec_ref_known(v_a_2863_, 1);
v_snd_2868_ = lean_ctor_get(v_val_2867_, 1);
lean_inc(v_snd_2868_);
v_snd_2869_ = lean_ctor_get(v_snd_2868_, 1);
lean_inc(v_snd_2869_);
v_fst_2870_ = lean_ctor_get(v_val_2867_, 0);
lean_inc(v_fst_2870_);
lean_dec(v_val_2867_);
v_fst_2871_ = lean_ctor_get(v_snd_2868_, 0);
lean_inc(v_fst_2871_);
lean_dec(v_snd_2868_);
v_p_2872_ = lean_ctor_get(v_snd_2869_, 0);
v___x_2873_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2872_, v_fst_2871_);
lean_inc_ref(v_c_u2082_2838_);
v___x_2874_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v___x_2873_, v_fst_2871_, v_snd_2869_, v_fst_2870_, v_c_u2082_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v___x_2861_, v_a_2849_);
lean_dec(v_fst_2871_);
lean_dec(v___x_2873_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
if (lean_obj_tag(v_a_2875_) == 1)
{
lean_object* v_val_2876_; 
lean_dec_ref(v_c_u2082_2838_);
v_val_2876_ = lean_ctor_get(v_a_2875_, 0);
lean_inc(v_val_2876_);
lean_dec_ref_known(v_a_2875_, 1);
v_c_u2082_2838_ = v_val_2876_;
v_a_2848_ = v___x_2861_;
goto _start;
}
else
{
lean_object* v___x_2878_; 
lean_dec(v_a_2875_);
v___x_2878_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_u2082_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v___x_2861_, v_a_2849_);
lean_dec_ref_known(v___x_2861_, 3);
lean_dec_ref(v_c_u2082_2838_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2886_; 
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2886_ == 0)
{
lean_object* v_unused_2887_; 
v_unused_2887_ = lean_ctor_get(v___x_2878_, 0);
lean_dec(v_unused_2887_);
v___x_2880_ = v___x_2878_;
v_isShared_2881_ = v_isSharedCheck_2886_;
goto v_resetjp_2879_;
}
else
{
lean_dec(v___x_2878_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2886_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2882_; lean_object* v___x_2884_; 
v___x_2882_ = lean_box(0);
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 0, v___x_2882_);
v___x_2884_ = v___x_2880_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2882_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
v_a_2888_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2878_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2878_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2861_, 3);
lean_dec_ref(v_c_u2082_2838_);
return v___x_2874_;
}
}
else
{
lean_object* v___x_2896_; lean_object* v___x_2898_; 
lean_dec(v_a_2863_);
lean_dec_ref_known(v___x_2861_, 3);
v___x_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2896_, 0, v_c_u2082_2838_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 0, v___x_2896_);
v___x_2898_ = v___x_2865_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec_ref_known(v___x_2861_, 3);
lean_dec_ref(v_c_u2082_2838_);
v_a_2901_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2862_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2862_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object* v_c_u2082_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_u2082_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_);
lean_dec(v_a_2925_);
lean_dec(v_a_2923_);
lean_dec_ref(v_a_2922_);
lean_dec(v_a_2921_);
lean_dec_ref(v_a_2920_);
lean_dec(v_a_2919_);
lean_dec_ref(v_a_2918_);
lean_dec(v_a_2917_);
lean_dec(v_a_2916_);
lean_dec(v_a_2915_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object* v_val_2928_, lean_object* v_x_2929_, size_t v_x_2930_, size_t v_x_2931_){
_start:
{
if (lean_obj_tag(v_x_2929_) == 0)
{
lean_object* v_cs_2932_; size_t v_j_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; 
v_cs_2932_ = lean_ctor_get(v_x_2929_, 0);
v_j_2933_ = lean_usize_shift_right(v_x_2930_, v_x_2931_);
v___x_2934_ = lean_usize_to_nat(v_j_2933_);
v___x_2935_ = lean_array_get_size(v_cs_2932_);
v___x_2936_ = lean_nat_dec_lt(v___x_2934_, v___x_2935_);
if (v___x_2936_ == 0)
{
lean_dec(v___x_2934_);
lean_dec_ref(v_val_2928_);
return v_x_2929_;
}
else
{
lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2954_; 
lean_inc_ref(v_cs_2932_);
v_isSharedCheck_2954_ = !lean_is_exclusive(v_x_2929_);
if (v_isSharedCheck_2954_ == 0)
{
lean_object* v_unused_2955_; 
v_unused_2955_ = lean_ctor_get(v_x_2929_, 0);
lean_dec(v_unused_2955_);
v___x_2938_ = v_x_2929_;
v_isShared_2939_ = v_isSharedCheck_2954_;
goto v_resetjp_2937_;
}
else
{
lean_dec(v_x_2929_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2954_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
size_t v___x_2940_; size_t v___x_2941_; size_t v___x_2942_; size_t v_i_2943_; size_t v___x_2944_; size_t v_shift_2945_; lean_object* v_v_2946_; lean_object* v___x_2947_; lean_object* v_xs_x27_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2952_; 
v___x_2940_ = ((size_t)1ULL);
v___x_2941_ = lean_usize_shift_left(v___x_2940_, v_x_2931_);
v___x_2942_ = lean_usize_sub(v___x_2941_, v___x_2940_);
v_i_2943_ = lean_usize_land(v_x_2930_, v___x_2942_);
v___x_2944_ = ((size_t)5ULL);
v_shift_2945_ = lean_usize_sub(v_x_2931_, v___x_2944_);
v_v_2946_ = lean_array_fget(v_cs_2932_, v___x_2934_);
v___x_2947_ = lean_box(0);
v_xs_x27_2948_ = lean_array_fset(v_cs_2932_, v___x_2934_, v___x_2947_);
v___x_2949_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2928_, v_v_2946_, v_i_2943_, v_shift_2945_);
v___x_2950_ = lean_array_fset(v_xs_x27_2948_, v___x_2934_, v___x_2949_);
lean_dec(v___x_2934_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v___x_2950_);
v___x_2952_ = v___x_2938_;
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
}
else
{
lean_object* v_vs_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; uint8_t v___x_2959_; 
v_vs_2956_ = lean_ctor_get(v_x_2929_, 0);
v___x_2957_ = lean_usize_to_nat(v_x_2930_);
v___x_2958_ = lean_array_get_size(v_vs_2956_);
v___x_2959_ = lean_nat_dec_lt(v___x_2957_, v___x_2958_);
if (v___x_2959_ == 0)
{
lean_dec(v___x_2957_);
lean_dec_ref(v_val_2928_);
return v_x_2929_;
}
else
{
lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2971_; 
lean_inc_ref(v_vs_2956_);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_x_2929_);
if (v_isSharedCheck_2971_ == 0)
{
lean_object* v_unused_2972_; 
v_unused_2972_ = lean_ctor_get(v_x_2929_, 0);
lean_dec(v_unused_2972_);
v___x_2961_ = v_x_2929_;
v_isShared_2962_ = v_isSharedCheck_2971_;
goto v_resetjp_2960_;
}
else
{
lean_dec(v_x_2929_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2971_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v_v_2963_; lean_object* v___x_2964_; lean_object* v_xs_x27_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2969_; 
v_v_2963_ = lean_array_fget(v_vs_2956_, v___x_2957_);
v___x_2964_ = lean_box(0);
v_xs_x27_2965_ = lean_array_fset(v_vs_2956_, v___x_2957_, v___x_2964_);
v___x_2966_ = l_Lean_PersistentArray_push___redArg(v_v_2963_, v_val_2928_);
v___x_2967_ = lean_array_fset(v_xs_x27_2965_, v___x_2957_, v___x_2966_);
lean_dec(v___x_2957_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 0, v___x_2967_);
v___x_2969_ = v___x_2961_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_val_2973_, lean_object* v_x_2974_, lean_object* v_x_2975_, lean_object* v_x_2976_){
_start:
{
size_t v_x_41338__boxed_2977_; size_t v_x_41339__boxed_2978_; lean_object* v_res_2979_; 
v_x_41338__boxed_2977_ = lean_unbox_usize(v_x_2975_);
lean_dec(v_x_2975_);
v_x_41339__boxed_2978_ = lean_unbox_usize(v_x_2976_);
lean_dec(v_x_2976_);
v_res_2979_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2973_, v_x_2974_, v_x_41338__boxed_2977_, v_x_41339__boxed_2978_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object* v_val_2980_, lean_object* v_t_2981_, lean_object* v_i_2982_){
_start:
{
lean_object* v_root_2983_; lean_object* v_tail_2984_; lean_object* v_size_2985_; size_t v_shift_2986_; lean_object* v_tailOff_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3011_; 
v_root_2983_ = lean_ctor_get(v_t_2981_, 0);
v_tail_2984_ = lean_ctor_get(v_t_2981_, 1);
v_size_2985_ = lean_ctor_get(v_t_2981_, 2);
v_shift_2986_ = lean_ctor_get_usize(v_t_2981_, 4);
v_tailOff_2987_ = lean_ctor_get(v_t_2981_, 3);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_t_2981_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_2989_ = v_t_2981_;
v_isShared_2990_ = v_isSharedCheck_3011_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_tailOff_2987_);
lean_inc(v_size_2985_);
lean_inc(v_tail_2984_);
lean_inc(v_root_2983_);
lean_dec(v_t_2981_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3011_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
uint8_t v___x_2991_; 
v___x_2991_ = lean_nat_dec_le(v_tailOff_2987_, v_i_2982_);
if (v___x_2991_ == 0)
{
size_t v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2995_; 
v___x_2992_ = lean_usize_of_nat(v_i_2982_);
v___x_2993_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2980_, v_root_2983_, v___x_2992_, v_shift_2986_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v___x_2993_);
v___x_2995_ = v___x_2989_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_tail_2984_);
lean_ctor_set(v_reuseFailAlloc_2996_, 2, v_size_2985_);
lean_ctor_set(v_reuseFailAlloc_2996_, 3, v_tailOff_2987_);
lean_ctor_set_usize(v_reuseFailAlloc_2996_, 4, v_shift_2986_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
else
{
lean_object* v___x_2997_; lean_object* v___x_2998_; uint8_t v___x_2999_; 
v___x_2997_ = lean_nat_sub(v_i_2982_, v_tailOff_2987_);
v___x_2998_ = lean_array_get_size(v_tail_2984_);
v___x_2999_ = lean_nat_dec_lt(v___x_2997_, v___x_2998_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3001_; 
lean_dec(v___x_2997_);
lean_dec_ref(v_val_2980_);
if (v_isShared_2990_ == 0)
{
v___x_3001_ = v___x_2989_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_root_2983_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v_tail_2984_);
lean_ctor_set(v_reuseFailAlloc_3002_, 2, v_size_2985_);
lean_ctor_set(v_reuseFailAlloc_3002_, 3, v_tailOff_2987_);
lean_ctor_set_usize(v_reuseFailAlloc_3002_, 4, v_shift_2986_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
else
{
lean_object* v_v_3003_; lean_object* v___x_3004_; lean_object* v_xs_x27_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3009_; 
v_v_3003_ = lean_array_fget(v_tail_2984_, v___x_2997_);
v___x_3004_ = lean_box(0);
v_xs_x27_3005_ = lean_array_fset(v_tail_2984_, v___x_2997_, v___x_3004_);
v___x_3006_ = l_Lean_PersistentArray_push___redArg(v_v_3003_, v_val_2980_);
v___x_3007_ = lean_array_fset(v_xs_x27_3005_, v___x_2997_, v___x_3006_);
lean_dec(v___x_2997_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 1, v___x_3007_);
v___x_3009_ = v___x_2989_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_root_2983_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v___x_3007_);
lean_ctor_set(v_reuseFailAlloc_3010_, 2, v_size_2985_);
lean_ctor_set(v_reuseFailAlloc_3010_, 3, v_tailOff_2987_);
lean_ctor_set_usize(v_reuseFailAlloc_3010_, 4, v_shift_2986_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object* v_val_3012_, lean_object* v_t_3013_, lean_object* v_i_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3012_, v_t_3013_, v_i_3014_);
lean_dec(v_i_3014_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(lean_object* v___y_3016_, lean_object* v_val_3017_, lean_object* v_v_3018_, lean_object* v_s_3019_){
_start:
{
lean_object* v_structs_3020_; lean_object* v_typeIdOf_3021_; lean_object* v_exprToStructId_3022_; lean_object* v_exprToStructIdEntries_3023_; lean_object* v_forbiddenNatModules_3024_; lean_object* v_natStructs_3025_; lean_object* v_natTypeIdOf_3026_; lean_object* v_exprToNatStructId_3027_; lean_object* v___x_3028_; uint8_t v___x_3029_; 
v_structs_3020_ = lean_ctor_get(v_s_3019_, 0);
v_typeIdOf_3021_ = lean_ctor_get(v_s_3019_, 1);
v_exprToStructId_3022_ = lean_ctor_get(v_s_3019_, 2);
v_exprToStructIdEntries_3023_ = lean_ctor_get(v_s_3019_, 3);
v_forbiddenNatModules_3024_ = lean_ctor_get(v_s_3019_, 4);
v_natStructs_3025_ = lean_ctor_get(v_s_3019_, 5);
v_natTypeIdOf_3026_ = lean_ctor_get(v_s_3019_, 6);
v_exprToNatStructId_3027_ = lean_ctor_get(v_s_3019_, 7);
v___x_3028_ = lean_array_get_size(v_structs_3020_);
v___x_3029_ = lean_nat_dec_lt(v___y_3016_, v___x_3028_);
if (v___x_3029_ == 0)
{
lean_dec_ref(v_val_3017_);
return v_s_3019_;
}
else
{
lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3091_; 
lean_inc_ref(v_exprToNatStructId_3027_);
lean_inc_ref(v_natTypeIdOf_3026_);
lean_inc_ref(v_natStructs_3025_);
lean_inc_ref(v_forbiddenNatModules_3024_);
lean_inc_ref(v_exprToStructIdEntries_3023_);
lean_inc_ref(v_exprToStructId_3022_);
lean_inc_ref(v_typeIdOf_3021_);
lean_inc_ref(v_structs_3020_);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_s_3019_);
if (v_isSharedCheck_3091_ == 0)
{
lean_object* v_unused_3092_; lean_object* v_unused_3093_; lean_object* v_unused_3094_; lean_object* v_unused_3095_; lean_object* v_unused_3096_; lean_object* v_unused_3097_; lean_object* v_unused_3098_; lean_object* v_unused_3099_; 
v_unused_3092_ = lean_ctor_get(v_s_3019_, 7);
lean_dec(v_unused_3092_);
v_unused_3093_ = lean_ctor_get(v_s_3019_, 6);
lean_dec(v_unused_3093_);
v_unused_3094_ = lean_ctor_get(v_s_3019_, 5);
lean_dec(v_unused_3094_);
v_unused_3095_ = lean_ctor_get(v_s_3019_, 4);
lean_dec(v_unused_3095_);
v_unused_3096_ = lean_ctor_get(v_s_3019_, 3);
lean_dec(v_unused_3096_);
v_unused_3097_ = lean_ctor_get(v_s_3019_, 2);
lean_dec(v_unused_3097_);
v_unused_3098_ = lean_ctor_get(v_s_3019_, 1);
lean_dec(v_unused_3098_);
v_unused_3099_ = lean_ctor_get(v_s_3019_, 0);
lean_dec(v_unused_3099_);
v___x_3031_ = v_s_3019_;
v_isShared_3032_ = v_isSharedCheck_3091_;
goto v_resetjp_3030_;
}
else
{
lean_dec(v_s_3019_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3091_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v_v_3033_; lean_object* v_id_3034_; lean_object* v_ringId_x3f_3035_; lean_object* v_type_3036_; lean_object* v_u_3037_; lean_object* v_intModuleInst_3038_; lean_object* v_leInst_x3f_3039_; lean_object* v_ltInst_x3f_3040_; lean_object* v_lawfulOrderLTInst_x3f_3041_; lean_object* v_isPreorderInst_x3f_3042_; lean_object* v_orderedAddInst_x3f_3043_; lean_object* v_isLinearInst_x3f_3044_; lean_object* v_noNatDivInst_x3f_3045_; lean_object* v_ringInst_x3f_3046_; lean_object* v_commRingInst_x3f_3047_; lean_object* v_orderedRingInst_x3f_3048_; lean_object* v_fieldInst_x3f_3049_; lean_object* v_charInst_x3f_3050_; lean_object* v_zero_3051_; lean_object* v_ofNatZero_3052_; lean_object* v_one_x3f_3053_; lean_object* v_leFn_x3f_3054_; lean_object* v_ltFn_x3f_3055_; lean_object* v_addFn_3056_; lean_object* v_zsmulFn_3057_; lean_object* v_nsmulFn_3058_; lean_object* v_zsmulFn_x3f_3059_; lean_object* v_nsmulFn_x3f_3060_; lean_object* v_homomulFn_x3f_3061_; lean_object* v_subFn_3062_; lean_object* v_negFn_3063_; lean_object* v_vars_3064_; lean_object* v_varMap_3065_; lean_object* v_lowers_3066_; lean_object* v_uppers_3067_; lean_object* v_diseqs_3068_; lean_object* v_assignment_3069_; uint8_t v_caseSplits_3070_; lean_object* v_conflict_x3f_3071_; lean_object* v_diseqSplits_3072_; lean_object* v_elimEqs_3073_; lean_object* v_elimStack_3074_; lean_object* v_occurs_3075_; lean_object* v_ignored_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3090_; 
v_v_3033_ = lean_array_fget(v_structs_3020_, v___y_3016_);
v_id_3034_ = lean_ctor_get(v_v_3033_, 0);
v_ringId_x3f_3035_ = lean_ctor_get(v_v_3033_, 1);
v_type_3036_ = lean_ctor_get(v_v_3033_, 2);
v_u_3037_ = lean_ctor_get(v_v_3033_, 3);
v_intModuleInst_3038_ = lean_ctor_get(v_v_3033_, 4);
v_leInst_x3f_3039_ = lean_ctor_get(v_v_3033_, 5);
v_ltInst_x3f_3040_ = lean_ctor_get(v_v_3033_, 6);
v_lawfulOrderLTInst_x3f_3041_ = lean_ctor_get(v_v_3033_, 7);
v_isPreorderInst_x3f_3042_ = lean_ctor_get(v_v_3033_, 8);
v_orderedAddInst_x3f_3043_ = lean_ctor_get(v_v_3033_, 9);
v_isLinearInst_x3f_3044_ = lean_ctor_get(v_v_3033_, 10);
v_noNatDivInst_x3f_3045_ = lean_ctor_get(v_v_3033_, 11);
v_ringInst_x3f_3046_ = lean_ctor_get(v_v_3033_, 12);
v_commRingInst_x3f_3047_ = lean_ctor_get(v_v_3033_, 13);
v_orderedRingInst_x3f_3048_ = lean_ctor_get(v_v_3033_, 14);
v_fieldInst_x3f_3049_ = lean_ctor_get(v_v_3033_, 15);
v_charInst_x3f_3050_ = lean_ctor_get(v_v_3033_, 16);
v_zero_3051_ = lean_ctor_get(v_v_3033_, 17);
v_ofNatZero_3052_ = lean_ctor_get(v_v_3033_, 18);
v_one_x3f_3053_ = lean_ctor_get(v_v_3033_, 19);
v_leFn_x3f_3054_ = lean_ctor_get(v_v_3033_, 20);
v_ltFn_x3f_3055_ = lean_ctor_get(v_v_3033_, 21);
v_addFn_3056_ = lean_ctor_get(v_v_3033_, 22);
v_zsmulFn_3057_ = lean_ctor_get(v_v_3033_, 23);
v_nsmulFn_3058_ = lean_ctor_get(v_v_3033_, 24);
v_zsmulFn_x3f_3059_ = lean_ctor_get(v_v_3033_, 25);
v_nsmulFn_x3f_3060_ = lean_ctor_get(v_v_3033_, 26);
v_homomulFn_x3f_3061_ = lean_ctor_get(v_v_3033_, 27);
v_subFn_3062_ = lean_ctor_get(v_v_3033_, 28);
v_negFn_3063_ = lean_ctor_get(v_v_3033_, 29);
v_vars_3064_ = lean_ctor_get(v_v_3033_, 30);
v_varMap_3065_ = lean_ctor_get(v_v_3033_, 31);
v_lowers_3066_ = lean_ctor_get(v_v_3033_, 32);
v_uppers_3067_ = lean_ctor_get(v_v_3033_, 33);
v_diseqs_3068_ = lean_ctor_get(v_v_3033_, 34);
v_assignment_3069_ = lean_ctor_get(v_v_3033_, 35);
v_caseSplits_3070_ = lean_ctor_get_uint8(v_v_3033_, sizeof(void*)*42);
v_conflict_x3f_3071_ = lean_ctor_get(v_v_3033_, 36);
v_diseqSplits_3072_ = lean_ctor_get(v_v_3033_, 37);
v_elimEqs_3073_ = lean_ctor_get(v_v_3033_, 38);
v_elimStack_3074_ = lean_ctor_get(v_v_3033_, 39);
v_occurs_3075_ = lean_ctor_get(v_v_3033_, 40);
v_ignored_3076_ = lean_ctor_get(v_v_3033_, 41);
v_isSharedCheck_3090_ = !lean_is_exclusive(v_v_3033_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3078_ = v_v_3033_;
v_isShared_3079_ = v_isSharedCheck_3090_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_ignored_3076_);
lean_inc(v_occurs_3075_);
lean_inc(v_elimStack_3074_);
lean_inc(v_elimEqs_3073_);
lean_inc(v_diseqSplits_3072_);
lean_inc(v_conflict_x3f_3071_);
lean_inc(v_assignment_3069_);
lean_inc(v_diseqs_3068_);
lean_inc(v_uppers_3067_);
lean_inc(v_lowers_3066_);
lean_inc(v_varMap_3065_);
lean_inc(v_vars_3064_);
lean_inc(v_negFn_3063_);
lean_inc(v_subFn_3062_);
lean_inc(v_homomulFn_x3f_3061_);
lean_inc(v_nsmulFn_x3f_3060_);
lean_inc(v_zsmulFn_x3f_3059_);
lean_inc(v_nsmulFn_3058_);
lean_inc(v_zsmulFn_3057_);
lean_inc(v_addFn_3056_);
lean_inc(v_ltFn_x3f_3055_);
lean_inc(v_leFn_x3f_3054_);
lean_inc(v_one_x3f_3053_);
lean_inc(v_ofNatZero_3052_);
lean_inc(v_zero_3051_);
lean_inc(v_charInst_x3f_3050_);
lean_inc(v_fieldInst_x3f_3049_);
lean_inc(v_orderedRingInst_x3f_3048_);
lean_inc(v_commRingInst_x3f_3047_);
lean_inc(v_ringInst_x3f_3046_);
lean_inc(v_noNatDivInst_x3f_3045_);
lean_inc(v_isLinearInst_x3f_3044_);
lean_inc(v_orderedAddInst_x3f_3043_);
lean_inc(v_isPreorderInst_x3f_3042_);
lean_inc(v_lawfulOrderLTInst_x3f_3041_);
lean_inc(v_ltInst_x3f_3040_);
lean_inc(v_leInst_x3f_3039_);
lean_inc(v_intModuleInst_3038_);
lean_inc(v_u_3037_);
lean_inc(v_type_3036_);
lean_inc(v_ringId_x3f_3035_);
lean_inc(v_id_3034_);
lean_dec(v_v_3033_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3090_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; lean_object* v_xs_x27_3081_; lean_object* v___x_3082_; lean_object* v___x_3084_; 
v___x_3080_ = lean_box(0);
v_xs_x27_3081_ = lean_array_fset(v_structs_3020_, v___y_3016_, v___x_3080_);
v___x_3082_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3017_, v_diseqs_3068_, v_v_3018_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 34, v___x_3082_);
v___x_3084_ = v___x_3078_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_id_3034_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_ringId_x3f_3035_);
lean_ctor_set(v_reuseFailAlloc_3089_, 2, v_type_3036_);
lean_ctor_set(v_reuseFailAlloc_3089_, 3, v_u_3037_);
lean_ctor_set(v_reuseFailAlloc_3089_, 4, v_intModuleInst_3038_);
lean_ctor_set(v_reuseFailAlloc_3089_, 5, v_leInst_x3f_3039_);
lean_ctor_set(v_reuseFailAlloc_3089_, 6, v_ltInst_x3f_3040_);
lean_ctor_set(v_reuseFailAlloc_3089_, 7, v_lawfulOrderLTInst_x3f_3041_);
lean_ctor_set(v_reuseFailAlloc_3089_, 8, v_isPreorderInst_x3f_3042_);
lean_ctor_set(v_reuseFailAlloc_3089_, 9, v_orderedAddInst_x3f_3043_);
lean_ctor_set(v_reuseFailAlloc_3089_, 10, v_isLinearInst_x3f_3044_);
lean_ctor_set(v_reuseFailAlloc_3089_, 11, v_noNatDivInst_x3f_3045_);
lean_ctor_set(v_reuseFailAlloc_3089_, 12, v_ringInst_x3f_3046_);
lean_ctor_set(v_reuseFailAlloc_3089_, 13, v_commRingInst_x3f_3047_);
lean_ctor_set(v_reuseFailAlloc_3089_, 14, v_orderedRingInst_x3f_3048_);
lean_ctor_set(v_reuseFailAlloc_3089_, 15, v_fieldInst_x3f_3049_);
lean_ctor_set(v_reuseFailAlloc_3089_, 16, v_charInst_x3f_3050_);
lean_ctor_set(v_reuseFailAlloc_3089_, 17, v_zero_3051_);
lean_ctor_set(v_reuseFailAlloc_3089_, 18, v_ofNatZero_3052_);
lean_ctor_set(v_reuseFailAlloc_3089_, 19, v_one_x3f_3053_);
lean_ctor_set(v_reuseFailAlloc_3089_, 20, v_leFn_x3f_3054_);
lean_ctor_set(v_reuseFailAlloc_3089_, 21, v_ltFn_x3f_3055_);
lean_ctor_set(v_reuseFailAlloc_3089_, 22, v_addFn_3056_);
lean_ctor_set(v_reuseFailAlloc_3089_, 23, v_zsmulFn_3057_);
lean_ctor_set(v_reuseFailAlloc_3089_, 24, v_nsmulFn_3058_);
lean_ctor_set(v_reuseFailAlloc_3089_, 25, v_zsmulFn_x3f_3059_);
lean_ctor_set(v_reuseFailAlloc_3089_, 26, v_nsmulFn_x3f_3060_);
lean_ctor_set(v_reuseFailAlloc_3089_, 27, v_homomulFn_x3f_3061_);
lean_ctor_set(v_reuseFailAlloc_3089_, 28, v_subFn_3062_);
lean_ctor_set(v_reuseFailAlloc_3089_, 29, v_negFn_3063_);
lean_ctor_set(v_reuseFailAlloc_3089_, 30, v_vars_3064_);
lean_ctor_set(v_reuseFailAlloc_3089_, 31, v_varMap_3065_);
lean_ctor_set(v_reuseFailAlloc_3089_, 32, v_lowers_3066_);
lean_ctor_set(v_reuseFailAlloc_3089_, 33, v_uppers_3067_);
lean_ctor_set(v_reuseFailAlloc_3089_, 34, v___x_3082_);
lean_ctor_set(v_reuseFailAlloc_3089_, 35, v_assignment_3069_);
lean_ctor_set(v_reuseFailAlloc_3089_, 36, v_conflict_x3f_3071_);
lean_ctor_set(v_reuseFailAlloc_3089_, 37, v_diseqSplits_3072_);
lean_ctor_set(v_reuseFailAlloc_3089_, 38, v_elimEqs_3073_);
lean_ctor_set(v_reuseFailAlloc_3089_, 39, v_elimStack_3074_);
lean_ctor_set(v_reuseFailAlloc_3089_, 40, v_occurs_3075_);
lean_ctor_set(v_reuseFailAlloc_3089_, 41, v_ignored_3076_);
lean_ctor_set_uint8(v_reuseFailAlloc_3089_, sizeof(void*)*42, v_caseSplits_3070_);
v___x_3084_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
lean_object* v___x_3085_; lean_object* v___x_3087_; 
v___x_3085_ = lean_array_fset(v_xs_x27_3081_, v___y_3016_, v___x_3084_);
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v___x_3085_);
v___x_3087_ = v___x_3031_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3085_);
lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_typeIdOf_3021_);
lean_ctor_set(v_reuseFailAlloc_3088_, 2, v_exprToStructId_3022_);
lean_ctor_set(v_reuseFailAlloc_3088_, 3, v_exprToStructIdEntries_3023_);
lean_ctor_set(v_reuseFailAlloc_3088_, 4, v_forbiddenNatModules_3024_);
lean_ctor_set(v_reuseFailAlloc_3088_, 5, v_natStructs_3025_);
lean_ctor_set(v_reuseFailAlloc_3088_, 6, v_natTypeIdOf_3026_);
lean_ctor_set(v_reuseFailAlloc_3088_, 7, v_exprToNatStructId_3027_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed(lean_object* v___y_3100_, lean_object* v_val_3101_, lean_object* v_v_3102_, lean_object* v_s_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(v___y_3100_, v_val_3101_, v_v_3102_, v_s_3103_);
lean_dec(v_v_3102_);
lean_dec(v___y_3100_);
return v_res_3104_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2(void){
_start:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3111_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3112_ = l_Lean_Name_append(v___x_3111_, v___x_3110_);
return v___x_3112_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3121_ = l_Lean_Name_append(v___x_3120_, v___x_3119_);
return v___x_3121_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7(void){
_start:
{
lean_object* v_cls_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v_cls_3126_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3127_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3128_ = l_Lean_Name_append(v___x_3127_, v_cls_3126_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object* v_c_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_){
_start:
{
lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v_toCold_3200_; lean_object* v_options_3201_; lean_object* v_inheritedTraceOptions_3202_; uint8_t v_hasTrace_3203_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; 
v_toCold_3200_ = lean_ctor_get(v_a_3139_, 0);
v_options_3201_ = lean_ctor_get(v_toCold_3200_, 2);
v_inheritedTraceOptions_3202_ = lean_ctor_get(v_toCold_3200_, 11);
v_hasTrace_3203_ = lean_ctor_get_uint8(v_options_3201_, sizeof(void*)*1);
if (v_hasTrace_3203_ == 0)
{
v___y_3205_ = v_a_3130_;
v___y_3206_ = v_a_3131_;
v___y_3207_ = v_a_3132_;
v___y_3208_ = v_a_3133_;
v___y_3209_ = v_a_3134_;
v___y_3210_ = v_a_3135_;
v___y_3211_ = v_a_3136_;
v___y_3212_ = v_a_3137_;
v___y_3213_ = v_a_3138_;
v___y_3214_ = v_a_3139_;
v___y_3215_ = v_a_3140_;
goto v___jp_3204_;
}
else
{
lean_object* v_cls_3276_; lean_object* v___x_3277_; uint8_t v___x_3278_; 
v_cls_3276_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3277_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_3278_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3202_, v_options_3201_, v___x_3277_);
if (v___x_3278_ == 0)
{
v___y_3205_ = v_a_3130_;
v___y_3206_ = v_a_3131_;
v___y_3207_ = v_a_3132_;
v___y_3208_ = v_a_3133_;
v___y_3209_ = v_a_3134_;
v___y_3210_ = v_a_3135_;
v___y_3211_ = v_a_3136_;
v___y_3212_ = v_a_3137_;
v___y_3213_ = v_a_3138_;
v___y_3214_ = v_a_3139_;
v___y_3215_ = v_a_3140_;
goto v___jp_3204_;
}
else
{
lean_object* v___x_3279_; 
v___x_3279_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_a_3280_);
lean_dec_ref_known(v___x_3279_, 1);
v___x_3281_ = l_Lean_MessageData_ofExpr(v_a_3280_);
v___x_3282_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_3276_, v___x_3281_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_dec_ref_known(v___x_3282_, 1);
v___y_3205_ = v_a_3130_;
v___y_3206_ = v_a_3131_;
v___y_3207_ = v_a_3132_;
v___y_3208_ = v_a_3133_;
v___y_3209_ = v_a_3134_;
v___y_3210_ = v_a_3135_;
v___y_3211_ = v_a_3136_;
v___y_3212_ = v_a_3137_;
v___y_3213_ = v_a_3138_;
v___y_3214_ = v_a_3139_;
v___y_3215_ = v_a_3140_;
goto v___jp_3204_;
}
else
{
lean_dec_ref(v_c_3129_);
return v___x_3282_;
}
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec_ref(v_c_3129_);
v_a_3283_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3279_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3279_);
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
}
v___jp_3142_:
{
lean_object* v___f_3159_; lean_object* v___x_3160_; 
lean_inc(v___y_3148_);
v___f_3159_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3159_, 0, v___y_3148_);
lean_closure_set(v___f_3159_, 1, v___y_3144_);
lean_closure_set(v___f_3159_, 2, v___y_3143_);
v___x_3160_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_3146_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
lean_dec_ref_known(v___x_3160_, 1);
v___x_3161_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3162_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3161_, v___f_3159_, v___y_3149_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v___x_3163_; 
lean_dec_ref_known(v___x_3162_, 1);
v___x_3163_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3176_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3166_ = v___x_3163_;
v_isShared_3167_ = v_isSharedCheck_3176_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3163_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3176_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
uint8_t v___x_3168_; uint8_t v___x_3169_; uint8_t v___x_3170_; 
v___x_3168_ = 0;
v___x_3169_ = lean_unbox(v_a_3164_);
lean_dec(v_a_3164_);
v___x_3170_ = l_Lean_instBEqLBool_beq(v___x_3169_, v___x_3168_);
if (v___x_3170_ == 0)
{
lean_object* v___x_3171_; lean_object* v___x_3173_; 
lean_dec(v___y_3145_);
v___x_3171_ = lean_box(0);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 0, v___x_3171_);
v___x_3173_ = v___x_3166_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3171_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
else
{
lean_object* v___x_3175_; 
lean_del_object(v___x_3166_);
v___x_3175_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_3145_, v___y_3148_, v___y_3149_);
return v___x_3175_;
}
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec(v___y_3145_);
v_a_3177_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3163_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3163_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
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
else
{
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3145_);
return v___x_3162_;
}
}
else
{
lean_dec_ref(v___f_3159_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3145_);
return v___x_3160_;
}
}
v___jp_3185_:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3198_, 0, v___y_3186_);
v___x_3199_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(v___x_3198_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3199_;
}
v___jp_3204_:
{
lean_object* v___x_3216_; 
lean_inc_ref(v___y_3214_);
v___x_3216_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_3129_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3267_; 
v_a_3217_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3219_ = v___x_3216_;
v_isShared_3220_ = v_isSharedCheck_3267_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3216_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3267_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
if (lean_obj_tag(v_a_3217_) == 1)
{
lean_object* v_val_3221_; lean_object* v_p_3222_; 
lean_del_object(v___x_3219_);
v_val_3221_ = lean_ctor_get(v_a_3217_, 0);
lean_inc(v_val_3221_);
lean_dec_ref_known(v_a_3217_, 1);
v_p_3222_ = lean_ctor_get(v_val_3221_, 0);
if (lean_obj_tag(v_p_3222_) == 0)
{
lean_object* v_toCold_3223_; lean_object* v_options_3224_; uint8_t v_hasTrace_3225_; 
v_toCold_3223_ = lean_ctor_get(v___y_3214_, 0);
v_options_3224_ = lean_ctor_get(v_toCold_3223_, 2);
v_hasTrace_3225_ = lean_ctor_get_uint8(v_options_3224_, sizeof(void*)*1);
if (v_hasTrace_3225_ == 0)
{
v___y_3186_ = v_val_3221_;
v___y_3187_ = v___y_3205_;
v___y_3188_ = v___y_3206_;
v___y_3189_ = v___y_3207_;
v___y_3190_ = v___y_3208_;
v___y_3191_ = v___y_3209_;
v___y_3192_ = v___y_3210_;
v___y_3193_ = v___y_3211_;
v___y_3194_ = v___y_3212_;
v___y_3195_ = v___y_3213_;
v___y_3196_ = v___y_3214_;
v___y_3197_ = v___y_3215_;
goto v___jp_3185_;
}
else
{
lean_object* v_inheritedTraceOptions_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; uint8_t v___x_3229_; 
v_inheritedTraceOptions_3226_ = lean_ctor_get(v_toCold_3223_, 11);
v___x_3227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3228_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2);
v___x_3229_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3226_, v_options_3224_, v___x_3228_);
if (v___x_3229_ == 0)
{
v___y_3186_ = v_val_3221_;
v___y_3187_ = v___y_3205_;
v___y_3188_ = v___y_3206_;
v___y_3189_ = v___y_3207_;
v___y_3190_ = v___y_3208_;
v___y_3191_ = v___y_3209_;
v___y_3192_ = v___y_3210_;
v___y_3193_ = v___y_3211_;
v___y_3194_ = v___y_3212_;
v___y_3195_ = v___y_3213_;
v___y_3196_ = v___y_3214_;
v___y_3197_ = v___y_3215_;
goto v___jp_3185_;
}
else
{
lean_object* v___x_3230_; 
v___x_3230_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3221_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3230_, 1);
v___x_3232_ = l_Lean_MessageData_ofExpr(v_a_3231_);
v___x_3233_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3227_, v___x_3232_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_dec_ref_known(v___x_3233_, 1);
v___y_3186_ = v_val_3221_;
v___y_3187_ = v___y_3205_;
v___y_3188_ = v___y_3206_;
v___y_3189_ = v___y_3207_;
v___y_3190_ = v___y_3208_;
v___y_3191_ = v___y_3209_;
v___y_3192_ = v___y_3210_;
v___y_3193_ = v___y_3211_;
v___y_3194_ = v___y_3212_;
v___y_3195_ = v___y_3213_;
v___y_3196_ = v___y_3214_;
v___y_3197_ = v___y_3215_;
goto v___jp_3185_;
}
else
{
lean_dec(v_val_3221_);
return v___x_3233_;
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec(v_val_3221_);
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
else
{
lean_object* v_toCold_3242_; lean_object* v_options_3243_; uint8_t v_hasTrace_3244_; 
lean_inc_ref(v_p_3222_);
v_toCold_3242_ = lean_ctor_get(v___y_3214_, 0);
v_options_3243_ = lean_ctor_get(v_toCold_3242_, 2);
v_hasTrace_3244_ = lean_ctor_get_uint8(v_options_3243_, sizeof(void*)*1);
if (v_hasTrace_3244_ == 0)
{
lean_object* v_v_3245_; 
v_v_3245_ = lean_ctor_get(v_p_3222_, 1);
lean_inc_n(v_v_3245_, 2);
lean_inc(v_val_3221_);
v___y_3143_ = v_v_3245_;
v___y_3144_ = v_val_3221_;
v___y_3145_ = v_v_3245_;
v___y_3146_ = v_p_3222_;
v___y_3147_ = v_val_3221_;
v___y_3148_ = v___y_3205_;
v___y_3149_ = v___y_3206_;
v___y_3150_ = v___y_3207_;
v___y_3151_ = v___y_3208_;
v___y_3152_ = v___y_3209_;
v___y_3153_ = v___y_3210_;
v___y_3154_ = v___y_3211_;
v___y_3155_ = v___y_3212_;
v___y_3156_ = v___y_3213_;
v___y_3157_ = v___y_3214_;
v___y_3158_ = v___y_3215_;
goto v___jp_3142_;
}
else
{
lean_object* v_v_3246_; lean_object* v_inheritedTraceOptions_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; uint8_t v___x_3250_; 
v_v_3246_ = lean_ctor_get(v_p_3222_, 1);
lean_inc(v_v_3246_);
v_inheritedTraceOptions_3247_ = lean_ctor_get(v_toCold_3242_, 11);
v___x_3248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3249_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_3250_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3247_, v_options_3243_, v___x_3249_);
if (v___x_3250_ == 0)
{
lean_inc(v_val_3221_);
lean_inc(v_v_3246_);
v___y_3143_ = v_v_3246_;
v___y_3144_ = v_val_3221_;
v___y_3145_ = v_v_3246_;
v___y_3146_ = v_p_3222_;
v___y_3147_ = v_val_3221_;
v___y_3148_ = v___y_3205_;
v___y_3149_ = v___y_3206_;
v___y_3150_ = v___y_3207_;
v___y_3151_ = v___y_3208_;
v___y_3152_ = v___y_3209_;
v___y_3153_ = v___y_3210_;
v___y_3154_ = v___y_3211_;
v___y_3155_ = v___y_3212_;
v___y_3156_ = v___y_3213_;
v___y_3157_ = v___y_3214_;
v___y_3158_ = v___y_3215_;
goto v___jp_3142_;
}
else
{
lean_object* v___x_3251_; 
v___x_3251_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3221_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_a_3252_);
lean_dec_ref_known(v___x_3251_, 1);
v___x_3253_ = l_Lean_MessageData_ofExpr(v_a_3252_);
v___x_3254_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3248_, v___x_3253_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_dec_ref_known(v___x_3254_, 1);
lean_inc(v_val_3221_);
lean_inc(v_v_3246_);
v___y_3143_ = v_v_3246_;
v___y_3144_ = v_val_3221_;
v___y_3145_ = v_v_3246_;
v___y_3146_ = v_p_3222_;
v___y_3147_ = v_val_3221_;
v___y_3148_ = v___y_3205_;
v___y_3149_ = v___y_3206_;
v___y_3150_ = v___y_3207_;
v___y_3151_ = v___y_3208_;
v___y_3152_ = v___y_3209_;
v___y_3153_ = v___y_3210_;
v___y_3154_ = v___y_3211_;
v___y_3155_ = v___y_3212_;
v___y_3156_ = v___y_3213_;
v___y_3157_ = v___y_3214_;
v___y_3158_ = v___y_3215_;
goto v___jp_3142_;
}
else
{
lean_dec(v_v_3246_);
lean_dec_ref_known(v_p_3222_, 3);
lean_dec(v_val_3221_);
return v___x_3254_;
}
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec(v_v_3246_);
lean_dec_ref_known(v_p_3222_, 3);
lean_dec(v_val_3221_);
v_a_3255_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3251_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3251_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3263_; lean_object* v___x_3265_; 
lean_dec(v_a_3217_);
v___x_3263_ = lean_box(0);
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 0, v___x_3263_);
v___x_3265_ = v___x_3219_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3263_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
else
{
lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
v_a_3268_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3270_ = v___x_3216_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v___x_3216_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3268_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___boxed(lean_object* v_c_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_c_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_);
lean_dec(v_a_3302_);
lean_dec_ref(v_a_3301_);
lean_dec(v_a_3300_);
lean_dec_ref(v_a_3299_);
lean_dec(v_a_3298_);
lean_dec_ref(v_a_3297_);
lean_dec(v_a_3296_);
lean_dec_ref(v_a_3295_);
lean_dec(v_a_3294_);
lean_dec(v_a_3293_);
lean_dec(v_a_3292_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_3305_, lean_object* v_as_3306_, size_t v_sz_3307_, size_t v_i_3308_, lean_object* v_b_3309_){
_start:
{
uint8_t v___x_3310_; 
v___x_3310_ = lean_usize_dec_lt(v_i_3308_, v_sz_3307_);
if (v___x_3310_ == 0)
{
return v_b_3309_;
}
else
{
lean_object* v_snd_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3352_; 
v_snd_3311_ = lean_ctor_get(v_b_3309_, 1);
v_isSharedCheck_3352_ = !lean_is_exclusive(v_b_3309_);
if (v_isSharedCheck_3352_ == 0)
{
lean_object* v_unused_3353_; 
v_unused_3353_ = lean_ctor_get(v_b_3309_, 0);
lean_dec(v_unused_3353_);
v___x_3313_ = v_b_3309_;
v_isShared_3314_ = v_isSharedCheck_3352_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_snd_3311_);
lean_dec(v_b_3309_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3352_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v_fst_3315_; lean_object* v_snd_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3351_; 
v_fst_3315_ = lean_ctor_get(v_snd_3311_, 0);
v_snd_3316_ = lean_ctor_get(v_snd_3311_, 1);
v_isSharedCheck_3351_ = !lean_is_exclusive(v_snd_3311_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3318_ = v_snd_3311_;
v_isShared_3319_ = v_isSharedCheck_3351_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_snd_3316_);
lean_inc(v_fst_3315_);
lean_dec(v_snd_3311_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3351_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v_a_3320_; lean_object* v_p_3321_; lean_object* v___x_3322_; lean_object* v_a_3324_; lean_object* v_b_3331_; lean_object* v___x_3332_; uint8_t v___x_3333_; 
v_a_3320_ = lean_array_uget(v_as_3306_, v_i_3308_);
v_p_3321_ = lean_ctor_get(v_a_3320_, 0);
v___x_3322_ = lean_box(0);
v_b_3331_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3321_, v_x_3305_);
v___x_3332_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3333_ = lean_int_dec_eq(v_b_3331_, v___x_3332_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3335_; 
lean_inc(v_a_3320_);
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 1, v_a_3320_);
lean_ctor_set(v___x_3313_, 0, v_b_3331_);
v___x_3335_ = v___x_3313_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_b_3331_);
lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_a_3320_);
v___x_3335_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3343_; 
v_isSharedCheck_3343_ = !lean_is_exclusive(v_a_3320_);
if (v_isSharedCheck_3343_ == 0)
{
lean_object* v_unused_3344_; lean_object* v_unused_3345_; 
v_unused_3344_ = lean_ctor_get(v_a_3320_, 1);
lean_dec(v_unused_3344_);
v_unused_3345_ = lean_ctor_get(v_a_3320_, 0);
lean_dec(v_unused_3345_);
v___x_3337_ = v_a_3320_;
v_isShared_3338_ = v_isSharedCheck_3343_;
goto v_resetjp_3336_;
}
else
{
lean_dec(v_a_3320_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3343_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v_todo_3339_; lean_object* v___x_3341_; 
v_todo_3339_ = lean_array_push(v_snd_3316_, v___x_3335_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 1, v_todo_3339_);
lean_ctor_set(v___x_3337_, 0, v_fst_3315_);
v___x_3341_ = v___x_3337_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_fst_3315_);
lean_ctor_set(v_reuseFailAlloc_3342_, 1, v_todo_3339_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
v_a_3324_ = v___x_3341_;
goto v___jp_3323_;
}
}
}
}
else
{
lean_object* v_cs_x27_3347_; lean_object* v___x_3349_; 
lean_dec(v_b_3331_);
v_cs_x27_3347_ = l_Lean_PersistentArray_push___redArg(v_fst_3315_, v_a_3320_);
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 1, v_snd_3316_);
lean_ctor_set(v___x_3313_, 0, v_cs_x27_3347_);
v___x_3349_ = v___x_3313_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_cs_x27_3347_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_snd_3316_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
v_a_3324_ = v___x_3349_;
goto v___jp_3323_;
}
}
v___jp_3323_:
{
lean_object* v___x_3326_; 
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 1, v_a_3324_);
lean_ctor_set(v___x_3318_, 0, v___x_3322_);
v___x_3326_ = v___x_3318_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3322_);
lean_ctor_set(v_reuseFailAlloc_3330_, 1, v_a_3324_);
v___x_3326_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
size_t v___x_3327_; size_t v___x_3328_; 
v___x_3327_ = ((size_t)1ULL);
v___x_3328_ = lean_usize_add(v_i_3308_, v___x_3327_);
v_i_3308_ = v___x_3328_;
v_b_3309_ = v___x_3326_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_3354_, lean_object* v_as_3355_, lean_object* v_sz_3356_, lean_object* v_i_3357_, lean_object* v_b_3358_){
_start:
{
size_t v_sz_boxed_3359_; size_t v_i_boxed_3360_; lean_object* v_res_3361_; 
v_sz_boxed_3359_ = lean_unbox_usize(v_sz_3356_);
lean_dec(v_sz_3356_);
v_i_boxed_3360_ = lean_unbox_usize(v_i_3357_);
lean_dec(v_i_3357_);
v_res_3361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3354_, v_as_3355_, v_sz_boxed_3359_, v_i_boxed_3360_, v_b_3358_);
lean_dec_ref(v_as_3355_);
lean_dec(v_x_3354_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(lean_object* v_x_3362_, lean_object* v_as_3363_, size_t v_sz_3364_, size_t v_i_3365_, lean_object* v_b_3366_){
_start:
{
uint8_t v___x_3367_; 
v___x_3367_ = lean_usize_dec_lt(v_i_3365_, v_sz_3364_);
if (v___x_3367_ == 0)
{
return v_b_3366_;
}
else
{
lean_object* v_snd_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3409_; 
v_snd_3368_ = lean_ctor_get(v_b_3366_, 1);
v_isSharedCheck_3409_ = !lean_is_exclusive(v_b_3366_);
if (v_isSharedCheck_3409_ == 0)
{
lean_object* v_unused_3410_; 
v_unused_3410_ = lean_ctor_get(v_b_3366_, 0);
lean_dec(v_unused_3410_);
v___x_3370_ = v_b_3366_;
v_isShared_3371_ = v_isSharedCheck_3409_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_snd_3368_);
lean_dec(v_b_3366_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3409_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v_fst_3372_; lean_object* v_snd_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3408_; 
v_fst_3372_ = lean_ctor_get(v_snd_3368_, 0);
v_snd_3373_ = lean_ctor_get(v_snd_3368_, 1);
v_isSharedCheck_3408_ = !lean_is_exclusive(v_snd_3368_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3375_ = v_snd_3368_;
v_isShared_3376_ = v_isSharedCheck_3408_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_snd_3373_);
lean_inc(v_fst_3372_);
lean_dec(v_snd_3368_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3408_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v_a_3377_; lean_object* v_p_3378_; lean_object* v___x_3379_; lean_object* v_a_3381_; lean_object* v_b_3388_; lean_object* v___x_3389_; uint8_t v___x_3390_; 
v_a_3377_ = lean_array_uget(v_as_3363_, v_i_3365_);
v_p_3378_ = lean_ctor_get(v_a_3377_, 0);
v___x_3379_ = lean_box(0);
v_b_3388_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3378_, v_x_3362_);
v___x_3389_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3390_ = lean_int_dec_eq(v_b_3388_, v___x_3389_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3392_; 
lean_inc(v_a_3377_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 1, v_a_3377_);
lean_ctor_set(v___x_3370_, 0, v_b_3388_);
v___x_3392_ = v___x_3370_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_b_3388_);
lean_ctor_set(v_reuseFailAlloc_3403_, 1, v_a_3377_);
v___x_3392_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3400_; 
v_isSharedCheck_3400_ = !lean_is_exclusive(v_a_3377_);
if (v_isSharedCheck_3400_ == 0)
{
lean_object* v_unused_3401_; lean_object* v_unused_3402_; 
v_unused_3401_ = lean_ctor_get(v_a_3377_, 1);
lean_dec(v_unused_3401_);
v_unused_3402_ = lean_ctor_get(v_a_3377_, 0);
lean_dec(v_unused_3402_);
v___x_3394_ = v_a_3377_;
v_isShared_3395_ = v_isSharedCheck_3400_;
goto v_resetjp_3393_;
}
else
{
lean_dec(v_a_3377_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3400_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v_todo_3396_; lean_object* v___x_3398_; 
v_todo_3396_ = lean_array_push(v_snd_3373_, v___x_3392_);
if (v_isShared_3395_ == 0)
{
lean_ctor_set(v___x_3394_, 1, v_todo_3396_);
lean_ctor_set(v___x_3394_, 0, v_fst_3372_);
v___x_3398_ = v___x_3394_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_fst_3372_);
lean_ctor_set(v_reuseFailAlloc_3399_, 1, v_todo_3396_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
v_a_3381_ = v___x_3398_;
goto v___jp_3380_;
}
}
}
}
else
{
lean_object* v_cs_x27_3404_; lean_object* v___x_3406_; 
lean_dec(v_b_3388_);
v_cs_x27_3404_ = l_Lean_PersistentArray_push___redArg(v_fst_3372_, v_a_3377_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 1, v_snd_3373_);
lean_ctor_set(v___x_3370_, 0, v_cs_x27_3404_);
v___x_3406_ = v___x_3370_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_cs_x27_3404_);
lean_ctor_set(v_reuseFailAlloc_3407_, 1, v_snd_3373_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
v_a_3381_ = v___x_3406_;
goto v___jp_3380_;
}
}
v___jp_3380_:
{
lean_object* v___x_3383_; 
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 1, v_a_3381_);
lean_ctor_set(v___x_3375_, 0, v___x_3379_);
v___x_3383_ = v___x_3375_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3379_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v_a_3381_);
v___x_3383_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
size_t v___x_3384_; size_t v___x_3385_; lean_object* v___x_3386_; 
v___x_3384_ = ((size_t)1ULL);
v___x_3385_ = lean_usize_add(v_i_3365_, v___x_3384_);
v___x_3386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3362_, v_as_3363_, v_sz_3364_, v___x_3385_, v___x_3383_);
return v___x_3386_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_3411_, lean_object* v_as_3412_, lean_object* v_sz_3413_, lean_object* v_i_3414_, lean_object* v_b_3415_){
_start:
{
size_t v_sz_boxed_3416_; size_t v_i_boxed_3417_; lean_object* v_res_3418_; 
v_sz_boxed_3416_ = lean_unbox_usize(v_sz_3413_);
lean_dec(v_sz_3413_);
v_i_boxed_3417_ = lean_unbox_usize(v_i_3414_);
lean_dec(v_i_3414_);
v_res_3418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3411_, v_as_3412_, v_sz_boxed_3416_, v_i_boxed_3417_, v_b_3415_);
lean_dec_ref(v_as_3412_);
lean_dec(v_x_3411_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_3419_, lean_object* v_as_3420_, size_t v_sz_3421_, size_t v_i_3422_, lean_object* v_b_3423_){
_start:
{
uint8_t v___x_3424_; 
v___x_3424_ = lean_usize_dec_lt(v_i_3422_, v_sz_3421_);
if (v___x_3424_ == 0)
{
return v_b_3423_;
}
else
{
lean_object* v_snd_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3466_; 
v_snd_3425_ = lean_ctor_get(v_b_3423_, 1);
v_isSharedCheck_3466_ = !lean_is_exclusive(v_b_3423_);
if (v_isSharedCheck_3466_ == 0)
{
lean_object* v_unused_3467_; 
v_unused_3467_ = lean_ctor_get(v_b_3423_, 0);
lean_dec(v_unused_3467_);
v___x_3427_ = v_b_3423_;
v_isShared_3428_ = v_isSharedCheck_3466_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_snd_3425_);
lean_dec(v_b_3423_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3466_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v_fst_3429_; lean_object* v_snd_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3465_; 
v_fst_3429_ = lean_ctor_get(v_snd_3425_, 0);
v_snd_3430_ = lean_ctor_get(v_snd_3425_, 1);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_snd_3425_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3432_ = v_snd_3425_;
v_isShared_3433_ = v_isSharedCheck_3465_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_snd_3430_);
lean_inc(v_fst_3429_);
lean_dec(v_snd_3425_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3465_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v_a_3434_; lean_object* v_p_3435_; lean_object* v___x_3436_; lean_object* v_a_3438_; lean_object* v_b_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; 
v_a_3434_ = lean_array_uget(v_as_3420_, v_i_3422_);
v_p_3435_ = lean_ctor_get(v_a_3434_, 0);
v___x_3436_ = lean_box(0);
v_b_3445_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3435_, v_x_3419_);
v___x_3446_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3447_ = lean_int_dec_eq(v_b_3445_, v___x_3446_);
if (v___x_3447_ == 0)
{
lean_object* v___x_3449_; 
lean_inc(v_a_3434_);
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 1, v_a_3434_);
lean_ctor_set(v___x_3427_, 0, v_b_3445_);
v___x_3449_ = v___x_3427_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_b_3445_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v_a_3434_);
v___x_3449_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3457_; 
v_isSharedCheck_3457_ = !lean_is_exclusive(v_a_3434_);
if (v_isSharedCheck_3457_ == 0)
{
lean_object* v_unused_3458_; lean_object* v_unused_3459_; 
v_unused_3458_ = lean_ctor_get(v_a_3434_, 1);
lean_dec(v_unused_3458_);
v_unused_3459_ = lean_ctor_get(v_a_3434_, 0);
lean_dec(v_unused_3459_);
v___x_3451_ = v_a_3434_;
v_isShared_3452_ = v_isSharedCheck_3457_;
goto v_resetjp_3450_;
}
else
{
lean_dec(v_a_3434_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3457_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v_todo_3453_; lean_object* v___x_3455_; 
v_todo_3453_ = lean_array_push(v_snd_3430_, v___x_3449_);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 1, v_todo_3453_);
lean_ctor_set(v___x_3451_, 0, v_fst_3429_);
v___x_3455_ = v___x_3451_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_fst_3429_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v_todo_3453_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
v_a_3438_ = v___x_3455_;
goto v___jp_3437_;
}
}
}
}
else
{
lean_object* v_cs_x27_3461_; lean_object* v___x_3463_; 
lean_dec(v_b_3445_);
v_cs_x27_3461_ = l_Lean_PersistentArray_push___redArg(v_fst_3429_, v_a_3434_);
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 1, v_snd_3430_);
lean_ctor_set(v___x_3427_, 0, v_cs_x27_3461_);
v___x_3463_ = v___x_3427_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_cs_x27_3461_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_snd_3430_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
v_a_3438_ = v___x_3463_;
goto v___jp_3437_;
}
}
v___jp_3437_:
{
lean_object* v___x_3440_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v_a_3438_);
lean_ctor_set(v___x_3432_, 0, v___x_3436_);
v___x_3440_ = v___x_3432_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3436_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_a_3438_);
v___x_3440_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
size_t v___x_3441_; size_t v___x_3442_; 
v___x_3441_ = ((size_t)1ULL);
v___x_3442_ = lean_usize_add(v_i_3422_, v___x_3441_);
v_i_3422_ = v___x_3442_;
v_b_3423_ = v___x_3440_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3468_, lean_object* v_as_3469_, lean_object* v_sz_3470_, lean_object* v_i_3471_, lean_object* v_b_3472_){
_start:
{
size_t v_sz_boxed_3473_; size_t v_i_boxed_3474_; lean_object* v_res_3475_; 
v_sz_boxed_3473_ = lean_unbox_usize(v_sz_3470_);
lean_dec(v_sz_3470_);
v_i_boxed_3474_ = lean_unbox_usize(v_i_3471_);
lean_dec(v_i_3471_);
v_res_3475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3468_, v_as_3469_, v_sz_boxed_3473_, v_i_boxed_3474_, v_b_3472_);
lean_dec_ref(v_as_3469_);
lean_dec(v_x_3468_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_3476_, lean_object* v_as_3477_, size_t v_sz_3478_, size_t v_i_3479_, lean_object* v_b_3480_){
_start:
{
uint8_t v___x_3481_; 
v___x_3481_ = lean_usize_dec_lt(v_i_3479_, v_sz_3478_);
if (v___x_3481_ == 0)
{
return v_b_3480_;
}
else
{
lean_object* v_snd_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3523_; 
v_snd_3482_ = lean_ctor_get(v_b_3480_, 1);
v_isSharedCheck_3523_ = !lean_is_exclusive(v_b_3480_);
if (v_isSharedCheck_3523_ == 0)
{
lean_object* v_unused_3524_; 
v_unused_3524_ = lean_ctor_get(v_b_3480_, 0);
lean_dec(v_unused_3524_);
v___x_3484_ = v_b_3480_;
v_isShared_3485_ = v_isSharedCheck_3523_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_snd_3482_);
lean_dec(v_b_3480_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3523_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v_fst_3486_; lean_object* v_snd_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3522_; 
v_fst_3486_ = lean_ctor_get(v_snd_3482_, 0);
v_snd_3487_ = lean_ctor_get(v_snd_3482_, 1);
v_isSharedCheck_3522_ = !lean_is_exclusive(v_snd_3482_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3489_ = v_snd_3482_;
v_isShared_3490_ = v_isSharedCheck_3522_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_snd_3487_);
lean_inc(v_fst_3486_);
lean_dec(v_snd_3482_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3522_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v_a_3491_; lean_object* v_p_3492_; lean_object* v___x_3493_; lean_object* v_a_3495_; lean_object* v_b_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v_a_3491_ = lean_array_uget(v_as_3477_, v_i_3479_);
v_p_3492_ = lean_ctor_get(v_a_3491_, 0);
v___x_3493_ = lean_box(0);
v_b_3502_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3492_, v_x_3476_);
v___x_3503_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3504_ = lean_int_dec_eq(v_b_3502_, v___x_3503_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3506_; 
lean_inc(v_a_3491_);
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 1, v_a_3491_);
lean_ctor_set(v___x_3484_, 0, v_b_3502_);
v___x_3506_ = v___x_3484_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_b_3502_);
lean_ctor_set(v_reuseFailAlloc_3517_, 1, v_a_3491_);
v___x_3506_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3514_; 
v_isSharedCheck_3514_ = !lean_is_exclusive(v_a_3491_);
if (v_isSharedCheck_3514_ == 0)
{
lean_object* v_unused_3515_; lean_object* v_unused_3516_; 
v_unused_3515_ = lean_ctor_get(v_a_3491_, 1);
lean_dec(v_unused_3515_);
v_unused_3516_ = lean_ctor_get(v_a_3491_, 0);
lean_dec(v_unused_3516_);
v___x_3508_ = v_a_3491_;
v_isShared_3509_ = v_isSharedCheck_3514_;
goto v_resetjp_3507_;
}
else
{
lean_dec(v_a_3491_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3514_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v_todo_3510_; lean_object* v___x_3512_; 
v_todo_3510_ = lean_array_push(v_snd_3487_, v___x_3506_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 1, v_todo_3510_);
lean_ctor_set(v___x_3508_, 0, v_fst_3486_);
v___x_3512_ = v___x_3508_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_fst_3486_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v_todo_3510_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
v_a_3495_ = v___x_3512_;
goto v___jp_3494_;
}
}
}
}
else
{
lean_object* v_cs_x27_3518_; lean_object* v___x_3520_; 
lean_dec(v_b_3502_);
v_cs_x27_3518_ = l_Lean_PersistentArray_push___redArg(v_fst_3486_, v_a_3491_);
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 1, v_snd_3487_);
lean_ctor_set(v___x_3484_, 0, v_cs_x27_3518_);
v___x_3520_ = v___x_3484_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_cs_x27_3518_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_snd_3487_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
v_a_3495_ = v___x_3520_;
goto v___jp_3494_;
}
}
v___jp_3494_:
{
lean_object* v___x_3497_; 
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 1, v_a_3495_);
lean_ctor_set(v___x_3489_, 0, v___x_3493_);
v___x_3497_ = v___x_3489_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3493_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v_a_3495_);
v___x_3497_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
size_t v___x_3498_; size_t v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = ((size_t)1ULL);
v___x_3499_ = lean_usize_add(v_i_3479_, v___x_3498_);
v___x_3500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3476_, v_as_3477_, v_sz_3478_, v___x_3499_, v___x_3497_);
return v___x_3500_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_3525_, lean_object* v_as_3526_, lean_object* v_sz_3527_, lean_object* v_i_3528_, lean_object* v_b_3529_){
_start:
{
size_t v_sz_boxed_3530_; size_t v_i_boxed_3531_; lean_object* v_res_3532_; 
v_sz_boxed_3530_ = lean_unbox_usize(v_sz_3527_);
lean_dec(v_sz_3527_);
v_i_boxed_3531_ = lean_unbox_usize(v_i_3528_);
lean_dec(v_i_3528_);
v_res_3532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3525_, v_as_3526_, v_sz_boxed_3530_, v_i_boxed_3531_, v_b_3529_);
lean_dec_ref(v_as_3526_);
lean_dec(v_x_3525_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(lean_object* v_init_3533_, lean_object* v_x_3534_, lean_object* v_n_3535_, lean_object* v_b_3536_){
_start:
{
if (lean_obj_tag(v_n_3535_) == 0)
{
lean_object* v_cs_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; size_t v_sz_3540_; size_t v___x_3541_; lean_object* v___x_3542_; lean_object* v_fst_3543_; 
v_cs_3537_ = lean_ctor_get(v_n_3535_, 0);
v___x_3538_ = lean_box(0);
v___x_3539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3538_);
lean_ctor_set(v___x_3539_, 1, v_b_3536_);
v_sz_3540_ = lean_array_size(v_cs_3537_);
v___x_3541_ = ((size_t)0ULL);
v___x_3542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3533_, v_x_3534_, v_cs_3537_, v_sz_3540_, v___x_3541_, v___x_3539_);
v_fst_3543_ = lean_ctor_get(v___x_3542_, 0);
if (lean_obj_tag(v_fst_3543_) == 0)
{
lean_object* v_snd_3544_; lean_object* v___x_3545_; 
v_snd_3544_ = lean_ctor_get(v___x_3542_, 1);
lean_inc(v_snd_3544_);
lean_dec_ref(v___x_3542_);
v___x_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3545_, 0, v_snd_3544_);
return v___x_3545_;
}
else
{
lean_object* v_val_3546_; 
lean_inc_ref(v_fst_3543_);
lean_dec_ref(v___x_3542_);
v_val_3546_ = lean_ctor_get(v_fst_3543_, 0);
lean_inc(v_val_3546_);
lean_dec_ref_known(v_fst_3543_, 1);
return v_val_3546_;
}
}
else
{
lean_object* v_vs_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; size_t v_sz_3550_; size_t v___x_3551_; lean_object* v___x_3552_; lean_object* v_fst_3553_; 
v_vs_3547_ = lean_ctor_get(v_n_3535_, 0);
v___x_3548_ = lean_box(0);
v___x_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
lean_ctor_set(v___x_3549_, 1, v_b_3536_);
v_sz_3550_ = lean_array_size(v_vs_3547_);
v___x_3551_ = ((size_t)0ULL);
v___x_3552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3534_, v_vs_3547_, v_sz_3550_, v___x_3551_, v___x_3549_);
v_fst_3553_ = lean_ctor_get(v___x_3552_, 0);
if (lean_obj_tag(v_fst_3553_) == 0)
{
lean_object* v_snd_3554_; lean_object* v___x_3555_; 
v_snd_3554_ = lean_ctor_get(v___x_3552_, 1);
lean_inc(v_snd_3554_);
lean_dec_ref(v___x_3552_);
v___x_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3555_, 0, v_snd_3554_);
return v___x_3555_;
}
else
{
lean_object* v_val_3556_; 
lean_inc_ref(v_fst_3553_);
lean_dec_ref(v___x_3552_);
v_val_3556_ = lean_ctor_get(v_fst_3553_, 0);
lean_inc(v_val_3556_);
lean_dec_ref_known(v_fst_3553_, 1);
return v_val_3556_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3557_, lean_object* v_x_3558_, lean_object* v_as_3559_, size_t v_sz_3560_, size_t v_i_3561_, lean_object* v_b_3562_){
_start:
{
uint8_t v___x_3563_; 
v___x_3563_ = lean_usize_dec_lt(v_i_3561_, v_sz_3560_);
if (v___x_3563_ == 0)
{
return v_b_3562_;
}
else
{
lean_object* v_snd_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3582_; 
v_snd_3564_ = lean_ctor_get(v_b_3562_, 1);
v_isSharedCheck_3582_ = !lean_is_exclusive(v_b_3562_);
if (v_isSharedCheck_3582_ == 0)
{
lean_object* v_unused_3583_; 
v_unused_3583_ = lean_ctor_get(v_b_3562_, 0);
lean_dec(v_unused_3583_);
v___x_3566_ = v_b_3562_;
v_isShared_3567_ = v_isSharedCheck_3582_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_snd_3564_);
lean_dec(v_b_3562_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3582_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v_a_3568_; lean_object* v___x_3569_; 
v_a_3568_ = lean_array_uget_borrowed(v_as_3559_, v_i_3561_);
lean_inc(v_snd_3564_);
v___x_3569_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3557_, v_x_3558_, v_a_3568_, v_snd_3564_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v___x_3570_; lean_object* v___x_3572_; 
v___x_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3569_);
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 0, v___x_3570_);
v___x_3572_ = v___x_3566_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3570_);
lean_ctor_set(v_reuseFailAlloc_3573_, 1, v_snd_3564_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
else
{
lean_object* v_a_3574_; lean_object* v___x_3575_; lean_object* v___x_3577_; 
lean_dec(v_snd_3564_);
v_a_3574_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_a_3574_);
lean_dec_ref_known(v___x_3569_, 1);
v___x_3575_ = lean_box(0);
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 1, v_a_3574_);
lean_ctor_set(v___x_3566_, 0, v___x_3575_);
v___x_3577_ = v___x_3566_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v___x_3575_);
lean_ctor_set(v_reuseFailAlloc_3581_, 1, v_a_3574_);
v___x_3577_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
size_t v___x_3578_; size_t v___x_3579_; 
v___x_3578_ = ((size_t)1ULL);
v___x_3579_ = lean_usize_add(v_i_3561_, v___x_3578_);
v_i_3561_ = v___x_3579_;
v_b_3562_ = v___x_3577_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3584_, lean_object* v_x_3585_, lean_object* v_as_3586_, lean_object* v_sz_3587_, lean_object* v_i_3588_, lean_object* v_b_3589_){
_start:
{
size_t v_sz_boxed_3590_; size_t v_i_boxed_3591_; lean_object* v_res_3592_; 
v_sz_boxed_3590_ = lean_unbox_usize(v_sz_3587_);
lean_dec(v_sz_3587_);
v_i_boxed_3591_ = lean_unbox_usize(v_i_3588_);
lean_dec(v_i_3588_);
v_res_3592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3584_, v_x_3585_, v_as_3586_, v_sz_boxed_3590_, v_i_boxed_3591_, v_b_3589_);
lean_dec_ref(v_as_3586_);
lean_dec(v_x_3585_);
lean_dec_ref(v_init_3584_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3593_, lean_object* v_x_3594_, lean_object* v_n_3595_, lean_object* v_b_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3593_, v_x_3594_, v_n_3595_, v_b_3596_);
lean_dec_ref(v_n_3595_);
lean_dec(v_x_3594_);
lean_dec_ref(v_init_3593_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object* v_x_3598_, lean_object* v_t_3599_, lean_object* v_init_3600_){
_start:
{
lean_object* v_root_3601_; lean_object* v_tail_3602_; lean_object* v___x_3603_; 
v_root_3601_ = lean_ctor_get(v_t_3599_, 0);
v_tail_3602_ = lean_ctor_get(v_t_3599_, 1);
lean_inc_ref(v_init_3600_);
v___x_3603_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3600_, v_x_3598_, v_root_3601_, v_init_3600_);
lean_dec_ref(v_init_3600_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3604_);
lean_dec_ref_known(v___x_3603_, 1);
return v_a_3604_;
}
else
{
lean_object* v_a_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; size_t v_sz_3608_; size_t v___x_3609_; lean_object* v___x_3610_; lean_object* v_fst_3611_; 
v_a_3605_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3605_);
lean_dec_ref_known(v___x_3603_, 1);
v___x_3606_ = lean_box(0);
v___x_3607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3606_);
lean_ctor_set(v___x_3607_, 1, v_a_3605_);
v_sz_3608_ = lean_array_size(v_tail_3602_);
v___x_3609_ = ((size_t)0ULL);
v___x_3610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3598_, v_tail_3602_, v_sz_3608_, v___x_3609_, v___x_3607_);
v_fst_3611_ = lean_ctor_get(v___x_3610_, 0);
if (lean_obj_tag(v_fst_3611_) == 0)
{
lean_object* v_snd_3612_; 
v_snd_3612_ = lean_ctor_get(v___x_3610_, 1);
lean_inc(v_snd_3612_);
lean_dec_ref(v___x_3610_);
return v_snd_3612_;
}
else
{
lean_object* v_val_3613_; 
lean_inc_ref(v_fst_3611_);
lean_dec_ref(v___x_3610_);
v_val_3613_ = lean_ctor_get(v_fst_3611_, 0);
lean_inc(v_val_3613_);
lean_dec_ref_known(v_fst_3611_, 1);
return v_val_3613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object* v_x_3614_, lean_object* v_t_3615_, lean_object* v_init_3616_){
_start:
{
lean_object* v_res_3617_; 
v_res_3617_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3614_, v_t_3615_, v_init_3616_);
lean_dec_ref(v_t_3615_);
lean_dec(v_x_3614_);
return v_res_3617_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3618_ = lean_unsigned_to_nat(32u);
v___x_3619_ = lean_mk_empty_array_with_capacity(v___x_3618_);
v___x_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
return v___x_3620_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1(void){
_start:
{
size_t v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v_cs_x27_3626_; 
v___x_3621_ = ((size_t)5ULL);
v___x_3622_ = lean_unsigned_to_nat(0u);
v___x_3623_ = lean_unsigned_to_nat(32u);
v___x_3624_ = lean_mk_empty_array_with_capacity(v___x_3623_);
v___x_3625_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0);
v_cs_x27_3626_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_3626_, 0, v___x_3625_);
lean_ctor_set(v_cs_x27_3626_, 1, v___x_3624_);
lean_ctor_set(v_cs_x27_3626_, 2, v___x_3622_);
lean_ctor_set(v_cs_x27_3626_, 3, v___x_3622_);
lean_ctor_set_usize(v_cs_x27_3626_, 4, v___x_3621_);
return v_cs_x27_3626_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_3629_; lean_object* v_cs_x27_3630_; lean_object* v___x_3631_; 
v_todo_3629_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2));
v_cs_x27_3630_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1);
v___x_3631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3631_, 0, v_cs_x27_3630_);
lean_ctor_set(v___x_3631_, 1, v_todo_3629_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object* v_x_3632_, lean_object* v_cs_3633_){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v_fst_3636_; lean_object* v_snd_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
v___x_3634_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3);
v___x_3635_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3632_, v_cs_3633_, v___x_3634_);
v_fst_3636_ = lean_ctor_get(v___x_3635_, 0);
v_snd_3637_ = lean_ctor_get(v___x_3635_, 1);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___x_3635_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_snd_3637_);
lean_inc(v_fst_3636_);
lean_dec(v___x_3635_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_fst_3636_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v_snd_3637_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object* v_x_3645_, lean_object* v_cs_3646_){
_start:
{
lean_object* v_res_3647_; 
v_res_3647_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3645_, v_cs_3646_);
lean_dec_ref(v_cs_3646_);
lean_dec(v_x_3645_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object* v_x_3648_, lean_object* v_cs_3649_){
_start:
{
lean_object* v___x_3650_; 
v___x_3650_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3648_, v_cs_3649_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object* v_x_3651_, lean_object* v_cs_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(v_x_3651_, v_cs_3652_);
lean_dec_ref(v_cs_3652_);
lean_dec(v_x_3651_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(lean_object* v_a_3654_, lean_object* v_y_3655_, lean_object* v_fst_3656_, lean_object* v_s_3657_){
_start:
{
lean_object* v_structs_3658_; lean_object* v_typeIdOf_3659_; lean_object* v_exprToStructId_3660_; lean_object* v_exprToStructIdEntries_3661_; lean_object* v_forbiddenNatModules_3662_; lean_object* v_natStructs_3663_; lean_object* v_natTypeIdOf_3664_; lean_object* v_exprToNatStructId_3665_; lean_object* v___x_3666_; uint8_t v___x_3667_; 
v_structs_3658_ = lean_ctor_get(v_s_3657_, 0);
v_typeIdOf_3659_ = lean_ctor_get(v_s_3657_, 1);
v_exprToStructId_3660_ = lean_ctor_get(v_s_3657_, 2);
v_exprToStructIdEntries_3661_ = lean_ctor_get(v_s_3657_, 3);
v_forbiddenNatModules_3662_ = lean_ctor_get(v_s_3657_, 4);
v_natStructs_3663_ = lean_ctor_get(v_s_3657_, 5);
v_natTypeIdOf_3664_ = lean_ctor_get(v_s_3657_, 6);
v_exprToNatStructId_3665_ = lean_ctor_get(v_s_3657_, 7);
v___x_3666_ = lean_array_get_size(v_structs_3658_);
v___x_3667_ = lean_nat_dec_lt(v_a_3654_, v___x_3666_);
if (v___x_3667_ == 0)
{
lean_dec_ref(v_fst_3656_);
return v_s_3657_;
}
else
{
lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3729_; 
lean_inc_ref(v_exprToNatStructId_3665_);
lean_inc_ref(v_natTypeIdOf_3664_);
lean_inc_ref(v_natStructs_3663_);
lean_inc_ref(v_forbiddenNatModules_3662_);
lean_inc_ref(v_exprToStructIdEntries_3661_);
lean_inc_ref(v_exprToStructId_3660_);
lean_inc_ref(v_typeIdOf_3659_);
lean_inc_ref(v_structs_3658_);
v_isSharedCheck_3729_ = !lean_is_exclusive(v_s_3657_);
if (v_isSharedCheck_3729_ == 0)
{
lean_object* v_unused_3730_; lean_object* v_unused_3731_; lean_object* v_unused_3732_; lean_object* v_unused_3733_; lean_object* v_unused_3734_; lean_object* v_unused_3735_; lean_object* v_unused_3736_; lean_object* v_unused_3737_; 
v_unused_3730_ = lean_ctor_get(v_s_3657_, 7);
lean_dec(v_unused_3730_);
v_unused_3731_ = lean_ctor_get(v_s_3657_, 6);
lean_dec(v_unused_3731_);
v_unused_3732_ = lean_ctor_get(v_s_3657_, 5);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_s_3657_, 4);
lean_dec(v_unused_3733_);
v_unused_3734_ = lean_ctor_get(v_s_3657_, 3);
lean_dec(v_unused_3734_);
v_unused_3735_ = lean_ctor_get(v_s_3657_, 2);
lean_dec(v_unused_3735_);
v_unused_3736_ = lean_ctor_get(v_s_3657_, 1);
lean_dec(v_unused_3736_);
v_unused_3737_ = lean_ctor_get(v_s_3657_, 0);
lean_dec(v_unused_3737_);
v___x_3669_ = v_s_3657_;
v_isShared_3670_ = v_isSharedCheck_3729_;
goto v_resetjp_3668_;
}
else
{
lean_dec(v_s_3657_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3729_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v_v_3671_; lean_object* v_id_3672_; lean_object* v_ringId_x3f_3673_; lean_object* v_type_3674_; lean_object* v_u_3675_; lean_object* v_intModuleInst_3676_; lean_object* v_leInst_x3f_3677_; lean_object* v_ltInst_x3f_3678_; lean_object* v_lawfulOrderLTInst_x3f_3679_; lean_object* v_isPreorderInst_x3f_3680_; lean_object* v_orderedAddInst_x3f_3681_; lean_object* v_isLinearInst_x3f_3682_; lean_object* v_noNatDivInst_x3f_3683_; lean_object* v_ringInst_x3f_3684_; lean_object* v_commRingInst_x3f_3685_; lean_object* v_orderedRingInst_x3f_3686_; lean_object* v_fieldInst_x3f_3687_; lean_object* v_charInst_x3f_3688_; lean_object* v_zero_3689_; lean_object* v_ofNatZero_3690_; lean_object* v_one_x3f_3691_; lean_object* v_leFn_x3f_3692_; lean_object* v_ltFn_x3f_3693_; lean_object* v_addFn_3694_; lean_object* v_zsmulFn_3695_; lean_object* v_nsmulFn_3696_; lean_object* v_zsmulFn_x3f_3697_; lean_object* v_nsmulFn_x3f_3698_; lean_object* v_homomulFn_x3f_3699_; lean_object* v_subFn_3700_; lean_object* v_negFn_3701_; lean_object* v_vars_3702_; lean_object* v_varMap_3703_; lean_object* v_lowers_3704_; lean_object* v_uppers_3705_; lean_object* v_diseqs_3706_; lean_object* v_assignment_3707_; uint8_t v_caseSplits_3708_; lean_object* v_conflict_x3f_3709_; lean_object* v_diseqSplits_3710_; lean_object* v_elimEqs_3711_; lean_object* v_elimStack_3712_; lean_object* v_occurs_3713_; lean_object* v_ignored_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3728_; 
v_v_3671_ = lean_array_fget(v_structs_3658_, v_a_3654_);
v_id_3672_ = lean_ctor_get(v_v_3671_, 0);
v_ringId_x3f_3673_ = lean_ctor_get(v_v_3671_, 1);
v_type_3674_ = lean_ctor_get(v_v_3671_, 2);
v_u_3675_ = lean_ctor_get(v_v_3671_, 3);
v_intModuleInst_3676_ = lean_ctor_get(v_v_3671_, 4);
v_leInst_x3f_3677_ = lean_ctor_get(v_v_3671_, 5);
v_ltInst_x3f_3678_ = lean_ctor_get(v_v_3671_, 6);
v_lawfulOrderLTInst_x3f_3679_ = lean_ctor_get(v_v_3671_, 7);
v_isPreorderInst_x3f_3680_ = lean_ctor_get(v_v_3671_, 8);
v_orderedAddInst_x3f_3681_ = lean_ctor_get(v_v_3671_, 9);
v_isLinearInst_x3f_3682_ = lean_ctor_get(v_v_3671_, 10);
v_noNatDivInst_x3f_3683_ = lean_ctor_get(v_v_3671_, 11);
v_ringInst_x3f_3684_ = lean_ctor_get(v_v_3671_, 12);
v_commRingInst_x3f_3685_ = lean_ctor_get(v_v_3671_, 13);
v_orderedRingInst_x3f_3686_ = lean_ctor_get(v_v_3671_, 14);
v_fieldInst_x3f_3687_ = lean_ctor_get(v_v_3671_, 15);
v_charInst_x3f_3688_ = lean_ctor_get(v_v_3671_, 16);
v_zero_3689_ = lean_ctor_get(v_v_3671_, 17);
v_ofNatZero_3690_ = lean_ctor_get(v_v_3671_, 18);
v_one_x3f_3691_ = lean_ctor_get(v_v_3671_, 19);
v_leFn_x3f_3692_ = lean_ctor_get(v_v_3671_, 20);
v_ltFn_x3f_3693_ = lean_ctor_get(v_v_3671_, 21);
v_addFn_3694_ = lean_ctor_get(v_v_3671_, 22);
v_zsmulFn_3695_ = lean_ctor_get(v_v_3671_, 23);
v_nsmulFn_3696_ = lean_ctor_get(v_v_3671_, 24);
v_zsmulFn_x3f_3697_ = lean_ctor_get(v_v_3671_, 25);
v_nsmulFn_x3f_3698_ = lean_ctor_get(v_v_3671_, 26);
v_homomulFn_x3f_3699_ = lean_ctor_get(v_v_3671_, 27);
v_subFn_3700_ = lean_ctor_get(v_v_3671_, 28);
v_negFn_3701_ = lean_ctor_get(v_v_3671_, 29);
v_vars_3702_ = lean_ctor_get(v_v_3671_, 30);
v_varMap_3703_ = lean_ctor_get(v_v_3671_, 31);
v_lowers_3704_ = lean_ctor_get(v_v_3671_, 32);
v_uppers_3705_ = lean_ctor_get(v_v_3671_, 33);
v_diseqs_3706_ = lean_ctor_get(v_v_3671_, 34);
v_assignment_3707_ = lean_ctor_get(v_v_3671_, 35);
v_caseSplits_3708_ = lean_ctor_get_uint8(v_v_3671_, sizeof(void*)*42);
v_conflict_x3f_3709_ = lean_ctor_get(v_v_3671_, 36);
v_diseqSplits_3710_ = lean_ctor_get(v_v_3671_, 37);
v_elimEqs_3711_ = lean_ctor_get(v_v_3671_, 38);
v_elimStack_3712_ = lean_ctor_get(v_v_3671_, 39);
v_occurs_3713_ = lean_ctor_get(v_v_3671_, 40);
v_ignored_3714_ = lean_ctor_get(v_v_3671_, 41);
v_isSharedCheck_3728_ = !lean_is_exclusive(v_v_3671_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3716_ = v_v_3671_;
v_isShared_3717_ = v_isSharedCheck_3728_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_ignored_3714_);
lean_inc(v_occurs_3713_);
lean_inc(v_elimStack_3712_);
lean_inc(v_elimEqs_3711_);
lean_inc(v_diseqSplits_3710_);
lean_inc(v_conflict_x3f_3709_);
lean_inc(v_assignment_3707_);
lean_inc(v_diseqs_3706_);
lean_inc(v_uppers_3705_);
lean_inc(v_lowers_3704_);
lean_inc(v_varMap_3703_);
lean_inc(v_vars_3702_);
lean_inc(v_negFn_3701_);
lean_inc(v_subFn_3700_);
lean_inc(v_homomulFn_x3f_3699_);
lean_inc(v_nsmulFn_x3f_3698_);
lean_inc(v_zsmulFn_x3f_3697_);
lean_inc(v_nsmulFn_3696_);
lean_inc(v_zsmulFn_3695_);
lean_inc(v_addFn_3694_);
lean_inc(v_ltFn_x3f_3693_);
lean_inc(v_leFn_x3f_3692_);
lean_inc(v_one_x3f_3691_);
lean_inc(v_ofNatZero_3690_);
lean_inc(v_zero_3689_);
lean_inc(v_charInst_x3f_3688_);
lean_inc(v_fieldInst_x3f_3687_);
lean_inc(v_orderedRingInst_x3f_3686_);
lean_inc(v_commRingInst_x3f_3685_);
lean_inc(v_ringInst_x3f_3684_);
lean_inc(v_noNatDivInst_x3f_3683_);
lean_inc(v_isLinearInst_x3f_3682_);
lean_inc(v_orderedAddInst_x3f_3681_);
lean_inc(v_isPreorderInst_x3f_3680_);
lean_inc(v_lawfulOrderLTInst_x3f_3679_);
lean_inc(v_ltInst_x3f_3678_);
lean_inc(v_leInst_x3f_3677_);
lean_inc(v_intModuleInst_3676_);
lean_inc(v_u_3675_);
lean_inc(v_type_3674_);
lean_inc(v_ringId_x3f_3673_);
lean_inc(v_id_3672_);
lean_dec(v_v_3671_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3728_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3718_; lean_object* v_xs_x27_3719_; lean_object* v___x_3720_; lean_object* v___x_3722_; 
v___x_3718_ = lean_box(0);
v_xs_x27_3719_ = lean_array_fset(v_structs_3658_, v_a_3654_, v___x_3718_);
v___x_3720_ = l_Lean_PersistentArray_set___redArg(v_diseqs_3706_, v_y_3655_, v_fst_3656_);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 34, v___x_3720_);
v___x_3722_ = v___x_3716_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_id_3672_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v_ringId_x3f_3673_);
lean_ctor_set(v_reuseFailAlloc_3727_, 2, v_type_3674_);
lean_ctor_set(v_reuseFailAlloc_3727_, 3, v_u_3675_);
lean_ctor_set(v_reuseFailAlloc_3727_, 4, v_intModuleInst_3676_);
lean_ctor_set(v_reuseFailAlloc_3727_, 5, v_leInst_x3f_3677_);
lean_ctor_set(v_reuseFailAlloc_3727_, 6, v_ltInst_x3f_3678_);
lean_ctor_set(v_reuseFailAlloc_3727_, 7, v_lawfulOrderLTInst_x3f_3679_);
lean_ctor_set(v_reuseFailAlloc_3727_, 8, v_isPreorderInst_x3f_3680_);
lean_ctor_set(v_reuseFailAlloc_3727_, 9, v_orderedAddInst_x3f_3681_);
lean_ctor_set(v_reuseFailAlloc_3727_, 10, v_isLinearInst_x3f_3682_);
lean_ctor_set(v_reuseFailAlloc_3727_, 11, v_noNatDivInst_x3f_3683_);
lean_ctor_set(v_reuseFailAlloc_3727_, 12, v_ringInst_x3f_3684_);
lean_ctor_set(v_reuseFailAlloc_3727_, 13, v_commRingInst_x3f_3685_);
lean_ctor_set(v_reuseFailAlloc_3727_, 14, v_orderedRingInst_x3f_3686_);
lean_ctor_set(v_reuseFailAlloc_3727_, 15, v_fieldInst_x3f_3687_);
lean_ctor_set(v_reuseFailAlloc_3727_, 16, v_charInst_x3f_3688_);
lean_ctor_set(v_reuseFailAlloc_3727_, 17, v_zero_3689_);
lean_ctor_set(v_reuseFailAlloc_3727_, 18, v_ofNatZero_3690_);
lean_ctor_set(v_reuseFailAlloc_3727_, 19, v_one_x3f_3691_);
lean_ctor_set(v_reuseFailAlloc_3727_, 20, v_leFn_x3f_3692_);
lean_ctor_set(v_reuseFailAlloc_3727_, 21, v_ltFn_x3f_3693_);
lean_ctor_set(v_reuseFailAlloc_3727_, 22, v_addFn_3694_);
lean_ctor_set(v_reuseFailAlloc_3727_, 23, v_zsmulFn_3695_);
lean_ctor_set(v_reuseFailAlloc_3727_, 24, v_nsmulFn_3696_);
lean_ctor_set(v_reuseFailAlloc_3727_, 25, v_zsmulFn_x3f_3697_);
lean_ctor_set(v_reuseFailAlloc_3727_, 26, v_nsmulFn_x3f_3698_);
lean_ctor_set(v_reuseFailAlloc_3727_, 27, v_homomulFn_x3f_3699_);
lean_ctor_set(v_reuseFailAlloc_3727_, 28, v_subFn_3700_);
lean_ctor_set(v_reuseFailAlloc_3727_, 29, v_negFn_3701_);
lean_ctor_set(v_reuseFailAlloc_3727_, 30, v_vars_3702_);
lean_ctor_set(v_reuseFailAlloc_3727_, 31, v_varMap_3703_);
lean_ctor_set(v_reuseFailAlloc_3727_, 32, v_lowers_3704_);
lean_ctor_set(v_reuseFailAlloc_3727_, 33, v_uppers_3705_);
lean_ctor_set(v_reuseFailAlloc_3727_, 34, v___x_3720_);
lean_ctor_set(v_reuseFailAlloc_3727_, 35, v_assignment_3707_);
lean_ctor_set(v_reuseFailAlloc_3727_, 36, v_conflict_x3f_3709_);
lean_ctor_set(v_reuseFailAlloc_3727_, 37, v_diseqSplits_3710_);
lean_ctor_set(v_reuseFailAlloc_3727_, 38, v_elimEqs_3711_);
lean_ctor_set(v_reuseFailAlloc_3727_, 39, v_elimStack_3712_);
lean_ctor_set(v_reuseFailAlloc_3727_, 40, v_occurs_3713_);
lean_ctor_set(v_reuseFailAlloc_3727_, 41, v_ignored_3714_);
lean_ctor_set_uint8(v_reuseFailAlloc_3727_, sizeof(void*)*42, v_caseSplits_3708_);
v___x_3722_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
lean_object* v___x_3723_; lean_object* v___x_3725_; 
v___x_3723_ = lean_array_fset(v_xs_x27_3719_, v_a_3654_, v___x_3722_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v___x_3723_);
v___x_3725_ = v___x_3669_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3723_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v_typeIdOf_3659_);
lean_ctor_set(v_reuseFailAlloc_3726_, 2, v_exprToStructId_3660_);
lean_ctor_set(v_reuseFailAlloc_3726_, 3, v_exprToStructIdEntries_3661_);
lean_ctor_set(v_reuseFailAlloc_3726_, 4, v_forbiddenNatModules_3662_);
lean_ctor_set(v_reuseFailAlloc_3726_, 5, v_natStructs_3663_);
lean_ctor_set(v_reuseFailAlloc_3726_, 6, v_natTypeIdOf_3664_);
lean_ctor_set(v_reuseFailAlloc_3726_, 7, v_exprToNatStructId_3665_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed(lean_object* v_a_3738_, lean_object* v_y_3739_, lean_object* v_fst_3740_, lean_object* v_s_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(v_a_3738_, v_y_3739_, v_fst_3740_, v_s_3741_);
lean_dec(v_y_3739_);
lean_dec(v_a_3738_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object* v_a_3743_, lean_object* v_x_3744_, lean_object* v_c_3745_, lean_object* v_as_3746_, size_t v_sz_3747_, size_t v_i_3748_, lean_object* v_b_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v_a_3763_; uint8_t v___x_3767_; 
v___x_3767_ = lean_usize_dec_lt(v_i_3748_, v_sz_3747_);
if (v___x_3767_ == 0)
{
lean_object* v___x_3768_; 
lean_dec_ref(v_c_3745_);
v___x_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3768_, 0, v_b_3749_);
return v___x_3768_;
}
else
{
lean_object* v_a_3769_; lean_object* v_fst_3770_; lean_object* v_snd_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
lean_dec_ref(v_b_3749_);
v_a_3769_ = lean_array_uget_borrowed(v_as_3746_, v_i_3748_);
v_fst_3770_ = lean_ctor_get(v_a_3769_, 0);
v_snd_3771_ = lean_ctor_get(v_a_3769_, 1);
v___x_3772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
lean_inc(v_snd_3771_);
lean_inc(v_fst_3770_);
lean_inc_ref(v_c_3745_);
v___x_3773_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_3743_, v_x_3744_, v_c_3745_, v_fst_3770_, v_snd_3771_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v_a_3774_; 
v_a_3774_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_a_3774_);
lean_dec_ref_known(v___x_3773_, 1);
if (lean_obj_tag(v_a_3774_) == 1)
{
lean_object* v_val_3775_; lean_object* v___x_3776_; 
v_val_3775_ = lean_ctor_get(v_a_3774_, 0);
lean_inc(v_val_3775_);
lean_dec_ref_known(v_a_3774_, 1);
v___x_3776_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_val_3775_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v___x_3777_; 
lean_dec_ref_known(v___x_3776_, 1);
v___x_3777_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3787_; 
v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3780_ = v___x_3777_;
v_isShared_3781_ = v_isSharedCheck_3787_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3777_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3787_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
uint8_t v___x_3782_; 
v___x_3782_ = lean_unbox(v_a_3778_);
lean_dec(v_a_3778_);
if (v___x_3782_ == 0)
{
lean_del_object(v___x_3780_);
v_a_3763_ = v___x_3772_;
goto v___jp_3762_;
}
else
{
lean_object* v___x_3783_; lean_object* v___x_3785_; 
lean_dec_ref(v_c_3745_);
v___x_3783_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 0, v___x_3783_);
v___x_3785_ = v___x_3780_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3783_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_dec_ref(v_c_3745_);
v_a_3788_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3777_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3777_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
else
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3803_; 
lean_dec_ref(v_c_3745_);
v_a_3796_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3798_ = v___x_3776_;
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3776_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
if (v_isShared_3799_ == 0)
{
v___x_3801_ = v___x_3798_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3796_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
else
{
lean_object* v___x_3804_; 
lean_dec(v_a_3774_);
v___x_3804_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_snd_3771_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_dec_ref_known(v___x_3804_, 1);
v_a_3763_ = v___x_3772_;
goto v___jp_3762_;
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3812_; 
lean_dec_ref(v_c_3745_);
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3807_ = v___x_3804_;
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3804_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3810_; 
if (v_isShared_3808_ == 0)
{
v___x_3810_ = v___x_3807_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_a_3805_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_dec_ref(v_c_3745_);
v_a_3813_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3773_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3773_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
v___jp_3762_:
{
size_t v___x_3764_; size_t v___x_3765_; 
v___x_3764_ = ((size_t)1ULL);
v___x_3765_ = lean_usize_add(v_i_3748_, v___x_3764_);
lean_inc_ref(v_a_3763_);
v_i_3748_ = v___x_3765_;
v_b_3749_ = v_a_3763_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object** _args){
lean_object* v_a_3821_ = _args[0];
lean_object* v_x_3822_ = _args[1];
lean_object* v_c_3823_ = _args[2];
lean_object* v_as_3824_ = _args[3];
lean_object* v_sz_3825_ = _args[4];
lean_object* v_i_3826_ = _args[5];
lean_object* v_b_3827_ = _args[6];
lean_object* v___y_3828_ = _args[7];
lean_object* v___y_3829_ = _args[8];
lean_object* v___y_3830_ = _args[9];
lean_object* v___y_3831_ = _args[10];
lean_object* v___y_3832_ = _args[11];
lean_object* v___y_3833_ = _args[12];
lean_object* v___y_3834_ = _args[13];
lean_object* v___y_3835_ = _args[14];
lean_object* v___y_3836_ = _args[15];
lean_object* v___y_3837_ = _args[16];
lean_object* v___y_3838_ = _args[17];
lean_object* v___y_3839_ = _args[18];
_start:
{
size_t v_sz_boxed_3840_; size_t v_i_boxed_3841_; lean_object* v_res_3842_; 
v_sz_boxed_3840_ = lean_unbox_usize(v_sz_3825_);
lean_dec(v_sz_3825_);
v_i_boxed_3841_ = lean_unbox_usize(v_i_3826_);
lean_dec(v_i_3826_);
v_res_3842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3821_, v_x_3822_, v_c_3823_, v_as_3824_, v_sz_boxed_3840_, v_i_boxed_3841_, v_b_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
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
lean_dec_ref(v_as_3824_);
lean_dec(v_x_3822_);
lean_dec(v_a_3821_);
return v_res_3842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object* v_a_3843_, lean_object* v_x_3844_, lean_object* v_c_3845_, lean_object* v_y_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_){
_start:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3859_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_3860_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3919_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3863_ = v___x_3860_;
v_isShared_3864_ = v_isSharedCheck_3919_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3860_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3919_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
uint8_t v___x_3865_; 
v___x_3865_ = lean_unbox(v_a_3861_);
lean_dec(v_a_3861_);
if (v___x_3865_ == 0)
{
lean_object* v___x_3866_; 
lean_del_object(v___x_3863_);
v___x_3866_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; lean_object* v___y_3869_; lean_object* v_diseqs_3902_; lean_object* v_size_3903_; uint8_t v___x_3904_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref_known(v___x_3866_, 1);
v_diseqs_3902_ = lean_ctor_get(v_a_3867_, 34);
lean_inc_ref(v_diseqs_3902_);
lean_dec(v_a_3867_);
v_size_3903_ = lean_ctor_get(v_diseqs_3902_, 2);
v___x_3904_ = lean_nat_dec_lt(v_y_3846_, v_size_3903_);
if (v___x_3904_ == 0)
{
lean_object* v___x_3905_; 
lean_dec_ref(v_diseqs_3902_);
v___x_3905_ = l_outOfBounds___redArg(v___x_3859_);
v___y_3869_ = v___x_3905_;
goto v___jp_3868_;
}
else
{
lean_object* v___x_3906_; 
v___x_3906_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3859_, v_diseqs_3902_, v_y_3846_);
lean_dec_ref(v_diseqs_3902_);
v___y_3869_ = v___x_3906_;
goto v___jp_3868_;
}
v___jp_3868_:
{
lean_object* v___x_3870_; lean_object* v_fst_3871_; lean_object* v_snd_3872_; lean_object* v___f_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3870_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3844_, v___y_3869_);
lean_dec_ref(v___y_3869_);
v_fst_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_fst_3871_);
v_snd_3872_ = lean_ctor_get(v___x_3870_, 1);
lean_inc(v_snd_3872_);
lean_dec_ref(v___x_3870_);
lean_inc(v_a_3847_);
v___f_3873_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3873_, 0, v_a_3847_);
lean_closure_set(v___f_3873_, 1, v_y_3846_);
lean_closure_set(v___f_3873_, 2, v_fst_3871_);
v___x_3874_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3875_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3874_, v___f_3873_, v_a_3848_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v___x_3876_; lean_object* v___x_3877_; size_t v_sz_3878_; size_t v___x_3879_; lean_object* v___x_3880_; 
lean_dec_ref_known(v___x_3875_, 1);
v___x_3876_ = lean_box(0);
v___x_3877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_3878_ = lean_array_size(v_snd_3872_);
v___x_3879_ = ((size_t)0ULL);
v___x_3880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3843_, v_x_3844_, v_c_3845_, v_snd_3872_, v_sz_3878_, v___x_3879_, v___x_3877_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_);
lean_dec(v_snd_3872_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3893_; 
v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3883_ = v___x_3880_;
v_isShared_3884_ = v_isSharedCheck_3893_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3880_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3893_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v_fst_3885_; 
v_fst_3885_ = lean_ctor_get(v_a_3881_, 0);
lean_inc(v_fst_3885_);
lean_dec(v_a_3881_);
if (lean_obj_tag(v_fst_3885_) == 0)
{
lean_object* v___x_3887_; 
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 0, v___x_3876_);
v___x_3887_ = v___x_3883_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3876_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
else
{
lean_object* v_val_3889_; lean_object* v___x_3891_; 
v_val_3889_ = lean_ctor_get(v_fst_3885_, 0);
lean_inc(v_val_3889_);
lean_dec_ref_known(v_fst_3885_, 1);
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 0, v_val_3889_);
v___x_3891_ = v___x_3883_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_val_3889_);
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
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3901_; 
v_a_3894_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3896_ = v___x_3880_;
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3880_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3899_; 
if (v_isShared_3897_ == 0)
{
v___x_3899_ = v___x_3896_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_a_3894_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
return v___x_3899_;
}
}
}
}
else
{
lean_dec(v_snd_3872_);
lean_dec_ref(v_c_3845_);
return v___x_3875_;
}
}
}
else
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3914_; 
lean_dec(v_y_3846_);
lean_dec_ref(v_c_3845_);
v_a_3907_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3909_ = v___x_3866_;
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3866_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3912_; 
if (v_isShared_3910_ == 0)
{
v___x_3912_ = v___x_3909_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
else
{
lean_object* v___x_3915_; lean_object* v___x_3917_; 
lean_dec(v_y_3846_);
lean_dec_ref(v_c_3845_);
v___x_3915_ = lean_box(0);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3915_);
v___x_3917_ = v___x_3863_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3915_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
else
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
lean_dec(v_y_3846_);
lean_dec_ref(v_c_3845_);
v_a_3920_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3860_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3860_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object* v_a_3928_, lean_object* v_x_3929_, lean_object* v_c_3930_, lean_object* v_y_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_){
_start:
{
lean_object* v_res_3944_; 
v_res_3944_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v_a_3928_, v_x_3929_, v_c_3930_, v_y_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_);
lean_dec(v_a_3942_);
lean_dec_ref(v_a_3941_);
lean_dec(v_a_3940_);
lean_dec_ref(v_a_3939_);
lean_dec(v_a_3938_);
lean_dec_ref(v_a_3937_);
lean_dec(v_a_3936_);
lean_dec_ref(v_a_3935_);
lean_dec(v_a_3934_);
lean_dec(v_a_3933_);
lean_dec(v_a_3932_);
lean_dec(v_x_3929_);
lean_dec(v_a_3928_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object* v_a_3945_, lean_object* v_x_3946_, lean_object* v_c_3947_, lean_object* v_y_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_){
_start:
{
lean_object* v___x_3961_; 
lean_inc(v_y_3948_);
lean_inc_ref(v_c_3947_);
lean_inc(v_x_3946_);
lean_inc(v_a_3945_);
v___x_3961_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_3945_, v_x_3946_, v_c_3947_, v_y_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v___x_3962_; 
lean_dec_ref_known(v___x_3961_, 1);
lean_inc(v_y_3948_);
lean_inc_ref(v_c_3947_);
lean_inc(v_x_3946_);
lean_inc(v_a_3945_);
v___x_3962_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_3945_, v_x_3946_, v_c_3947_, v_y_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
lean_dec_ref_known(v___x_3962_, 1);
v___x_3963_ = lean_nat_to_int(v_a_3945_);
v___x_3964_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v___x_3963_, v_x_3946_, v_c_3947_, v_y_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
lean_dec(v_x_3946_);
lean_dec(v___x_3963_);
return v___x_3964_;
}
else
{
lean_dec(v_y_3948_);
lean_dec_ref(v_c_3947_);
lean_dec(v_x_3946_);
lean_dec(v_a_3945_);
return v___x_3962_;
}
}
else
{
lean_dec(v_y_3948_);
lean_dec_ref(v_c_3947_);
lean_dec(v_x_3946_);
lean_dec(v_a_3945_);
return v___x_3961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object* v_a_3965_, lean_object* v_x_3966_, lean_object* v_c_3967_, lean_object* v_y_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_3965_, v_x_3966_, v_c_3967_, v_y_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
lean_dec(v_a_3979_);
lean_dec_ref(v_a_3978_);
lean_dec(v_a_3977_);
lean_dec_ref(v_a_3976_);
lean_dec(v_a_3975_);
lean_dec_ref(v_a_3974_);
lean_dec(v_a_3973_);
lean_dec_ref(v_a_3972_);
lean_dec(v_a_3971_);
lean_dec(v_a_3970_);
lean_dec(v_a_3969_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(lean_object* v_a_3982_, lean_object* v_x_3983_, lean_object* v_s_3984_){
_start:
{
lean_object* v_structs_3985_; lean_object* v_typeIdOf_3986_; lean_object* v_exprToStructId_3987_; lean_object* v_exprToStructIdEntries_3988_; lean_object* v_forbiddenNatModules_3989_; lean_object* v_natStructs_3990_; lean_object* v_natTypeIdOf_3991_; lean_object* v_exprToNatStructId_3992_; lean_object* v___x_3993_; uint8_t v___x_3994_; 
v_structs_3985_ = lean_ctor_get(v_s_3984_, 0);
v_typeIdOf_3986_ = lean_ctor_get(v_s_3984_, 1);
v_exprToStructId_3987_ = lean_ctor_get(v_s_3984_, 2);
v_exprToStructIdEntries_3988_ = lean_ctor_get(v_s_3984_, 3);
v_forbiddenNatModules_3989_ = lean_ctor_get(v_s_3984_, 4);
v_natStructs_3990_ = lean_ctor_get(v_s_3984_, 5);
v_natTypeIdOf_3991_ = lean_ctor_get(v_s_3984_, 6);
v_exprToNatStructId_3992_ = lean_ctor_get(v_s_3984_, 7);
v___x_3993_ = lean_array_get_size(v_structs_3985_);
v___x_3994_ = lean_nat_dec_lt(v_a_3982_, v___x_3993_);
if (v___x_3994_ == 0)
{
return v_s_3984_;
}
else
{
lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4057_; 
lean_inc_ref(v_exprToNatStructId_3992_);
lean_inc_ref(v_natTypeIdOf_3991_);
lean_inc_ref(v_natStructs_3990_);
lean_inc_ref(v_forbiddenNatModules_3989_);
lean_inc_ref(v_exprToStructIdEntries_3988_);
lean_inc_ref(v_exprToStructId_3987_);
lean_inc_ref(v_typeIdOf_3986_);
lean_inc_ref(v_structs_3985_);
v_isSharedCheck_4057_ = !lean_is_exclusive(v_s_3984_);
if (v_isSharedCheck_4057_ == 0)
{
lean_object* v_unused_4058_; lean_object* v_unused_4059_; lean_object* v_unused_4060_; lean_object* v_unused_4061_; lean_object* v_unused_4062_; lean_object* v_unused_4063_; lean_object* v_unused_4064_; lean_object* v_unused_4065_; 
v_unused_4058_ = lean_ctor_get(v_s_3984_, 7);
lean_dec(v_unused_4058_);
v_unused_4059_ = lean_ctor_get(v_s_3984_, 6);
lean_dec(v_unused_4059_);
v_unused_4060_ = lean_ctor_get(v_s_3984_, 5);
lean_dec(v_unused_4060_);
v_unused_4061_ = lean_ctor_get(v_s_3984_, 4);
lean_dec(v_unused_4061_);
v_unused_4062_ = lean_ctor_get(v_s_3984_, 3);
lean_dec(v_unused_4062_);
v_unused_4063_ = lean_ctor_get(v_s_3984_, 2);
lean_dec(v_unused_4063_);
v_unused_4064_ = lean_ctor_get(v_s_3984_, 1);
lean_dec(v_unused_4064_);
v_unused_4065_ = lean_ctor_get(v_s_3984_, 0);
lean_dec(v_unused_4065_);
v___x_3996_ = v_s_3984_;
v_isShared_3997_ = v_isSharedCheck_4057_;
goto v_resetjp_3995_;
}
else
{
lean_dec(v_s_3984_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4057_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v_v_3998_; lean_object* v_id_3999_; lean_object* v_ringId_x3f_4000_; lean_object* v_type_4001_; lean_object* v_u_4002_; lean_object* v_intModuleInst_4003_; lean_object* v_leInst_x3f_4004_; lean_object* v_ltInst_x3f_4005_; lean_object* v_lawfulOrderLTInst_x3f_4006_; lean_object* v_isPreorderInst_x3f_4007_; lean_object* v_orderedAddInst_x3f_4008_; lean_object* v_isLinearInst_x3f_4009_; lean_object* v_noNatDivInst_x3f_4010_; lean_object* v_ringInst_x3f_4011_; lean_object* v_commRingInst_x3f_4012_; lean_object* v_orderedRingInst_x3f_4013_; lean_object* v_fieldInst_x3f_4014_; lean_object* v_charInst_x3f_4015_; lean_object* v_zero_4016_; lean_object* v_ofNatZero_4017_; lean_object* v_one_x3f_4018_; lean_object* v_leFn_x3f_4019_; lean_object* v_ltFn_x3f_4020_; lean_object* v_addFn_4021_; lean_object* v_zsmulFn_4022_; lean_object* v_nsmulFn_4023_; lean_object* v_zsmulFn_x3f_4024_; lean_object* v_nsmulFn_x3f_4025_; lean_object* v_homomulFn_x3f_4026_; lean_object* v_subFn_4027_; lean_object* v_negFn_4028_; lean_object* v_vars_4029_; lean_object* v_varMap_4030_; lean_object* v_lowers_4031_; lean_object* v_uppers_4032_; lean_object* v_diseqs_4033_; lean_object* v_assignment_4034_; uint8_t v_caseSplits_4035_; lean_object* v_conflict_x3f_4036_; lean_object* v_diseqSplits_4037_; lean_object* v_elimEqs_4038_; lean_object* v_elimStack_4039_; lean_object* v_occurs_4040_; lean_object* v_ignored_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4056_; 
v_v_3998_ = lean_array_fget(v_structs_3985_, v_a_3982_);
v_id_3999_ = lean_ctor_get(v_v_3998_, 0);
v_ringId_x3f_4000_ = lean_ctor_get(v_v_3998_, 1);
v_type_4001_ = lean_ctor_get(v_v_3998_, 2);
v_u_4002_ = lean_ctor_get(v_v_3998_, 3);
v_intModuleInst_4003_ = lean_ctor_get(v_v_3998_, 4);
v_leInst_x3f_4004_ = lean_ctor_get(v_v_3998_, 5);
v_ltInst_x3f_4005_ = lean_ctor_get(v_v_3998_, 6);
v_lawfulOrderLTInst_x3f_4006_ = lean_ctor_get(v_v_3998_, 7);
v_isPreorderInst_x3f_4007_ = lean_ctor_get(v_v_3998_, 8);
v_orderedAddInst_x3f_4008_ = lean_ctor_get(v_v_3998_, 9);
v_isLinearInst_x3f_4009_ = lean_ctor_get(v_v_3998_, 10);
v_noNatDivInst_x3f_4010_ = lean_ctor_get(v_v_3998_, 11);
v_ringInst_x3f_4011_ = lean_ctor_get(v_v_3998_, 12);
v_commRingInst_x3f_4012_ = lean_ctor_get(v_v_3998_, 13);
v_orderedRingInst_x3f_4013_ = lean_ctor_get(v_v_3998_, 14);
v_fieldInst_x3f_4014_ = lean_ctor_get(v_v_3998_, 15);
v_charInst_x3f_4015_ = lean_ctor_get(v_v_3998_, 16);
v_zero_4016_ = lean_ctor_get(v_v_3998_, 17);
v_ofNatZero_4017_ = lean_ctor_get(v_v_3998_, 18);
v_one_x3f_4018_ = lean_ctor_get(v_v_3998_, 19);
v_leFn_x3f_4019_ = lean_ctor_get(v_v_3998_, 20);
v_ltFn_x3f_4020_ = lean_ctor_get(v_v_3998_, 21);
v_addFn_4021_ = lean_ctor_get(v_v_3998_, 22);
v_zsmulFn_4022_ = lean_ctor_get(v_v_3998_, 23);
v_nsmulFn_4023_ = lean_ctor_get(v_v_3998_, 24);
v_zsmulFn_x3f_4024_ = lean_ctor_get(v_v_3998_, 25);
v_nsmulFn_x3f_4025_ = lean_ctor_get(v_v_3998_, 26);
v_homomulFn_x3f_4026_ = lean_ctor_get(v_v_3998_, 27);
v_subFn_4027_ = lean_ctor_get(v_v_3998_, 28);
v_negFn_4028_ = lean_ctor_get(v_v_3998_, 29);
v_vars_4029_ = lean_ctor_get(v_v_3998_, 30);
v_varMap_4030_ = lean_ctor_get(v_v_3998_, 31);
v_lowers_4031_ = lean_ctor_get(v_v_3998_, 32);
v_uppers_4032_ = lean_ctor_get(v_v_3998_, 33);
v_diseqs_4033_ = lean_ctor_get(v_v_3998_, 34);
v_assignment_4034_ = lean_ctor_get(v_v_3998_, 35);
v_caseSplits_4035_ = lean_ctor_get_uint8(v_v_3998_, sizeof(void*)*42);
v_conflict_x3f_4036_ = lean_ctor_get(v_v_3998_, 36);
v_diseqSplits_4037_ = lean_ctor_get(v_v_3998_, 37);
v_elimEqs_4038_ = lean_ctor_get(v_v_3998_, 38);
v_elimStack_4039_ = lean_ctor_get(v_v_3998_, 39);
v_occurs_4040_ = lean_ctor_get(v_v_3998_, 40);
v_ignored_4041_ = lean_ctor_get(v_v_3998_, 41);
v_isSharedCheck_4056_ = !lean_is_exclusive(v_v_3998_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4043_ = v_v_3998_;
v_isShared_4044_ = v_isSharedCheck_4056_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_ignored_4041_);
lean_inc(v_occurs_4040_);
lean_inc(v_elimStack_4039_);
lean_inc(v_elimEqs_4038_);
lean_inc(v_diseqSplits_4037_);
lean_inc(v_conflict_x3f_4036_);
lean_inc(v_assignment_4034_);
lean_inc(v_diseqs_4033_);
lean_inc(v_uppers_4032_);
lean_inc(v_lowers_4031_);
lean_inc(v_varMap_4030_);
lean_inc(v_vars_4029_);
lean_inc(v_negFn_4028_);
lean_inc(v_subFn_4027_);
lean_inc(v_homomulFn_x3f_4026_);
lean_inc(v_nsmulFn_x3f_4025_);
lean_inc(v_zsmulFn_x3f_4024_);
lean_inc(v_nsmulFn_4023_);
lean_inc(v_zsmulFn_4022_);
lean_inc(v_addFn_4021_);
lean_inc(v_ltFn_x3f_4020_);
lean_inc(v_leFn_x3f_4019_);
lean_inc(v_one_x3f_4018_);
lean_inc(v_ofNatZero_4017_);
lean_inc(v_zero_4016_);
lean_inc(v_charInst_x3f_4015_);
lean_inc(v_fieldInst_x3f_4014_);
lean_inc(v_orderedRingInst_x3f_4013_);
lean_inc(v_commRingInst_x3f_4012_);
lean_inc(v_ringInst_x3f_4011_);
lean_inc(v_noNatDivInst_x3f_4010_);
lean_inc(v_isLinearInst_x3f_4009_);
lean_inc(v_orderedAddInst_x3f_4008_);
lean_inc(v_isPreorderInst_x3f_4007_);
lean_inc(v_lawfulOrderLTInst_x3f_4006_);
lean_inc(v_ltInst_x3f_4005_);
lean_inc(v_leInst_x3f_4004_);
lean_inc(v_intModuleInst_4003_);
lean_inc(v_u_4002_);
lean_inc(v_type_4001_);
lean_inc(v_ringId_x3f_4000_);
lean_inc(v_id_3999_);
lean_dec(v_v_3998_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4056_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4045_; lean_object* v_xs_x27_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4050_; 
v___x_4045_ = lean_box(0);
v_xs_x27_4046_ = lean_array_fset(v_structs_3985_, v_a_3982_, v___x_4045_);
v___x_4047_ = lean_box(1);
v___x_4048_ = l_Lean_PersistentArray_set___redArg(v_occurs_4040_, v_x_3983_, v___x_4047_);
if (v_isShared_4044_ == 0)
{
lean_ctor_set(v___x_4043_, 40, v___x_4048_);
v___x_4050_ = v___x_4043_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_id_3999_);
lean_ctor_set(v_reuseFailAlloc_4055_, 1, v_ringId_x3f_4000_);
lean_ctor_set(v_reuseFailAlloc_4055_, 2, v_type_4001_);
lean_ctor_set(v_reuseFailAlloc_4055_, 3, v_u_4002_);
lean_ctor_set(v_reuseFailAlloc_4055_, 4, v_intModuleInst_4003_);
lean_ctor_set(v_reuseFailAlloc_4055_, 5, v_leInst_x3f_4004_);
lean_ctor_set(v_reuseFailAlloc_4055_, 6, v_ltInst_x3f_4005_);
lean_ctor_set(v_reuseFailAlloc_4055_, 7, v_lawfulOrderLTInst_x3f_4006_);
lean_ctor_set(v_reuseFailAlloc_4055_, 8, v_isPreorderInst_x3f_4007_);
lean_ctor_set(v_reuseFailAlloc_4055_, 9, v_orderedAddInst_x3f_4008_);
lean_ctor_set(v_reuseFailAlloc_4055_, 10, v_isLinearInst_x3f_4009_);
lean_ctor_set(v_reuseFailAlloc_4055_, 11, v_noNatDivInst_x3f_4010_);
lean_ctor_set(v_reuseFailAlloc_4055_, 12, v_ringInst_x3f_4011_);
lean_ctor_set(v_reuseFailAlloc_4055_, 13, v_commRingInst_x3f_4012_);
lean_ctor_set(v_reuseFailAlloc_4055_, 14, v_orderedRingInst_x3f_4013_);
lean_ctor_set(v_reuseFailAlloc_4055_, 15, v_fieldInst_x3f_4014_);
lean_ctor_set(v_reuseFailAlloc_4055_, 16, v_charInst_x3f_4015_);
lean_ctor_set(v_reuseFailAlloc_4055_, 17, v_zero_4016_);
lean_ctor_set(v_reuseFailAlloc_4055_, 18, v_ofNatZero_4017_);
lean_ctor_set(v_reuseFailAlloc_4055_, 19, v_one_x3f_4018_);
lean_ctor_set(v_reuseFailAlloc_4055_, 20, v_leFn_x3f_4019_);
lean_ctor_set(v_reuseFailAlloc_4055_, 21, v_ltFn_x3f_4020_);
lean_ctor_set(v_reuseFailAlloc_4055_, 22, v_addFn_4021_);
lean_ctor_set(v_reuseFailAlloc_4055_, 23, v_zsmulFn_4022_);
lean_ctor_set(v_reuseFailAlloc_4055_, 24, v_nsmulFn_4023_);
lean_ctor_set(v_reuseFailAlloc_4055_, 25, v_zsmulFn_x3f_4024_);
lean_ctor_set(v_reuseFailAlloc_4055_, 26, v_nsmulFn_x3f_4025_);
lean_ctor_set(v_reuseFailAlloc_4055_, 27, v_homomulFn_x3f_4026_);
lean_ctor_set(v_reuseFailAlloc_4055_, 28, v_subFn_4027_);
lean_ctor_set(v_reuseFailAlloc_4055_, 29, v_negFn_4028_);
lean_ctor_set(v_reuseFailAlloc_4055_, 30, v_vars_4029_);
lean_ctor_set(v_reuseFailAlloc_4055_, 31, v_varMap_4030_);
lean_ctor_set(v_reuseFailAlloc_4055_, 32, v_lowers_4031_);
lean_ctor_set(v_reuseFailAlloc_4055_, 33, v_uppers_4032_);
lean_ctor_set(v_reuseFailAlloc_4055_, 34, v_diseqs_4033_);
lean_ctor_set(v_reuseFailAlloc_4055_, 35, v_assignment_4034_);
lean_ctor_set(v_reuseFailAlloc_4055_, 36, v_conflict_x3f_4036_);
lean_ctor_set(v_reuseFailAlloc_4055_, 37, v_diseqSplits_4037_);
lean_ctor_set(v_reuseFailAlloc_4055_, 38, v_elimEqs_4038_);
lean_ctor_set(v_reuseFailAlloc_4055_, 39, v_elimStack_4039_);
lean_ctor_set(v_reuseFailAlloc_4055_, 40, v___x_4048_);
lean_ctor_set(v_reuseFailAlloc_4055_, 41, v_ignored_4041_);
lean_ctor_set_uint8(v_reuseFailAlloc_4055_, sizeof(void*)*42, v_caseSplits_4035_);
v___x_4050_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
lean_object* v___x_4051_; lean_object* v___x_4053_; 
v___x_4051_ = lean_array_fset(v_xs_x27_4046_, v_a_3982_, v___x_4050_);
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 0, v___x_4051_);
v___x_4053_ = v___x_3996_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v___x_4051_);
lean_ctor_set(v_reuseFailAlloc_4054_, 1, v_typeIdOf_3986_);
lean_ctor_set(v_reuseFailAlloc_4054_, 2, v_exprToStructId_3987_);
lean_ctor_set(v_reuseFailAlloc_4054_, 3, v_exprToStructIdEntries_3988_);
lean_ctor_set(v_reuseFailAlloc_4054_, 4, v_forbiddenNatModules_3989_);
lean_ctor_set(v_reuseFailAlloc_4054_, 5, v_natStructs_3990_);
lean_ctor_set(v_reuseFailAlloc_4054_, 6, v_natTypeIdOf_3991_);
lean_ctor_set(v_reuseFailAlloc_4054_, 7, v_exprToNatStructId_3992_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed(lean_object* v_a_4066_, lean_object* v_x_4067_, lean_object* v_s_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(v_a_4066_, v_x_4067_, v_s_4068_);
lean_dec(v_x_4067_);
lean_dec(v_a_4066_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object* v_a_4070_, lean_object* v_x_4071_, lean_object* v_c_4072_, lean_object* v_init_4073_, lean_object* v_x_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
if (lean_obj_tag(v_x_4074_) == 0)
{
lean_object* v_k_4087_; lean_object* v_l_4088_; lean_object* v_r_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v_k_4087_ = lean_ctor_get(v_x_4074_, 1);
lean_inc(v_k_4087_);
v_l_4088_ = lean_ctor_get(v_x_4074_, 3);
lean_inc(v_l_4088_);
v_r_4089_ = lean_ctor_get(v_x_4074_, 4);
lean_inc(v_r_4089_);
lean_dec_ref_known(v_x_4074_, 5);
v___x_4090_ = lean_box(0);
lean_inc_ref(v_c_4072_);
lean_inc(v_x_4071_);
lean_inc(v_a_4070_);
v___x_4091_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4070_, v_x_4071_, v_c_4072_, v_init_4073_, v_l_4088_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_object* v___x_4092_; 
lean_dec_ref_known(v___x_4091_, 1);
lean_inc_ref(v_c_4072_);
lean_inc(v_x_4071_);
lean_inc(v_a_4070_);
v___x_4092_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4070_, v_x_4071_, v_c_4072_, v_k_4087_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_dec_ref_known(v___x_4092_, 1);
v_init_4073_ = v___x_4090_;
v_x_4074_ = v_r_4089_;
goto _start;
}
else
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4101_; 
lean_dec(v_r_4089_);
lean_dec_ref(v_c_4072_);
lean_dec(v_x_4071_);
lean_dec(v_a_4070_);
v_a_4094_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4096_ = v___x_4092_;
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___x_4092_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4099_; 
if (v_isShared_4097_ == 0)
{
v___x_4099_ = v___x_4096_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_a_4094_);
v___x_4099_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
return v___x_4099_;
}
}
}
}
else
{
lean_dec(v_r_4089_);
lean_dec(v_k_4087_);
lean_dec_ref(v_c_4072_);
lean_dec(v_x_4071_);
lean_dec(v_a_4070_);
return v___x_4091_;
}
}
else
{
lean_object* v___x_4102_; lean_object* v___x_4103_; 
lean_dec_ref(v_c_4072_);
lean_dec(v_x_4071_);
lean_dec(v_a_4070_);
v___x_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4102_, 0, v_init_4073_);
v___x_4103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4102_);
return v___x_4103_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object** _args){
lean_object* v_a_4104_ = _args[0];
lean_object* v_x_4105_ = _args[1];
lean_object* v_c_4106_ = _args[2];
lean_object* v_init_4107_ = _args[3];
lean_object* v_x_4108_ = _args[4];
lean_object* v___y_4109_ = _args[5];
lean_object* v___y_4110_ = _args[6];
lean_object* v___y_4111_ = _args[7];
lean_object* v___y_4112_ = _args[8];
lean_object* v___y_4113_ = _args[9];
lean_object* v___y_4114_ = _args[10];
lean_object* v___y_4115_ = _args[11];
lean_object* v___y_4116_ = _args[12];
lean_object* v___y_4117_ = _args[13];
lean_object* v___y_4118_ = _args[14];
lean_object* v___y_4119_ = _args[15];
lean_object* v___y_4120_ = _args[16];
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4104_, v_x_4105_, v_c_4106_, v_init_4107_, v_x_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
lean_dec(v___y_4113_);
lean_dec_ref(v___y_4112_);
lean_dec(v___y_4111_);
lean_dec(v___y_4110_);
lean_dec(v___y_4109_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object* v_a_4122_, lean_object* v_x_4123_, lean_object* v_c_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_){
_start:
{
lean_object* v___f_4137_; lean_object* v___x_4138_; 
lean_inc(v_x_4123_);
lean_inc(v_a_4125_);
v___f_4137_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4137_, 0, v_a_4125_);
lean_closure_set(v___f_4137_, 1, v_x_4123_);
v___x_4138_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___y_4141_; lean_object* v_occurs_4163_; lean_object* v_size_4164_; lean_object* v___x_4165_; uint8_t v___x_4166_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v___x_4138_, 1);
v_occurs_4163_ = lean_ctor_get(v_a_4139_, 40);
lean_inc_ref(v_occurs_4163_);
lean_dec(v_a_4139_);
v_size_4164_ = lean_ctor_get(v_occurs_4163_, 2);
v___x_4165_ = lean_box(1);
v___x_4166_ = lean_nat_dec_lt(v_x_4123_, v_size_4164_);
if (v___x_4166_ == 0)
{
lean_object* v___x_4167_; 
lean_dec_ref(v_occurs_4163_);
v___x_4167_ = l_outOfBounds___redArg(v___x_4165_);
v___y_4141_ = v___x_4167_;
goto v___jp_4140_;
}
else
{
lean_object* v___x_4168_; 
v___x_4168_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4165_, v_occurs_4163_, v_x_4123_);
lean_dec_ref(v_occurs_4163_);
v___y_4141_ = v___x_4168_;
goto v___jp_4140_;
}
v___jp_4140_:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4142_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4143_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4142_, v___f_4137_, v_a_4126_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v___x_4144_; 
lean_dec_ref_known(v___x_4143_, 1);
lean_inc_ref(v_c_4124_);
lean_inc_n(v_x_4123_, 2);
lean_inc(v_a_4122_);
v___x_4144_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4122_, v_x_4123_, v_c_4124_, v_x_4123_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_object* v___x_4145_; lean_object* v___x_4146_; 
lean_dec_ref_known(v___x_4144_, 1);
v___x_4145_ = lean_box(0);
v___x_4146_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4122_, v_x_4123_, v_c_4124_, v___x_4145_, v___y_4141_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
if (lean_obj_tag(v___x_4146_) == 0)
{
lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4153_; 
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4146_);
if (v_isSharedCheck_4153_ == 0)
{
lean_object* v_unused_4154_; 
v_unused_4154_ = lean_ctor_get(v___x_4146_, 0);
lean_dec(v_unused_4154_);
v___x_4148_ = v___x_4146_;
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
else
{
lean_dec(v___x_4146_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4151_; 
if (v_isShared_4149_ == 0)
{
lean_ctor_set(v___x_4148_, 0, v___x_4145_);
v___x_4151_ = v___x_4148_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v___x_4145_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
v_a_4155_ = lean_ctor_get(v___x_4146_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4146_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___x_4146_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4146_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
else
{
lean_dec(v___y_4141_);
lean_dec_ref(v_c_4124_);
lean_dec(v_x_4123_);
lean_dec(v_a_4122_);
return v___x_4144_;
}
}
else
{
lean_dec(v___y_4141_);
lean_dec_ref(v_c_4124_);
lean_dec(v_x_4123_);
lean_dec(v_a_4122_);
return v___x_4143_;
}
}
}
else
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
lean_dec_ref(v___f_4137_);
lean_dec_ref(v_c_4124_);
lean_dec(v_x_4123_);
lean_dec(v_a_4122_);
v_a_4169_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4171_ = v___x_4138_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4138_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___boxed(lean_object* v_a_4177_, lean_object* v_x_4178_, lean_object* v_c_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_){
_start:
{
lean_object* v_res_4192_; 
v_res_4192_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v_a_4177_, v_x_4178_, v_c_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_);
lean_dec(v_a_4190_);
lean_dec_ref(v_a_4189_);
lean_dec(v_a_4188_);
lean_dec_ref(v_a_4187_);
lean_dec(v_a_4186_);
lean_dec_ref(v_a_4185_);
lean_dec(v_a_4184_);
lean_dec_ref(v_a_4183_);
lean_dec(v_a_4182_);
lean_dec(v_a_4181_);
lean_dec(v_a_4180_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(lean_object* v_c_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_){
_start:
{
lean_object* v_p_4210_; 
v_p_4210_ = lean_ctor_get(v_c_4193_, 0);
if (lean_obj_tag(v_p_4210_) == 1)
{
lean_object* v_k_4211_; lean_object* v_v_4212_; lean_object* v_p_4213_; lean_object* v_y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___x_4264_; lean_object* v___x_4265_; uint8_t v___x_4266_; 
v_k_4211_ = lean_ctor_get(v_p_4210_, 0);
v_v_4212_ = lean_ctor_get(v_p_4210_, 1);
v_p_4213_ = lean_ctor_get(v_p_4210_, 2);
v___x_4264_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_4265_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4266_ = lean_int_dec_eq(v_k_4211_, v___x_4265_);
if (v___x_4266_ == 0)
{
uint8_t v___x_4267_; 
v___x_4267_ = lean_int_dec_eq(v_k_4211_, v___x_4264_);
if (v___x_4267_ == 0)
{
goto v___jp_4206_;
}
else
{
if (lean_obj_tag(v_p_4213_) == 1)
{
lean_object* v_k_4268_; lean_object* v_v_4269_; lean_object* v_p_4270_; uint8_t v___x_4271_; 
v_k_4268_ = lean_ctor_get(v_p_4213_, 0);
v_v_4269_ = lean_ctor_get(v_p_4213_, 1);
v_p_4270_ = lean_ctor_get(v_p_4213_, 2);
v___x_4271_ = lean_int_dec_eq(v_k_4268_, v___x_4265_);
if (v___x_4271_ == 0)
{
goto v___jp_4206_;
}
else
{
if (lean_obj_tag(v_p_4270_) == 0)
{
v_y_4215_ = v_v_4269_;
v___y_4216_ = v_a_4194_;
v___y_4217_ = v_a_4195_;
v___y_4218_ = v_a_4196_;
v___y_4219_ = v_a_4197_;
v___y_4220_ = v_a_4198_;
v___y_4221_ = v_a_4199_;
v___y_4222_ = v_a_4200_;
v___y_4223_ = v_a_4201_;
v___y_4224_ = v_a_4202_;
v___y_4225_ = v_a_4203_;
v___y_4226_ = v_a_4204_;
goto v___jp_4214_;
}
else
{
goto v___jp_4206_;
}
}
}
else
{
goto v___jp_4206_;
}
}
}
else
{
if (lean_obj_tag(v_p_4213_) == 1)
{
lean_object* v_k_4272_; lean_object* v_v_4273_; lean_object* v_p_4274_; uint8_t v___x_4275_; 
v_k_4272_ = lean_ctor_get(v_p_4213_, 0);
v_v_4273_ = lean_ctor_get(v_p_4213_, 1);
v_p_4274_ = lean_ctor_get(v_p_4213_, 2);
v___x_4275_ = lean_int_dec_eq(v_k_4272_, v___x_4264_);
if (v___x_4275_ == 0)
{
goto v___jp_4206_;
}
else
{
if (lean_obj_tag(v_p_4274_) == 0)
{
v_y_4215_ = v_v_4273_;
v___y_4216_ = v_a_4194_;
v___y_4217_ = v_a_4195_;
v___y_4218_ = v_a_4196_;
v___y_4219_ = v_a_4197_;
v___y_4220_ = v_a_4198_;
v___y_4221_ = v_a_4199_;
v___y_4222_ = v_a_4200_;
v___y_4223_ = v_a_4201_;
v___y_4224_ = v_a_4202_;
v___y_4225_ = v_a_4203_;
v___y_4226_ = v_a_4204_;
goto v___jp_4214_;
}
else
{
goto v___jp_4206_;
}
}
}
else
{
goto v___jp_4206_;
}
}
v___jp_4214_:
{
lean_object* v___x_4227_; 
v___x_4227_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_v_4212_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; lean_object* v___x_4229_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4228_);
lean_dec_ref_known(v___x_4227_, 1);
v___x_4229_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_object* v_a_4230_; lean_object* v___x_4231_; 
v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
lean_inc(v_a_4230_);
lean_dec_ref_known(v___x_4229_, 1);
v___x_4231_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_4228_, v_a_4230_, v___y_4217_);
lean_dec(v_a_4230_);
lean_dec(v_a_4228_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4247_; 
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4234_ = v___x_4231_;
v_isShared_4235_ = v_isSharedCheck_4247_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_a_4232_);
lean_dec(v___x_4231_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4247_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
uint8_t v___x_4236_; 
v___x_4236_ = lean_unbox(v_a_4232_);
lean_dec(v_a_4232_);
if (v___x_4236_ == 0)
{
uint8_t v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4240_; 
v___x_4237_ = 1;
v___x_4238_ = lean_box(v___x_4237_);
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 0, v___x_4238_);
v___x_4240_ = v___x_4234_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v___x_4238_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
else
{
uint8_t v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4245_; 
v___x_4242_ = 0;
v___x_4243_ = lean_box(v___x_4242_);
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 0, v___x_4243_);
v___x_4245_ = v___x_4234_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v___x_4243_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
}
else
{
return v___x_4231_;
}
}
else
{
lean_object* v_a_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4255_; 
lean_dec(v_a_4228_);
v_a_4248_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4250_ = v___x_4229_;
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_a_4248_);
lean_dec(v___x_4229_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4253_; 
if (v_isShared_4251_ == 0)
{
v___x_4253_ = v___x_4250_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4248_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
v_a_4256_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4227_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4227_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
}
else
{
goto v___jp_4206_;
}
v___jp_4206_:
{
uint8_t v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4207_ = 0;
v___x_4208_ = lean_box(v___x_4207_);
v___x_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
return v___x_4209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq___boxed(lean_object* v_c_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_){
_start:
{
lean_object* v_res_4289_; 
v_res_4289_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v_c_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
lean_dec(v_a_4287_);
lean_dec_ref(v_a_4286_);
lean_dec(v_a_4285_);
lean_dec_ref(v_a_4284_);
lean_dec(v_a_4283_);
lean_dec_ref(v_a_4282_);
lean_dec(v_a_4281_);
lean_dec_ref(v_a_4280_);
lean_dec(v_a_4279_);
lean_dec(v_a_4278_);
lean_dec(v_a_4277_);
lean_dec_ref(v_c_4276_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(lean_object* v_c_4290_){
_start:
{
lean_object* v_p_4292_; 
v_p_4292_ = lean_ctor_get(v_c_4290_, 0);
if (lean_obj_tag(v_p_4292_) == 1)
{
lean_object* v_k_4293_; lean_object* v___x_4294_; uint8_t v___x_4295_; 
v_k_4293_ = lean_ctor_get(v_p_4292_, 0);
v___x_4294_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_4295_ = lean_int_dec_lt(v_k_4293_, v___x_4294_);
if (v___x_4295_ == 0)
{
lean_object* v___x_4296_; 
v___x_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4296_, 0, v_c_4290_);
return v___x_4296_;
}
else
{
lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4297_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_4292_);
v___x_4298_ = l_Lean_Grind_Linarith_Poly_mul(v_p_4292_, v___x_4297_);
v___x_4299_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4299_, 0, v_c_4290_);
v___x_4300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4300_, 0, v___x_4298_);
lean_ctor_set(v___x_4300_, 1, v___x_4299_);
v___x_4301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4300_);
return v___x_4301_;
}
}
else
{
lean_object* v___x_4302_; 
v___x_4302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4302_, 0, v_c_4290_);
return v___x_4302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg___boxed(lean_object* v_c_4303_, lean_object* v_a_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4303_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(lean_object* v_c_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_){
_start:
{
lean_object* v___x_4319_; 
v___x_4319_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4306_);
return v___x_4319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___boxed(lean_object* v_c_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_){
_start:
{
lean_object* v_res_4333_; 
v_res_4333_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(v_c_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_);
lean_dec(v_a_4331_);
lean_dec_ref(v_a_4330_);
lean_dec(v_a_4329_);
lean_dec_ref(v_a_4328_);
lean_dec(v_a_4327_);
lean_dec_ref(v_a_4326_);
lean_dec(v_a_4325_);
lean_dec_ref(v_a_4324_);
lean_dec(v_a_4323_);
lean_dec(v_a_4322_);
lean_dec(v_a_4321_);
return v_res_4333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(lean_object* v___y_4334_, lean_object* v_snd_4335_, lean_object* v_fst_4336_, lean_object* v_s_4337_){
_start:
{
lean_object* v_structs_4338_; lean_object* v_typeIdOf_4339_; lean_object* v_exprToStructId_4340_; lean_object* v_exprToStructIdEntries_4341_; lean_object* v_forbiddenNatModules_4342_; lean_object* v_natStructs_4343_; lean_object* v_natTypeIdOf_4344_; lean_object* v_exprToNatStructId_4345_; lean_object* v___x_4346_; uint8_t v___x_4347_; 
v_structs_4338_ = lean_ctor_get(v_s_4337_, 0);
v_typeIdOf_4339_ = lean_ctor_get(v_s_4337_, 1);
v_exprToStructId_4340_ = lean_ctor_get(v_s_4337_, 2);
v_exprToStructIdEntries_4341_ = lean_ctor_get(v_s_4337_, 3);
v_forbiddenNatModules_4342_ = lean_ctor_get(v_s_4337_, 4);
v_natStructs_4343_ = lean_ctor_get(v_s_4337_, 5);
v_natTypeIdOf_4344_ = lean_ctor_get(v_s_4337_, 6);
v_exprToNatStructId_4345_ = lean_ctor_get(v_s_4337_, 7);
v___x_4346_ = lean_array_get_size(v_structs_4338_);
v___x_4347_ = lean_nat_dec_lt(v___y_4334_, v___x_4346_);
if (v___x_4347_ == 0)
{
lean_dec(v_fst_4336_);
lean_dec_ref(v_snd_4335_);
return v_s_4337_;
}
else
{
lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4411_; 
lean_inc_ref(v_exprToNatStructId_4345_);
lean_inc_ref(v_natTypeIdOf_4344_);
lean_inc_ref(v_natStructs_4343_);
lean_inc_ref(v_forbiddenNatModules_4342_);
lean_inc_ref(v_exprToStructIdEntries_4341_);
lean_inc_ref(v_exprToStructId_4340_);
lean_inc_ref(v_typeIdOf_4339_);
lean_inc_ref(v_structs_4338_);
v_isSharedCheck_4411_ = !lean_is_exclusive(v_s_4337_);
if (v_isSharedCheck_4411_ == 0)
{
lean_object* v_unused_4412_; lean_object* v_unused_4413_; lean_object* v_unused_4414_; lean_object* v_unused_4415_; lean_object* v_unused_4416_; lean_object* v_unused_4417_; lean_object* v_unused_4418_; lean_object* v_unused_4419_; 
v_unused_4412_ = lean_ctor_get(v_s_4337_, 7);
lean_dec(v_unused_4412_);
v_unused_4413_ = lean_ctor_get(v_s_4337_, 6);
lean_dec(v_unused_4413_);
v_unused_4414_ = lean_ctor_get(v_s_4337_, 5);
lean_dec(v_unused_4414_);
v_unused_4415_ = lean_ctor_get(v_s_4337_, 4);
lean_dec(v_unused_4415_);
v_unused_4416_ = lean_ctor_get(v_s_4337_, 3);
lean_dec(v_unused_4416_);
v_unused_4417_ = lean_ctor_get(v_s_4337_, 2);
lean_dec(v_unused_4417_);
v_unused_4418_ = lean_ctor_get(v_s_4337_, 1);
lean_dec(v_unused_4418_);
v_unused_4419_ = lean_ctor_get(v_s_4337_, 0);
lean_dec(v_unused_4419_);
v___x_4349_ = v_s_4337_;
v_isShared_4350_ = v_isSharedCheck_4411_;
goto v_resetjp_4348_;
}
else
{
lean_dec(v_s_4337_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4411_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v_v_4351_; lean_object* v_id_4352_; lean_object* v_ringId_x3f_4353_; lean_object* v_type_4354_; lean_object* v_u_4355_; lean_object* v_intModuleInst_4356_; lean_object* v_leInst_x3f_4357_; lean_object* v_ltInst_x3f_4358_; lean_object* v_lawfulOrderLTInst_x3f_4359_; lean_object* v_isPreorderInst_x3f_4360_; lean_object* v_orderedAddInst_x3f_4361_; lean_object* v_isLinearInst_x3f_4362_; lean_object* v_noNatDivInst_x3f_4363_; lean_object* v_ringInst_x3f_4364_; lean_object* v_commRingInst_x3f_4365_; lean_object* v_orderedRingInst_x3f_4366_; lean_object* v_fieldInst_x3f_4367_; lean_object* v_charInst_x3f_4368_; lean_object* v_zero_4369_; lean_object* v_ofNatZero_4370_; lean_object* v_one_x3f_4371_; lean_object* v_leFn_x3f_4372_; lean_object* v_ltFn_x3f_4373_; lean_object* v_addFn_4374_; lean_object* v_zsmulFn_4375_; lean_object* v_nsmulFn_4376_; lean_object* v_zsmulFn_x3f_4377_; lean_object* v_nsmulFn_x3f_4378_; lean_object* v_homomulFn_x3f_4379_; lean_object* v_subFn_4380_; lean_object* v_negFn_4381_; lean_object* v_vars_4382_; lean_object* v_varMap_4383_; lean_object* v_lowers_4384_; lean_object* v_uppers_4385_; lean_object* v_diseqs_4386_; lean_object* v_assignment_4387_; uint8_t v_caseSplits_4388_; lean_object* v_conflict_x3f_4389_; lean_object* v_diseqSplits_4390_; lean_object* v_elimEqs_4391_; lean_object* v_elimStack_4392_; lean_object* v_occurs_4393_; lean_object* v_ignored_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4410_; 
v_v_4351_ = lean_array_fget(v_structs_4338_, v___y_4334_);
v_id_4352_ = lean_ctor_get(v_v_4351_, 0);
v_ringId_x3f_4353_ = lean_ctor_get(v_v_4351_, 1);
v_type_4354_ = lean_ctor_get(v_v_4351_, 2);
v_u_4355_ = lean_ctor_get(v_v_4351_, 3);
v_intModuleInst_4356_ = lean_ctor_get(v_v_4351_, 4);
v_leInst_x3f_4357_ = lean_ctor_get(v_v_4351_, 5);
v_ltInst_x3f_4358_ = lean_ctor_get(v_v_4351_, 6);
v_lawfulOrderLTInst_x3f_4359_ = lean_ctor_get(v_v_4351_, 7);
v_isPreorderInst_x3f_4360_ = lean_ctor_get(v_v_4351_, 8);
v_orderedAddInst_x3f_4361_ = lean_ctor_get(v_v_4351_, 9);
v_isLinearInst_x3f_4362_ = lean_ctor_get(v_v_4351_, 10);
v_noNatDivInst_x3f_4363_ = lean_ctor_get(v_v_4351_, 11);
v_ringInst_x3f_4364_ = lean_ctor_get(v_v_4351_, 12);
v_commRingInst_x3f_4365_ = lean_ctor_get(v_v_4351_, 13);
v_orderedRingInst_x3f_4366_ = lean_ctor_get(v_v_4351_, 14);
v_fieldInst_x3f_4367_ = lean_ctor_get(v_v_4351_, 15);
v_charInst_x3f_4368_ = lean_ctor_get(v_v_4351_, 16);
v_zero_4369_ = lean_ctor_get(v_v_4351_, 17);
v_ofNatZero_4370_ = lean_ctor_get(v_v_4351_, 18);
v_one_x3f_4371_ = lean_ctor_get(v_v_4351_, 19);
v_leFn_x3f_4372_ = lean_ctor_get(v_v_4351_, 20);
v_ltFn_x3f_4373_ = lean_ctor_get(v_v_4351_, 21);
v_addFn_4374_ = lean_ctor_get(v_v_4351_, 22);
v_zsmulFn_4375_ = lean_ctor_get(v_v_4351_, 23);
v_nsmulFn_4376_ = lean_ctor_get(v_v_4351_, 24);
v_zsmulFn_x3f_4377_ = lean_ctor_get(v_v_4351_, 25);
v_nsmulFn_x3f_4378_ = lean_ctor_get(v_v_4351_, 26);
v_homomulFn_x3f_4379_ = lean_ctor_get(v_v_4351_, 27);
v_subFn_4380_ = lean_ctor_get(v_v_4351_, 28);
v_negFn_4381_ = lean_ctor_get(v_v_4351_, 29);
v_vars_4382_ = lean_ctor_get(v_v_4351_, 30);
v_varMap_4383_ = lean_ctor_get(v_v_4351_, 31);
v_lowers_4384_ = lean_ctor_get(v_v_4351_, 32);
v_uppers_4385_ = lean_ctor_get(v_v_4351_, 33);
v_diseqs_4386_ = lean_ctor_get(v_v_4351_, 34);
v_assignment_4387_ = lean_ctor_get(v_v_4351_, 35);
v_caseSplits_4388_ = lean_ctor_get_uint8(v_v_4351_, sizeof(void*)*42);
v_conflict_x3f_4389_ = lean_ctor_get(v_v_4351_, 36);
v_diseqSplits_4390_ = lean_ctor_get(v_v_4351_, 37);
v_elimEqs_4391_ = lean_ctor_get(v_v_4351_, 38);
v_elimStack_4392_ = lean_ctor_get(v_v_4351_, 39);
v_occurs_4393_ = lean_ctor_get(v_v_4351_, 40);
v_ignored_4394_ = lean_ctor_get(v_v_4351_, 41);
v_isSharedCheck_4410_ = !lean_is_exclusive(v_v_4351_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4396_ = v_v_4351_;
v_isShared_4397_ = v_isSharedCheck_4410_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_ignored_4394_);
lean_inc(v_occurs_4393_);
lean_inc(v_elimStack_4392_);
lean_inc(v_elimEqs_4391_);
lean_inc(v_diseqSplits_4390_);
lean_inc(v_conflict_x3f_4389_);
lean_inc(v_assignment_4387_);
lean_inc(v_diseqs_4386_);
lean_inc(v_uppers_4385_);
lean_inc(v_lowers_4384_);
lean_inc(v_varMap_4383_);
lean_inc(v_vars_4382_);
lean_inc(v_negFn_4381_);
lean_inc(v_subFn_4380_);
lean_inc(v_homomulFn_x3f_4379_);
lean_inc(v_nsmulFn_x3f_4378_);
lean_inc(v_zsmulFn_x3f_4377_);
lean_inc(v_nsmulFn_4376_);
lean_inc(v_zsmulFn_4375_);
lean_inc(v_addFn_4374_);
lean_inc(v_ltFn_x3f_4373_);
lean_inc(v_leFn_x3f_4372_);
lean_inc(v_one_x3f_4371_);
lean_inc(v_ofNatZero_4370_);
lean_inc(v_zero_4369_);
lean_inc(v_charInst_x3f_4368_);
lean_inc(v_fieldInst_x3f_4367_);
lean_inc(v_orderedRingInst_x3f_4366_);
lean_inc(v_commRingInst_x3f_4365_);
lean_inc(v_ringInst_x3f_4364_);
lean_inc(v_noNatDivInst_x3f_4363_);
lean_inc(v_isLinearInst_x3f_4362_);
lean_inc(v_orderedAddInst_x3f_4361_);
lean_inc(v_isPreorderInst_x3f_4360_);
lean_inc(v_lawfulOrderLTInst_x3f_4359_);
lean_inc(v_ltInst_x3f_4358_);
lean_inc(v_leInst_x3f_4357_);
lean_inc(v_intModuleInst_4356_);
lean_inc(v_u_4355_);
lean_inc(v_type_4354_);
lean_inc(v_ringId_x3f_4353_);
lean_inc(v_id_4352_);
lean_dec(v_v_4351_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4410_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4398_; lean_object* v_xs_x27_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4404_; 
v___x_4398_ = lean_box(0);
v_xs_x27_4399_ = lean_array_fset(v_structs_4338_, v___y_4334_, v___x_4398_);
v___x_4400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4400_, 0, v_snd_4335_);
v___x_4401_ = l_Lean_PersistentArray_set___redArg(v_elimEqs_4391_, v_fst_4336_, v___x_4400_);
v___x_4402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4402_, 0, v_fst_4336_);
lean_ctor_set(v___x_4402_, 1, v_elimStack_4392_);
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 39, v___x_4402_);
lean_ctor_set(v___x_4396_, 38, v___x_4401_);
v___x_4404_ = v___x_4396_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_id_4352_);
lean_ctor_set(v_reuseFailAlloc_4409_, 1, v_ringId_x3f_4353_);
lean_ctor_set(v_reuseFailAlloc_4409_, 2, v_type_4354_);
lean_ctor_set(v_reuseFailAlloc_4409_, 3, v_u_4355_);
lean_ctor_set(v_reuseFailAlloc_4409_, 4, v_intModuleInst_4356_);
lean_ctor_set(v_reuseFailAlloc_4409_, 5, v_leInst_x3f_4357_);
lean_ctor_set(v_reuseFailAlloc_4409_, 6, v_ltInst_x3f_4358_);
lean_ctor_set(v_reuseFailAlloc_4409_, 7, v_lawfulOrderLTInst_x3f_4359_);
lean_ctor_set(v_reuseFailAlloc_4409_, 8, v_isPreorderInst_x3f_4360_);
lean_ctor_set(v_reuseFailAlloc_4409_, 9, v_orderedAddInst_x3f_4361_);
lean_ctor_set(v_reuseFailAlloc_4409_, 10, v_isLinearInst_x3f_4362_);
lean_ctor_set(v_reuseFailAlloc_4409_, 11, v_noNatDivInst_x3f_4363_);
lean_ctor_set(v_reuseFailAlloc_4409_, 12, v_ringInst_x3f_4364_);
lean_ctor_set(v_reuseFailAlloc_4409_, 13, v_commRingInst_x3f_4365_);
lean_ctor_set(v_reuseFailAlloc_4409_, 14, v_orderedRingInst_x3f_4366_);
lean_ctor_set(v_reuseFailAlloc_4409_, 15, v_fieldInst_x3f_4367_);
lean_ctor_set(v_reuseFailAlloc_4409_, 16, v_charInst_x3f_4368_);
lean_ctor_set(v_reuseFailAlloc_4409_, 17, v_zero_4369_);
lean_ctor_set(v_reuseFailAlloc_4409_, 18, v_ofNatZero_4370_);
lean_ctor_set(v_reuseFailAlloc_4409_, 19, v_one_x3f_4371_);
lean_ctor_set(v_reuseFailAlloc_4409_, 20, v_leFn_x3f_4372_);
lean_ctor_set(v_reuseFailAlloc_4409_, 21, v_ltFn_x3f_4373_);
lean_ctor_set(v_reuseFailAlloc_4409_, 22, v_addFn_4374_);
lean_ctor_set(v_reuseFailAlloc_4409_, 23, v_zsmulFn_4375_);
lean_ctor_set(v_reuseFailAlloc_4409_, 24, v_nsmulFn_4376_);
lean_ctor_set(v_reuseFailAlloc_4409_, 25, v_zsmulFn_x3f_4377_);
lean_ctor_set(v_reuseFailAlloc_4409_, 26, v_nsmulFn_x3f_4378_);
lean_ctor_set(v_reuseFailAlloc_4409_, 27, v_homomulFn_x3f_4379_);
lean_ctor_set(v_reuseFailAlloc_4409_, 28, v_subFn_4380_);
lean_ctor_set(v_reuseFailAlloc_4409_, 29, v_negFn_4381_);
lean_ctor_set(v_reuseFailAlloc_4409_, 30, v_vars_4382_);
lean_ctor_set(v_reuseFailAlloc_4409_, 31, v_varMap_4383_);
lean_ctor_set(v_reuseFailAlloc_4409_, 32, v_lowers_4384_);
lean_ctor_set(v_reuseFailAlloc_4409_, 33, v_uppers_4385_);
lean_ctor_set(v_reuseFailAlloc_4409_, 34, v_diseqs_4386_);
lean_ctor_set(v_reuseFailAlloc_4409_, 35, v_assignment_4387_);
lean_ctor_set(v_reuseFailAlloc_4409_, 36, v_conflict_x3f_4389_);
lean_ctor_set(v_reuseFailAlloc_4409_, 37, v_diseqSplits_4390_);
lean_ctor_set(v_reuseFailAlloc_4409_, 38, v___x_4401_);
lean_ctor_set(v_reuseFailAlloc_4409_, 39, v___x_4402_);
lean_ctor_set(v_reuseFailAlloc_4409_, 40, v_occurs_4393_);
lean_ctor_set(v_reuseFailAlloc_4409_, 41, v_ignored_4394_);
lean_ctor_set_uint8(v_reuseFailAlloc_4409_, sizeof(void*)*42, v_caseSplits_4388_);
v___x_4404_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
lean_object* v___x_4405_; lean_object* v___x_4407_; 
v___x_4405_ = lean_array_fset(v_xs_x27_4399_, v___y_4334_, v___x_4404_);
if (v_isShared_4350_ == 0)
{
lean_ctor_set(v___x_4349_, 0, v___x_4405_);
v___x_4407_ = v___x_4349_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v___x_4405_);
lean_ctor_set(v_reuseFailAlloc_4408_, 1, v_typeIdOf_4339_);
lean_ctor_set(v_reuseFailAlloc_4408_, 2, v_exprToStructId_4340_);
lean_ctor_set(v_reuseFailAlloc_4408_, 3, v_exprToStructIdEntries_4341_);
lean_ctor_set(v_reuseFailAlloc_4408_, 4, v_forbiddenNatModules_4342_);
lean_ctor_set(v_reuseFailAlloc_4408_, 5, v_natStructs_4343_);
lean_ctor_set(v_reuseFailAlloc_4408_, 6, v_natTypeIdOf_4344_);
lean_ctor_set(v_reuseFailAlloc_4408_, 7, v_exprToNatStructId_4345_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed(lean_object* v___y_4420_, lean_object* v_snd_4421_, lean_object* v_fst_4422_, lean_object* v_s_4423_){
_start:
{
lean_object* v_res_4424_; 
v_res_4424_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(v___y_4420_, v_snd_4421_, v_fst_4422_, v_s_4423_);
lean_dec(v___y_4420_);
return v_res_4424_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1(void){
_start:
{
lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4426_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0));
v___x_4427_ = l_Lean_stringToMessageData(v___x_4426_);
return v___x_4427_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4(void){
_start:
{
lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___x_4433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4435_ = l_Lean_Name_append(v___x_4434_, v___x_4433_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object* v_c_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_){
_start:
{
lean_object* v___y_4453_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v_toCold_4515_; lean_object* v_options_4516_; lean_object* v_inheritedTraceOptions_4517_; uint8_t v_hasTrace_4518_; lean_object* v___y_4520_; lean_object* v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v_options_4535_; lean_object* v_inheritedTraceOptions_4536_; lean_object* v___y_4537_; lean_object* v___y_4554_; lean_object* v___y_4555_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; 
v_toCold_4515_ = lean_ctor_get(v_a_4446_, 0);
v_options_4516_ = lean_ctor_get(v_toCold_4515_, 2);
v_inheritedTraceOptions_4517_ = lean_ctor_get(v_toCold_4515_, 11);
v_hasTrace_4518_ = lean_ctor_get_uint8(v_options_4516_, sizeof(void*)*1);
if (v_hasTrace_4518_ == 0)
{
v___y_4554_ = v_a_4437_;
v___y_4555_ = v_a_4438_;
v___y_4556_ = v_a_4439_;
v___y_4557_ = v_a_4440_;
v___y_4558_ = v_a_4441_;
v___y_4559_ = v_a_4442_;
v___y_4560_ = v_a_4443_;
v___y_4561_ = v_a_4444_;
v___y_4562_ = v_a_4445_;
v___y_4563_ = v_a_4446_;
v___y_4564_ = v_a_4447_;
goto v___jp_4553_;
}
else
{
lean_object* v_cls_4662_; lean_object* v___x_4663_; uint8_t v___x_4664_; 
v_cls_4662_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_4663_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_4664_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4517_, v_options_4516_, v___x_4663_);
if (v___x_4664_ == 0)
{
v___y_4554_ = v_a_4437_;
v___y_4555_ = v_a_4438_;
v___y_4556_ = v_a_4439_;
v___y_4557_ = v_a_4440_;
v___y_4558_ = v_a_4441_;
v___y_4559_ = v_a_4442_;
v___y_4560_ = v_a_4443_;
v___y_4561_ = v_a_4444_;
v___y_4562_ = v_a_4445_;
v___y_4563_ = v_a_4446_;
v___y_4564_ = v_a_4447_;
goto v___jp_4553_;
}
else
{
lean_object* v___x_4665_; 
v___x_4665_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; 
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
lean_inc(v_a_4666_);
lean_dec_ref_known(v___x_4665_, 1);
v___x_4667_ = l_Lean_MessageData_ofExpr(v_a_4666_);
v___x_4668_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4662_, v___x_4667_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_);
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_dec_ref_known(v___x_4668_, 1);
v___y_4554_ = v_a_4437_;
v___y_4555_ = v_a_4438_;
v___y_4556_ = v_a_4439_;
v___y_4557_ = v_a_4440_;
v___y_4558_ = v_a_4441_;
v___y_4559_ = v_a_4442_;
v___y_4560_ = v_a_4443_;
v___y_4561_ = v_a_4444_;
v___y_4562_ = v_a_4445_;
v___y_4563_ = v_a_4446_;
v___y_4564_ = v_a_4447_;
goto v___jp_4553_;
}
else
{
lean_dec_ref(v_c_4436_);
return v___x_4668_;
}
}
else
{
lean_object* v_a_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4676_; 
lean_dec_ref(v_c_4436_);
v_a_4669_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4676_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4671_ = v___x_4665_;
v_isShared_4672_ = v_isSharedCheck_4676_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_a_4669_);
lean_dec(v___x_4665_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4676_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4674_; 
if (v_isShared_4672_ == 0)
{
v___x_4674_ = v___x_4671_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_a_4669_);
v___x_4674_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
return v___x_4674_;
}
}
}
}
}
v___jp_4449_:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4450_ = lean_box(0);
v___x_4451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4451_, 0, v___x_4450_);
return v___x_4451_;
}
v___jp_4452_:
{
lean_object* v___f_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
lean_inc(v___y_4458_);
v___f_4469_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4469_, 0, v___y_4458_);
lean_closure_set(v___f_4469_, 1, v___y_4454_);
lean_closure_set(v___f_4469_, 2, v___y_4453_);
v___x_4470_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4471_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4470_, v___f_4469_, v___y_4459_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_object* v___x_4472_; 
lean_dec_ref_known(v___x_4471_, 1);
v___x_4472_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v___y_4457_, v___y_4456_, v___y_4455_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
return v___x_4472_;
}
else
{
lean_dec(v___y_4457_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
return v___x_4471_;
}
}
v___jp_4473_:
{
lean_object* v___x_4490_; 
v___x_4490_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_object* v_a_4491_; uint8_t v_caseSplits_4492_; 
v_a_4491_ = lean_ctor_get(v___x_4490_, 0);
lean_inc(v_a_4491_);
lean_dec_ref_known(v___x_4490_, 1);
v_caseSplits_4492_ = lean_ctor_get_uint8(v_a_4491_, sizeof(void*)*42);
lean_dec(v_a_4491_);
if (v_caseSplits_4492_ == 0)
{
lean_object* v___x_4493_; 
v___x_4493_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v___y_4477_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
if (lean_obj_tag(v___x_4493_) == 0)
{
lean_object* v_a_4494_; uint8_t v___x_4495_; 
v_a_4494_ = lean_ctor_get(v___x_4493_, 0);
lean_inc(v_a_4494_);
lean_dec_ref_known(v___x_4493_, 1);
v___x_4495_ = lean_unbox(v_a_4494_);
lean_dec(v_a_4494_);
if (v___x_4495_ == 0)
{
v___y_4453_ = v___y_4475_;
v___y_4454_ = v___y_4474_;
v___y_4455_ = v___y_4477_;
v___y_4456_ = v___y_4476_;
v___y_4457_ = v___y_4478_;
v___y_4458_ = v___y_4479_;
v___y_4459_ = v___y_4480_;
v___y_4460_ = v___y_4481_;
v___y_4461_ = v___y_4482_;
v___y_4462_ = v___y_4483_;
v___y_4463_ = v___y_4484_;
v___y_4464_ = v___y_4485_;
v___y_4465_ = v___y_4486_;
v___y_4466_ = v___y_4487_;
v___y_4467_ = v___y_4488_;
v___y_4468_ = v___y_4489_;
goto v___jp_4452_;
}
else
{
lean_object* v___x_4496_; lean_object* v_a_4497_; lean_object* v___x_4498_; 
lean_inc_ref(v___y_4477_);
v___x_4496_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v___y_4477_);
v_a_4497_ = lean_ctor_get(v___x_4496_, 0);
lean_inc(v_a_4497_);
lean_dec_ref(v___x_4496_);
v___x_4498_ = l_Lean_Meta_Grind_Arith_Linear_propagateImpEq(v_a_4497_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_dec_ref_known(v___x_4498_, 1);
v___y_4453_ = v___y_4475_;
v___y_4454_ = v___y_4474_;
v___y_4455_ = v___y_4477_;
v___y_4456_ = v___y_4476_;
v___y_4457_ = v___y_4478_;
v___y_4458_ = v___y_4479_;
v___y_4459_ = v___y_4480_;
v___y_4460_ = v___y_4481_;
v___y_4461_ = v___y_4482_;
v___y_4462_ = v___y_4483_;
v___y_4463_ = v___y_4484_;
v___y_4464_ = v___y_4485_;
v___y_4465_ = v___y_4486_;
v___y_4466_ = v___y_4487_;
v___y_4467_ = v___y_4488_;
v___y_4468_ = v___y_4489_;
goto v___jp_4452_;
}
else
{
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
return v___x_4498_;
}
}
}
else
{
lean_object* v_a_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4506_; 
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
v_a_4499_ = lean_ctor_get(v___x_4493_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4501_ = v___x_4493_;
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_a_4499_);
lean_dec(v___x_4493_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4504_; 
if (v_isShared_4502_ == 0)
{
v___x_4504_ = v___x_4501_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_a_4499_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
return v___x_4504_;
}
}
}
}
else
{
v___y_4453_ = v___y_4475_;
v___y_4454_ = v___y_4474_;
v___y_4455_ = v___y_4477_;
v___y_4456_ = v___y_4476_;
v___y_4457_ = v___y_4478_;
v___y_4458_ = v___y_4479_;
v___y_4459_ = v___y_4480_;
v___y_4460_ = v___y_4481_;
v___y_4461_ = v___y_4482_;
v___y_4462_ = v___y_4483_;
v___y_4463_ = v___y_4484_;
v___y_4464_ = v___y_4485_;
v___y_4465_ = v___y_4486_;
v___y_4466_ = v___y_4487_;
v___y_4467_ = v___y_4488_;
v___y_4468_ = v___y_4489_;
goto v___jp_4452_;
}
}
else
{
lean_object* v_a_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4514_; 
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
v_a_4507_ = lean_ctor_get(v___x_4490_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4490_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4509_ = v___x_4490_;
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_dec(v___x_4490_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4512_; 
if (v_isShared_4510_ == 0)
{
v___x_4512_ = v___x_4509_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
}
v___jp_4519_:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; uint8_t v___x_4540_; 
v___x_4538_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_4539_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_4540_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4536_, v_options_4535_, v___x_4539_);
if (v___x_4540_ == 0)
{
v___y_4474_ = v___y_4521_;
v___y_4475_ = v___y_4520_;
v___y_4476_ = v___y_4523_;
v___y_4477_ = v___y_4522_;
v___y_4478_ = v___y_4524_;
v___y_4479_ = v___y_4525_;
v___y_4480_ = v___y_4526_;
v___y_4481_ = v___y_4527_;
v___y_4482_ = v___y_4528_;
v___y_4483_ = v___y_4529_;
v___y_4484_ = v___y_4530_;
v___y_4485_ = v___y_4531_;
v___y_4486_ = v___y_4532_;
v___y_4487_ = v___y_4533_;
v___y_4488_ = v___y_4534_;
v___y_4489_ = v___y_4537_;
goto v___jp_4473_;
}
else
{
lean_object* v___x_4541_; 
v___x_4541_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v___y_4522_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4537_);
if (lean_obj_tag(v___x_4541_) == 0)
{
lean_object* v_a_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; 
v_a_4542_ = lean_ctor_get(v___x_4541_, 0);
lean_inc(v_a_4542_);
lean_dec_ref_known(v___x_4541_, 1);
v___x_4543_ = l_Lean_MessageData_ofExpr(v_a_4542_);
v___x_4544_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4538_, v___x_4543_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4537_);
if (lean_obj_tag(v___x_4544_) == 0)
{
lean_dec_ref_known(v___x_4544_, 1);
v___y_4474_ = v___y_4521_;
v___y_4475_ = v___y_4520_;
v___y_4476_ = v___y_4523_;
v___y_4477_ = v___y_4522_;
v___y_4478_ = v___y_4524_;
v___y_4479_ = v___y_4525_;
v___y_4480_ = v___y_4526_;
v___y_4481_ = v___y_4527_;
v___y_4482_ = v___y_4528_;
v___y_4483_ = v___y_4529_;
v___y_4484_ = v___y_4530_;
v___y_4485_ = v___y_4531_;
v___y_4486_ = v___y_4532_;
v___y_4487_ = v___y_4533_;
v___y_4488_ = v___y_4534_;
v___y_4489_ = v___y_4537_;
goto v___jp_4473_;
}
else
{
lean_dec(v___y_4524_);
lean_dec(v___y_4523_);
lean_dec_ref(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
return v___x_4544_;
}
}
else
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4552_; 
lean_dec(v___y_4524_);
lean_dec(v___y_4523_);
lean_dec_ref(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
v_a_4545_ = lean_ctor_get(v___x_4541_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4547_ = v___x_4541_;
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v___x_4541_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4550_; 
if (v_isShared_4548_ == 0)
{
v___x_4550_ = v___x_4547_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v_a_4545_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
}
}
}
v___jp_4553_:
{
lean_object* v___x_4565_; 
lean_inc_ref(v___y_4563_);
v___x_4565_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_4436_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4565_) == 0)
{
lean_object* v_a_4566_; lean_object* v_p_4567_; lean_object* v___x_4568_; uint8_t v___x_4569_; 
v_a_4566_ = lean_ctor_get(v___x_4565_, 0);
lean_inc(v_a_4566_);
lean_dec_ref_known(v___x_4565_, 1);
v_p_4567_ = lean_ctor_get(v_a_4566_, 0);
v___x_4568_ = lean_box(0);
v___x_4569_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_4567_, v___x_4568_);
if (v___x_4569_ == 0)
{
lean_object* v___x_4570_; 
v___x_4570_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_a_4566_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4570_) == 0)
{
lean_object* v_a_4571_; lean_object* v_snd_4572_; lean_object* v_toCold_4573_; lean_object* v_options_4574_; uint8_t v_hasTrace_4575_; 
v_a_4571_ = lean_ctor_get(v___x_4570_, 0);
lean_inc(v_a_4571_);
lean_dec_ref_known(v___x_4570_, 1);
v_snd_4572_ = lean_ctor_get(v_a_4571_, 1);
lean_inc(v_snd_4572_);
v_toCold_4573_ = lean_ctor_get(v___y_4563_, 0);
v_options_4574_ = lean_ctor_get(v_toCold_4573_, 2);
v_hasTrace_4575_ = lean_ctor_get_uint8(v_options_4574_, sizeof(void*)*1);
if (v_hasTrace_4575_ == 0)
{
lean_object* v_fst_4576_; lean_object* v_fst_4577_; lean_object* v_snd_4578_; 
v_fst_4576_ = lean_ctor_get(v_a_4571_, 0);
lean_inc(v_fst_4576_);
lean_dec(v_a_4571_);
v_fst_4577_ = lean_ctor_get(v_snd_4572_, 0);
lean_inc_n(v_fst_4577_, 2);
v_snd_4578_ = lean_ctor_get(v_snd_4572_, 1);
lean_inc_n(v_snd_4578_, 2);
lean_dec(v_snd_4572_);
v___y_4474_ = v_snd_4578_;
v___y_4475_ = v_fst_4577_;
v___y_4476_ = v_fst_4577_;
v___y_4477_ = v_snd_4578_;
v___y_4478_ = v_fst_4576_;
v___y_4479_ = v___y_4554_;
v___y_4480_ = v___y_4555_;
v___y_4481_ = v___y_4556_;
v___y_4482_ = v___y_4557_;
v___y_4483_ = v___y_4558_;
v___y_4484_ = v___y_4559_;
v___y_4485_ = v___y_4560_;
v___y_4486_ = v___y_4561_;
v___y_4487_ = v___y_4562_;
v___y_4488_ = v___y_4563_;
v___y_4489_ = v___y_4564_;
goto v___jp_4473_;
}
else
{
lean_object* v_fst_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4625_; 
v_fst_4579_ = lean_ctor_get(v_a_4571_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v_a_4571_);
if (v_isSharedCheck_4625_ == 0)
{
lean_object* v_unused_4626_; 
v_unused_4626_ = lean_ctor_get(v_a_4571_, 1);
lean_dec(v_unused_4626_);
v___x_4581_ = v_a_4571_;
v_isShared_4582_ = v_isSharedCheck_4625_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_fst_4579_);
lean_dec(v_a_4571_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4625_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v_fst_4583_; lean_object* v_snd_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4624_; 
v_fst_4583_ = lean_ctor_get(v_snd_4572_, 0);
v_snd_4584_ = lean_ctor_get(v_snd_4572_, 1);
v_isSharedCheck_4624_ = !lean_is_exclusive(v_snd_4572_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4586_ = v_snd_4572_;
v_isShared_4587_ = v_isSharedCheck_4624_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_snd_4584_);
lean_inc(v_fst_4583_);
lean_dec(v_snd_4572_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4624_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v_inheritedTraceOptions_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; uint8_t v___x_4591_; 
v_inheritedTraceOptions_4588_ = lean_ctor_get(v_toCold_4573_, 11);
v___x_4589_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_4590_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_4591_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4588_, v_options_4574_, v___x_4590_);
if (v___x_4591_ == 0)
{
lean_del_object(v___x_4586_);
lean_del_object(v___x_4581_);
lean_inc(v_snd_4584_);
lean_inc(v_fst_4583_);
v___y_4520_ = v_fst_4583_;
v___y_4521_ = v_snd_4584_;
v___y_4522_ = v_snd_4584_;
v___y_4523_ = v_fst_4583_;
v___y_4524_ = v_fst_4579_;
v___y_4525_ = v___y_4554_;
v___y_4526_ = v___y_4555_;
v___y_4527_ = v___y_4556_;
v___y_4528_ = v___y_4557_;
v___y_4529_ = v___y_4558_;
v___y_4530_ = v___y_4559_;
v___y_4531_ = v___y_4560_;
v___y_4532_ = v___y_4561_;
v___y_4533_ = v___y_4562_;
v___y_4534_ = v___y_4563_;
v_options_4535_ = v_options_4574_;
v_inheritedTraceOptions_4536_ = v_inheritedTraceOptions_4588_;
v___y_4537_ = v___y_4564_;
goto v___jp_4519_;
}
else
{
lean_object* v___x_4592_; 
v___x_4592_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_4583_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4592_) == 0)
{
lean_object* v_a_4593_; lean_object* v___x_4594_; 
v_a_4593_ = lean_ctor_get(v___x_4592_, 0);
lean_inc(v_a_4593_);
lean_dec_ref_known(v___x_4592_, 1);
v___x_4594_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_4584_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4594_) == 0)
{
lean_object* v_a_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4599_; 
v_a_4595_ = lean_ctor_get(v___x_4594_, 0);
lean_inc(v_a_4595_);
lean_dec_ref_known(v___x_4594_, 1);
v___x_4596_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1);
v___x_4597_ = l_Lean_MessageData_ofExpr(v_a_4593_);
if (v_isShared_4587_ == 0)
{
lean_ctor_set_tag(v___x_4586_, 7);
lean_ctor_set(v___x_4586_, 1, v___x_4597_);
lean_ctor_set(v___x_4586_, 0, v___x_4596_);
v___x_4599_ = v___x_4586_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v___x_4596_);
lean_ctor_set(v_reuseFailAlloc_4607_, 1, v___x_4597_);
v___x_4599_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
lean_object* v___x_4600_; lean_object* v___x_4602_; 
v___x_4600_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_4582_ == 0)
{
lean_ctor_set_tag(v___x_4581_, 7);
lean_ctor_set(v___x_4581_, 1, v___x_4600_);
lean_ctor_set(v___x_4581_, 0, v___x_4599_);
v___x_4602_ = v___x_4581_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___x_4599_);
lean_ctor_set(v_reuseFailAlloc_4606_, 1, v___x_4600_);
v___x_4602_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4603_ = l_Lean_MessageData_ofExpr(v_a_4595_);
v___x_4604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4604_, 0, v___x_4602_);
lean_ctor_set(v___x_4604_, 1, v___x_4603_);
v___x_4605_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4589_, v___x_4604_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_dec_ref_known(v___x_4605_, 1);
lean_inc(v_snd_4584_);
lean_inc(v_fst_4583_);
v___y_4520_ = v_fst_4583_;
v___y_4521_ = v_snd_4584_;
v___y_4522_ = v_snd_4584_;
v___y_4523_ = v_fst_4583_;
v___y_4524_ = v_fst_4579_;
v___y_4525_ = v___y_4554_;
v___y_4526_ = v___y_4555_;
v___y_4527_ = v___y_4556_;
v___y_4528_ = v___y_4557_;
v___y_4529_ = v___y_4558_;
v___y_4530_ = v___y_4559_;
v___y_4531_ = v___y_4560_;
v___y_4532_ = v___y_4561_;
v___y_4533_ = v___y_4562_;
v___y_4534_ = v___y_4563_;
v_options_4535_ = v_options_4574_;
v_inheritedTraceOptions_4536_ = v_inheritedTraceOptions_4588_;
v___y_4537_ = v___y_4564_;
goto v___jp_4519_;
}
else
{
lean_dec(v_snd_4584_);
lean_dec(v_fst_4583_);
lean_dec(v_fst_4579_);
return v___x_4605_;
}
}
}
}
else
{
lean_object* v_a_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4615_; 
lean_dec(v_a_4593_);
lean_del_object(v___x_4586_);
lean_dec(v_snd_4584_);
lean_dec(v_fst_4583_);
lean_del_object(v___x_4581_);
lean_dec(v_fst_4579_);
v_a_4608_ = lean_ctor_get(v___x_4594_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v___x_4594_);
if (v_isSharedCheck_4615_ == 0)
{
v___x_4610_ = v___x_4594_;
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_a_4608_);
lean_dec(v___x_4594_);
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
lean_object* v_a_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4623_; 
lean_del_object(v___x_4586_);
lean_dec(v_snd_4584_);
lean_dec(v_fst_4583_);
lean_del_object(v___x_4581_);
lean_dec(v_fst_4579_);
v_a_4616_ = lean_ctor_get(v___x_4592_, 0);
v_isSharedCheck_4623_ = !lean_is_exclusive(v___x_4592_);
if (v_isSharedCheck_4623_ == 0)
{
v___x_4618_ = v___x_4592_;
v_isShared_4619_ = v_isSharedCheck_4623_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_a_4616_);
lean_dec(v___x_4592_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4623_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v___x_4621_; 
if (v_isShared_4619_ == 0)
{
v___x_4621_ = v___x_4618_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v_a_4616_);
v___x_4621_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
return v___x_4621_;
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
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4634_; 
v_a_4627_ = lean_ctor_get(v___x_4570_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4629_ = v___x_4570_;
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4570_);
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
else
{
lean_object* v_toCold_4635_; lean_object* v_options_4636_; uint8_t v_hasTrace_4637_; 
v_toCold_4635_ = lean_ctor_get(v___y_4563_, 0);
v_options_4636_ = lean_ctor_get(v_toCold_4635_, 2);
v_hasTrace_4637_ = lean_ctor_get_uint8(v_options_4636_, sizeof(void*)*1);
if (v_hasTrace_4637_ == 0)
{
lean_dec(v_a_4566_);
goto v___jp_4449_;
}
else
{
lean_object* v_inheritedTraceOptions_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; uint8_t v___x_4641_; 
v_inheritedTraceOptions_4638_ = lean_ctor_get(v_toCold_4635_, 11);
v___x_4639_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4640_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4);
v___x_4641_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4638_, v_options_4636_, v___x_4640_);
if (v___x_4641_ == 0)
{
lean_dec(v_a_4566_);
goto v___jp_4449_;
}
else
{
lean_object* v___x_4642_; 
v___x_4642_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_a_4566_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
lean_dec(v_a_4566_);
if (lean_obj_tag(v___x_4642_) == 0)
{
lean_object* v_a_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; 
v_a_4643_ = lean_ctor_get(v___x_4642_, 0);
lean_inc(v_a_4643_);
lean_dec_ref_known(v___x_4642_, 1);
v___x_4644_ = l_Lean_MessageData_ofExpr(v_a_4643_);
v___x_4645_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4639_, v___x_4644_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_dec_ref_known(v___x_4645_, 1);
goto v___jp_4449_;
}
else
{
return v___x_4645_;
}
}
else
{
lean_object* v_a_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4653_; 
v_a_4646_ = lean_ctor_get(v___x_4642_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v___x_4642_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4648_ = v___x_4642_;
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_a_4646_);
lean_dec(v___x_4642_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
lean_object* v___x_4651_; 
if (v_isShared_4649_ == 0)
{
v___x_4651_ = v___x_4648_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_a_4646_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
return v___x_4651_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4661_; 
v_a_4654_ = lean_ctor_get(v___x_4565_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4656_ = v___x_4565_;
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4565_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4659_; 
if (v_isShared_4657_ == 0)
{
v___x_4659_ = v___x_4656_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_a_4654_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object* v_c_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_){
_start:
{
lean_object* v_res_4690_; 
v_res_4690_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v_c_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_);
lean_dec(v_a_4688_);
lean_dec_ref(v_a_4687_);
lean_dec(v_a_4686_);
lean_dec_ref(v_a_4685_);
lean_dec(v_a_4684_);
lean_dec_ref(v_a_4683_);
lean_dec(v_a_4682_);
lean_dec_ref(v_a_4681_);
lean_dec(v_a_4680_);
lean_dec(v_a_4679_);
lean_dec(v_a_4678_);
return v_res_4690_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2(void){
_start:
{
lean_object* v_cls_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; 
v_cls_4695_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4696_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4697_ = l_Lean_Name_append(v___x_4696_, v_cls_4695_);
return v___x_4697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object* v_a_4698_, lean_object* v_b_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_){
_start:
{
lean_object* v_toCold_4708_; lean_object* v_options_4709_; uint8_t v_hasTrace_4710_; 
v_toCold_4708_ = lean_ctor_get(v_a_4702_, 0);
v_options_4709_ = lean_ctor_get(v_toCold_4708_, 2);
v_hasTrace_4710_ = lean_ctor_get_uint8(v_options_4709_, sizeof(void*)*1);
if (v_hasTrace_4710_ == 0)
{
lean_dec_ref(v_b_4699_);
lean_dec_ref(v_a_4698_);
goto v___jp_4705_;
}
else
{
lean_object* v_inheritedTraceOptions_4711_; lean_object* v_cls_4712_; lean_object* v___x_4713_; uint8_t v___x_4714_; 
v_inheritedTraceOptions_4711_ = lean_ctor_get(v_toCold_4708_, 11);
v_cls_4712_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4713_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2);
v___x_4714_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4711_, v_options_4709_, v___x_4713_);
if (v___x_4714_ == 0)
{
lean_dec_ref(v_b_4699_);
lean_dec_ref(v_a_4698_);
goto v___jp_4705_;
}
else
{
lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; 
v___x_4715_ = l_Lean_MessageData_ofExpr(v_a_4698_);
v___x_4716_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_4717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4715_);
lean_ctor_set(v___x_4717_, 1, v___x_4716_);
v___x_4718_ = l_Lean_MessageData_ofExpr(v_b_4699_);
v___x_4719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4719_, 0, v___x_4717_);
lean_ctor_set(v___x_4719_, 1, v___x_4718_);
v___x_4720_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4712_, v___x_4719_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_);
return v___x_4720_;
}
}
v___jp_4705_:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; 
v___x_4706_ = lean_box(0);
v___x_4707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4707_, 0, v___x_4706_);
return v___x_4707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object* v_a_4721_, lean_object* v_b_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_){
_start:
{
lean_object* v_res_4728_; 
v_res_4728_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4721_, v_b_4722_, v_a_4723_, v_a_4724_, v_a_4725_, v_a_4726_);
lean_dec(v_a_4726_);
lean_dec_ref(v_a_4725_);
lean_dec(v_a_4724_);
lean_dec_ref(v_a_4723_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object* v_a_4729_, lean_object* v_b_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_){
_start:
{
lean_object* v___x_4743_; 
v___x_4743_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4729_, v_b_4730_, v_a_4738_, v_a_4739_, v_a_4740_, v_a_4741_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object* v_a_4744_, lean_object* v_b_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(v_a_4744_, v_b_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_);
lean_dec(v_a_4756_);
lean_dec_ref(v_a_4755_);
lean_dec(v_a_4754_);
lean_dec_ref(v_a_4753_);
lean_dec(v_a_4752_);
lean_dec_ref(v_a_4751_);
lean_dec(v_a_4750_);
lean_dec_ref(v_a_4749_);
lean_dec(v_a_4748_);
lean_dec(v_a_4747_);
lean_dec(v_a_4746_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object* v_a_4759_, lean_object* v_b_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_){
_start:
{
lean_object* v___x_4773_; 
v___x_4773_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4759_, v_a_4762_);
if (lean_obj_tag(v___x_4773_) == 0)
{
lean_object* v_a_4774_; uint8_t v___x_4775_; lean_object* v___x_4776_; 
v_a_4774_ = lean_ctor_get(v___x_4773_, 0);
lean_inc(v_a_4774_);
lean_dec_ref_known(v___x_4773_, 1);
v___x_4775_ = 0;
lean_inc_ref(v_a_4759_);
v___x_4776_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_4759_, v___x_4775_, v_a_4774_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_);
if (lean_obj_tag(v___x_4776_) == 0)
{
lean_object* v_a_4777_; lean_object* v___x_4779_; uint8_t v_isShared_4780_; uint8_t v_isSharedCheck_4826_; 
v_a_4777_ = lean_ctor_get(v___x_4776_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4779_ = v___x_4776_;
v_isShared_4780_ = v_isSharedCheck_4826_;
goto v_resetjp_4778_;
}
else
{
lean_inc(v_a_4777_);
lean_dec(v___x_4776_);
v___x_4779_ = lean_box(0);
v_isShared_4780_ = v_isSharedCheck_4826_;
goto v_resetjp_4778_;
}
v_resetjp_4778_:
{
if (lean_obj_tag(v_a_4777_) == 1)
{
lean_object* v_val_4781_; lean_object* v___x_4782_; 
lean_del_object(v___x_4779_);
v_val_4781_ = lean_ctor_get(v_a_4777_, 0);
lean_inc(v_val_4781_);
lean_dec_ref_known(v_a_4777_, 1);
v___x_4782_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4760_, v_a_4762_);
if (lean_obj_tag(v___x_4782_) == 0)
{
lean_object* v_a_4783_; lean_object* v___x_4784_; 
v_a_4783_ = lean_ctor_get(v___x_4782_, 0);
lean_inc(v_a_4783_);
lean_dec_ref_known(v___x_4782_, 1);
lean_inc_ref(v_b_4760_);
v___x_4784_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_4760_, v___x_4775_, v_a_4783_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_);
if (lean_obj_tag(v___x_4784_) == 0)
{
lean_object* v_a_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4805_; 
v_a_4785_ = lean_ctor_get(v___x_4784_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4787_ = v___x_4784_;
v_isShared_4788_ = v_isSharedCheck_4805_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_a_4785_);
lean_dec(v___x_4784_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4805_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
if (lean_obj_tag(v_a_4785_) == 1)
{
lean_object* v_val_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; uint8_t v___x_4793_; 
v_val_4789_ = lean_ctor_get(v_a_4785_, 0);
lean_inc_n(v_val_4789_, 2);
lean_dec_ref_known(v_a_4785_, 1);
lean_inc(v_val_4781_);
v___x_4790_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4790_, 0, v_val_4781_);
lean_ctor_set(v___x_4790_, 1, v_val_4789_);
v___x_4791_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4790_);
v___x_4792_ = lean_box(0);
v___x_4793_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4791_, v___x_4792_);
if (v___x_4793_ == 0)
{
lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; 
lean_del_object(v___x_4787_);
v___x_4794_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4794_, 0, v_a_4759_);
lean_ctor_set(v___x_4794_, 1, v_b_4760_);
lean_ctor_set(v___x_4794_, 2, v_val_4781_);
lean_ctor_set(v___x_4794_, 3, v_val_4789_);
v___x_4795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4795_, 0, v___x_4791_);
lean_ctor_set(v___x_4795_, 1, v___x_4794_);
v___x_4796_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_4795_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_);
return v___x_4796_;
}
else
{
lean_object* v___x_4797_; lean_object* v___x_4799_; 
lean_dec(v___x_4791_);
lean_dec(v_val_4789_);
lean_dec(v_val_4781_);
lean_dec_ref(v_b_4760_);
lean_dec_ref(v_a_4759_);
v___x_4797_ = lean_box(0);
if (v_isShared_4788_ == 0)
{
lean_ctor_set(v___x_4787_, 0, v___x_4797_);
v___x_4799_ = v___x_4787_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v___x_4797_);
v___x_4799_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
return v___x_4799_;
}
}
}
else
{
lean_object* v___x_4801_; lean_object* v___x_4803_; 
lean_dec(v_a_4785_);
lean_dec(v_val_4781_);
lean_dec_ref(v_b_4760_);
lean_dec_ref(v_a_4759_);
v___x_4801_ = lean_box(0);
if (v_isShared_4788_ == 0)
{
lean_ctor_set(v___x_4787_, 0, v___x_4801_);
v___x_4803_ = v___x_4787_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v___x_4801_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
}
else
{
lean_object* v_a_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4813_; 
lean_dec(v_val_4781_);
lean_dec_ref(v_b_4760_);
lean_dec_ref(v_a_4759_);
v_a_4806_ = lean_ctor_get(v___x_4784_, 0);
v_isSharedCheck_4813_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4813_ == 0)
{
v___x_4808_ = v___x_4784_;
v_isShared_4809_ = v_isSharedCheck_4813_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_a_4806_);
lean_dec(v___x_4784_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4813_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v___x_4811_; 
if (v_isShared_4809_ == 0)
{
v___x_4811_ = v___x_4808_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v_a_4806_);
v___x_4811_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
return v___x_4811_;
}
}
}
}
else
{
lean_object* v_a_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4821_; 
lean_dec(v_val_4781_);
lean_dec_ref(v_b_4760_);
lean_dec_ref(v_a_4759_);
v_a_4814_ = lean_ctor_get(v___x_4782_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4782_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4816_ = v___x_4782_;
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_a_4814_);
lean_dec(v___x_4782_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v___x_4819_; 
if (v_isShared_4817_ == 0)
{
v___x_4819_ = v___x_4816_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_a_4814_);
v___x_4819_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
return v___x_4819_;
}
}
}
}
else
{
lean_object* v___x_4822_; lean_object* v___x_4824_; 
lean_dec(v_a_4777_);
lean_dec_ref(v_b_4760_);
lean_dec_ref(v_a_4759_);
v___x_4822_ = lean_box(0);
if (v_isShared_4780_ == 0)
{
lean_ctor_set(v___x_4779_, 0, v___x_4822_);
v___x_4824_ = v___x_4779_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v___x_4822_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
}
else
{
lean_object* v_a_4827_; lean_object* v___x_4829_; uint8_t v_isShared_4830_; uint8_t v_isSharedCheck_4834_; 
lean_dec_ref(v_b_4760_);
lean_dec_ref(v_a_4759_);
v_a_4827_ = lean_ctor_get(v___x_4776_, 0);
v_isSharedCheck_4834_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4834_ == 0)
{
v___x_4829_ = v___x_4776_;
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
else
{
lean_inc(v_a_4827_);
lean_dec(v___x_4776_);
v___x_4829_ = lean_box(0);
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
v_resetjp_4828_:
{
lean_object* v___x_4832_; 
if (v_isShared_4830_ == 0)
{
v___x_4832_ = v___x_4829_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_a_4827_);
v___x_4832_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
return v___x_4832_;
}
}
}
}
else
{
lean_object* v_a_4835_; lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4842_; 
lean_dec_ref(v_b_4760_);
lean_dec_ref(v_a_4759_);
v_a_4835_ = lean_ctor_get(v___x_4773_, 0);
v_isSharedCheck_4842_ = !lean_is_exclusive(v___x_4773_);
if (v_isSharedCheck_4842_ == 0)
{
v___x_4837_ = v___x_4773_;
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
else
{
lean_inc(v_a_4835_);
lean_dec(v___x_4773_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v___x_4840_; 
if (v_isShared_4838_ == 0)
{
v___x_4840_ = v___x_4837_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_a_4835_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___boxed(lean_object* v_a_4843_, lean_object* v_b_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_){
_start:
{
lean_object* v_res_4857_; 
v_res_4857_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_4843_, v_b_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_);
lean_dec(v_a_4855_);
lean_dec_ref(v_a_4854_);
lean_dec(v_a_4853_);
lean_dec_ref(v_a_4852_);
lean_dec(v_a_4851_);
lean_dec_ref(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec_ref(v_a_4848_);
lean_dec(v_a_4847_);
lean_dec(v_a_4846_);
lean_dec(v_a_4845_);
return v_res_4857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(lean_object* v_a_4858_, lean_object* v_b_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_){
_start:
{
lean_object* v___x_4872_; 
v___x_4872_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_);
if (lean_obj_tag(v___x_4872_) == 0)
{
lean_object* v_a_4873_; lean_object* v___x_4874_; 
v_a_4873_ = lean_ctor_get(v___x_4872_, 0);
lean_inc(v_a_4873_);
lean_dec_ref_known(v___x_4872_, 1);
lean_inc_ref(v_a_4858_);
v___x_4874_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_4858_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_);
if (lean_obj_tag(v___x_4874_) == 0)
{
lean_object* v_a_4875_; lean_object* v_fst_4876_; lean_object* v___x_4877_; 
v_a_4875_ = lean_ctor_get(v___x_4874_, 0);
lean_inc(v_a_4875_);
lean_dec_ref_known(v___x_4874_, 1);
v_fst_4876_ = lean_ctor_get(v_a_4875_, 0);
lean_inc(v_fst_4876_);
lean_dec(v_a_4875_);
lean_inc_ref(v_b_4859_);
v___x_4877_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_);
if (lean_obj_tag(v___x_4877_) == 0)
{
lean_object* v_a_4878_; lean_object* v_fst_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4962_; 
v_a_4878_ = lean_ctor_get(v___x_4877_, 0);
lean_inc(v_a_4878_);
lean_dec_ref_known(v___x_4877_, 1);
v_fst_4879_ = lean_ctor_get(v_a_4878_, 0);
v_isSharedCheck_4962_ = !lean_is_exclusive(v_a_4878_);
if (v_isSharedCheck_4962_ == 0)
{
lean_object* v_unused_4963_; 
v_unused_4963_ = lean_ctor_get(v_a_4878_, 1);
lean_dec(v_unused_4963_);
v___x_4881_ = v_a_4878_;
v_isShared_4882_ = v_isSharedCheck_4962_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_fst_4879_);
lean_dec(v_a_4878_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4962_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v_id_4883_; lean_object* v_structId_4884_; lean_object* v___x_4885_; 
v_id_4883_ = lean_ctor_get(v_a_4873_, 0);
lean_inc(v_id_4883_);
v_structId_4884_ = lean_ctor_get(v_a_4873_, 1);
lean_inc(v_structId_4884_);
lean_dec(v_a_4873_);
v___x_4885_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4858_, v_a_4861_);
if (lean_obj_tag(v___x_4885_) == 0)
{
lean_object* v_a_4886_; uint8_t v___x_4887_; lean_object* v___x_4888_; 
v_a_4886_ = lean_ctor_get(v___x_4885_, 0);
lean_inc(v_a_4886_);
lean_dec_ref_known(v___x_4885_, 1);
v___x_4887_ = 0;
v___x_4888_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4876_, v___x_4887_, v_a_4886_, v_structId_4884_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_);
if (lean_obj_tag(v___x_4888_) == 0)
{
lean_object* v_a_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4945_; 
v_a_4889_ = lean_ctor_get(v___x_4888_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4891_ = v___x_4888_;
v_isShared_4892_ = v_isSharedCheck_4945_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_a_4889_);
lean_dec(v___x_4888_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4945_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
if (lean_obj_tag(v_a_4889_) == 1)
{
lean_object* v_val_4893_; lean_object* v___x_4894_; 
lean_del_object(v___x_4891_);
v_val_4893_ = lean_ctor_get(v_a_4889_, 0);
lean_inc(v_val_4893_);
lean_dec_ref_known(v_a_4889_, 1);
v___x_4894_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4859_, v_a_4861_);
if (lean_obj_tag(v___x_4894_) == 0)
{
lean_object* v_a_4895_; lean_object* v___x_4896_; 
v_a_4895_ = lean_ctor_get(v___x_4894_, 0);
lean_inc(v_a_4895_);
lean_dec_ref_known(v___x_4894_, 1);
v___x_4896_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4879_, v___x_4887_, v_a_4895_, v_structId_4884_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_);
if (lean_obj_tag(v___x_4896_) == 0)
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4924_; 
v_a_4897_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4899_ = v___x_4896_;
v_isShared_4900_ = v_isSharedCheck_4924_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4896_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4924_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
if (lean_obj_tag(v_a_4897_) == 1)
{
lean_object* v_val_4901_; lean_object* v___x_4903_; 
v_val_4901_ = lean_ctor_get(v_a_4897_, 0);
lean_inc_n(v_val_4901_, 2);
lean_dec_ref_known(v_a_4897_, 1);
lean_inc(v_val_4893_);
if (v_isShared_4882_ == 0)
{
lean_ctor_set_tag(v___x_4881_, 3);
lean_ctor_set(v___x_4881_, 1, v_val_4901_);
lean_ctor_set(v___x_4881_, 0, v_val_4893_);
v___x_4903_ = v___x_4881_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_val_4893_);
lean_ctor_set(v_reuseFailAlloc_4919_, 1, v_val_4901_);
v___x_4903_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
lean_object* v___x_4904_; lean_object* v___x_4905_; uint8_t v___x_4906_; 
v___x_4904_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4903_);
v___x_4905_ = lean_box(0);
v___x_4906_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4904_, v___x_4905_);
if (v___x_4906_ == 0)
{
lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
lean_del_object(v___x_4899_);
lean_inc(v_val_4901_);
lean_inc(v_val_4893_);
lean_inc(v_id_4883_);
lean_inc_ref(v_b_4859_);
lean_inc_ref(v_a_4858_);
v___x_4907_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4907_, 0, v_a_4858_);
lean_ctor_set(v___x_4907_, 1, v_b_4859_);
lean_ctor_set(v___x_4907_, 2, v_id_4883_);
lean_ctor_set(v___x_4907_, 3, v_val_4893_);
lean_ctor_set(v___x_4907_, 4, v_val_4901_);
lean_inc(v___x_4904_);
v___x_4908_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4908_, 0, v___x_4904_);
lean_ctor_set(v___x_4908_, 1, v___x_4907_);
lean_ctor_set_uint8(v___x_4908_, sizeof(void*)*2, v___x_4887_);
v___x_4909_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4908_, v_structId_4884_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; 
lean_dec_ref_known(v___x_4909_, 1);
v___x_4910_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4911_ = l_Lean_Grind_Linarith_Poly_mul(v___x_4904_, v___x_4910_);
v___x_4912_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4912_, 0, v_b_4859_);
lean_ctor_set(v___x_4912_, 1, v_a_4858_);
lean_ctor_set(v___x_4912_, 2, v_id_4883_);
lean_ctor_set(v___x_4912_, 3, v_val_4901_);
lean_ctor_set(v___x_4912_, 4, v_val_4893_);
v___x_4913_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4913_, 0, v___x_4911_);
lean_ctor_set(v___x_4913_, 1, v___x_4912_);
lean_ctor_set_uint8(v___x_4913_, sizeof(void*)*2, v___x_4887_);
v___x_4914_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4913_, v_structId_4884_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_);
lean_dec(v_structId_4884_);
return v___x_4914_;
}
else
{
lean_dec(v___x_4904_);
lean_dec(v_val_4901_);
lean_dec(v_val_4893_);
lean_dec(v_structId_4884_);
lean_dec(v_id_4883_);
lean_dec_ref(v_b_4859_);
lean_dec_ref(v_a_4858_);
return v___x_4909_;
}
}
else
{
lean_object* v___x_4915_; lean_object* v___x_4917_; 
lean_dec(v___x_4904_);
lean_dec(v_val_4901_);
lean_dec(v_val_4893_);
lean_dec(v_structId_4884_);
lean_dec(v_id_4883_);
lean_dec_ref(v_b_4859_);
lean_dec_ref(v_a_4858_);
v___x_4915_ = lean_box(0);
if (v_isShared_4900_ == 0)
{
lean_ctor_set(v___x_4899_, 0, v___x_4915_);
v___x_4917_ = v___x_4899_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4918_; 
v_reuseFailAlloc_4918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4918_, 0, v___x_4915_);
v___x_4917_ = v_reuseFailAlloc_4918_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
return v___x_4917_;
}
}
}
}
else
{
lean_object* v___x_4920_; lean_object* v___x_4922_; 
lean_dec(v_a_4897_);
lean_dec(v_val_4893_);
lean_dec(v_structId_4884_);
lean_dec(v_id_4883_);
lean_del_object(v___x_4881_);
lean_dec_ref(v_b_4859_);
lean_dec_ref(v_a_4858_);
v___x_4920_ = lean_box(0);
if (v_isShared_4900_ == 0)
{
lean_ctor_set(v___x_4899_, 0, v___x_4920_);
v___x_4922_ = v___x_4899_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v___x_4920_);
v___x_4922_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
return v___x_4922_;
}
}
}
}
else
{
lean_object* v_a_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4932_; 
lean_dec(v_val_4893_);
lean_dec(v_structId_4884_);
lean_dec(v_id_4883_);
lean_del_object(v___x_4881_);
lean_dec_ref(v_b_4859_);
lean_dec_ref(v_a_4858_);
v_a_4925_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4932_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4932_ == 0)
{
v___x_4927_ = v___x_4896_;
v_isShared_4928_ = v_isSharedCheck_4932_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_a_4925_);
lean_dec(v___x_4896_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4932_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v___x_4930_; 
if (v_isShared_4928_ == 0)
{
v___x_4930_ = v___x_4927_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_a_4925_);
v___x_4930_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
return v___x_4930_;
}
}
}
}
else
{
lean_object* v_a_4933_; lean_object* v___x_4935_; uint8_t v_isShared_4936_; uint8_t v_isSharedCheck_4940_; 
lean_dec(v_val_4893_);
lean_dec(v_structId_4884_);
lean_dec(v_id_4883_);
lean_del_object(v___x_4881_);
lean_dec(v_fst_4879_);
lean_dec_ref(v_b_4859_);
lean_dec_ref(v_a_4858_);
v_a_4933_ = lean_ctor_get(v___x_4894_, 0);
v_isSharedCheck_4940_ = !lean_is_exclusive(v___x_4894_);
if (v_isSharedCheck_4940_ == 0)
{
v___x_4935_ = v___x_4894_;
v_isShared_4936_ = v_isSharedCheck_4940_;
goto v_resetjp_4934_;
}
else
{
lean_inc(v_a_4933_);
lean_dec(v___x_4894_);
v___x_4935_ = lean_box(0);
v_isShared_4936_ = v_isSharedCheck_4940_;
goto v_resetjp_4934_;
}
v_resetjp_4934_:
{
lean_object* v___x_4938_; 
if (v_isShared_4936_ == 0)
{
v___x_4938_ = v___x_4935_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v_a_4933_);
v___x_4938_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
return v___x_4938_;
}
}
}
}
else
{
lean_object* v___x_4941_; lean_object* v___x_4943_; 
lean_dec(v_a_4889_);
lean_dec(v_structId_4884_);
lean_dec(v_id_4883_);
lean_del_object(v___x_4881_);
lean_dec(v_fst_4879_);
lean_dec_ref(v_b_4859_);
lean_dec_ref(v_a_4858_);
v___x_4941_ = lean_box(0);
if (v_isShared_4892_ == 0)
{
lean_ctor_set(v___x_4891_, 0, v___x_4941_);
v___x_4943_ = v___x_4891_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v___x_4941_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
return v___x_4943_;
}
}
}
}
else
{
lean_object* v_a_4946_; lean_object* v___x_4948_; uint8_t v_isShared_4949_; uint8_t v_isSharedCheck_4953_; 
lean_dec(v_structId_4884_);
lean_dec(v_id_4883_);
lean_del_object(v___x_4881_);
lean_dec(v_fst_4879_);
lean_dec_ref(v_b_4859_);
lean_dec_ref(v_a_4858_);
v_a_4946_ = lean_ctor_get(v___x_4888_, 0);
v_isSharedCheck_4953_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4953_ == 0)
{
v___x_4948_ = v___x_4888_;
v_isShared_4949_ = v_isSharedCheck_4953_;
goto v_resetjp_4947_;
}
else
{
lean_inc(v_a_4946_);
lean_dec(v___x_4888_);
v___x_4948_ = lean_box(0);
v_isShared_4949_ = v_isSharedCheck_4953_;
goto v_resetjp_4947_;
}
v_resetjp_4947_:
{
lean_object* v___x_4951_; 
if (v_isShared_4949_ == 0)
{
v___x_4951_ = v___x_4948_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v_a_4946_);
v___x_4951_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
return v___x_4951_;
}
}
}
}
else
{
lean_object* v_a_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_4961_; 
lean_dec(v_structId_4884_);
lean_dec(v_id_4883_);
lean_del_object(v___x_4881_);
lean_dec(v_fst_4879_);
lean_dec(v_fst_4876_);
lean_dec_ref(v_b_4859_);
lean_dec_ref(v_a_4858_);
v_a_4954_ = lean_ctor_get(v___x_4885_, 0);
v_isSharedCheck_4961_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4961_ == 0)
{
v___x_4956_ = v___x_4885_;
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_a_4954_);
lean_dec(v___x_4885_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v___x_4959_; 
if (v_isShared_4957_ == 0)
{
v___x_4959_ = v___x_4956_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v_a_4954_);
v___x_4959_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
return v___x_4959_;
}
}
}
}
}
else
{
lean_object* v_a_4964_; lean_object* v___x_4966_; uint8_t v_isShared_4967_; uint8_t v_isSharedCheck_4971_; 
lean_dec(v_fst_4876_);
lean_dec(v_a_4873_);
lean_dec_ref(v_b_4859_);
lean_dec_ref(v_a_4858_);
v_a_4964_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_4971_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4971_ == 0)
{
v___x_4966_ = v___x_4877_;
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
else
{
lean_inc(v_a_4964_);
lean_dec(v___x_4877_);
v___x_4966_ = lean_box(0);
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
v_resetjp_4965_:
{
lean_object* v___x_4969_; 
if (v_isShared_4967_ == 0)
{
v___x_4969_ = v___x_4966_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v_a_4964_);
v___x_4969_ = v_reuseFailAlloc_4970_;
goto v_reusejp_4968_;
}
v_reusejp_4968_:
{
return v___x_4969_;
}
}
}
}
else
{
lean_object* v_a_4972_; lean_object* v___x_4974_; uint8_t v_isShared_4975_; uint8_t v_isSharedCheck_4979_; 
lean_dec(v_a_4873_);
lean_dec_ref(v_b_4859_);
lean_dec_ref(v_a_4858_);
v_a_4972_ = lean_ctor_get(v___x_4874_, 0);
v_isSharedCheck_4979_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_4979_ == 0)
{
v___x_4974_ = v___x_4874_;
v_isShared_4975_ = v_isSharedCheck_4979_;
goto v_resetjp_4973_;
}
else
{
lean_inc(v_a_4972_);
lean_dec(v___x_4874_);
v___x_4974_ = lean_box(0);
v_isShared_4975_ = v_isSharedCheck_4979_;
goto v_resetjp_4973_;
}
v_resetjp_4973_:
{
lean_object* v___x_4977_; 
if (v_isShared_4975_ == 0)
{
v___x_4977_ = v___x_4974_;
goto v_reusejp_4976_;
}
else
{
lean_object* v_reuseFailAlloc_4978_; 
v_reuseFailAlloc_4978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4978_, 0, v_a_4972_);
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
lean_object* v_a_4980_; lean_object* v___x_4982_; uint8_t v_isShared_4983_; uint8_t v_isSharedCheck_4987_; 
lean_dec_ref(v_b_4859_);
lean_dec_ref(v_a_4858_);
v_a_4980_ = lean_ctor_get(v___x_4872_, 0);
v_isSharedCheck_4987_ = !lean_is_exclusive(v___x_4872_);
if (v_isSharedCheck_4987_ == 0)
{
v___x_4982_ = v___x_4872_;
v_isShared_4983_ = v_isSharedCheck_4987_;
goto v_resetjp_4981_;
}
else
{
lean_inc(v_a_4980_);
lean_dec(v___x_4872_);
v___x_4982_ = lean_box(0);
v_isShared_4983_ = v_isSharedCheck_4987_;
goto v_resetjp_4981_;
}
v_resetjp_4981_:
{
lean_object* v___x_4985_; 
if (v_isShared_4983_ == 0)
{
v___x_4985_ = v___x_4982_;
goto v_reusejp_4984_;
}
else
{
lean_object* v_reuseFailAlloc_4986_; 
v_reuseFailAlloc_4986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4986_, 0, v_a_4980_);
v___x_4985_ = v_reuseFailAlloc_4986_;
goto v_reusejp_4984_;
}
v_reusejp_4984_:
{
return v___x_4985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27___boxed(lean_object* v_a_4988_, lean_object* v_b_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_){
_start:
{
lean_object* v_res_5002_; 
v_res_5002_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_4988_, v_b_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
lean_dec(v_a_5000_);
lean_dec_ref(v_a_4999_);
lean_dec(v_a_4998_);
lean_dec_ref(v_a_4997_);
lean_dec(v_a_4996_);
lean_dec_ref(v_a_4995_);
lean_dec(v_a_4994_);
lean_dec_ref(v_a_4993_);
lean_dec(v_a_4992_);
lean_dec(v_a_4991_);
lean_dec(v_a_4990_);
return v_res_5002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(lean_object* v_a_5003_, lean_object* v_b_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_){
_start:
{
lean_object* v___x_5017_; 
v___x_5017_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_);
if (lean_obj_tag(v___x_5017_) == 0)
{
lean_object* v_a_5018_; lean_object* v___x_5019_; 
v_a_5018_ = lean_ctor_get(v___x_5017_, 0);
lean_inc(v_a_5018_);
lean_dec_ref_known(v___x_5017_, 1);
lean_inc_ref(v_a_5003_);
v___x_5019_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5003_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_);
if (lean_obj_tag(v___x_5019_) == 0)
{
lean_object* v_a_5020_; lean_object* v_fst_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5117_; 
v_a_5020_ = lean_ctor_get(v___x_5019_, 0);
lean_inc(v_a_5020_);
lean_dec_ref_known(v___x_5019_, 1);
v_fst_5021_ = lean_ctor_get(v_a_5020_, 0);
v_isSharedCheck_5117_ = !lean_is_exclusive(v_a_5020_);
if (v_isSharedCheck_5117_ == 0)
{
lean_object* v_unused_5118_; 
v_unused_5118_ = lean_ctor_get(v_a_5020_, 1);
lean_dec(v_unused_5118_);
v___x_5023_ = v_a_5020_;
v_isShared_5024_ = v_isSharedCheck_5117_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_fst_5021_);
lean_dec(v_a_5020_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5117_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
lean_object* v___x_5025_; 
lean_inc_ref(v_b_5004_);
v___x_5025_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_);
if (lean_obj_tag(v___x_5025_) == 0)
{
lean_object* v_a_5026_; lean_object* v_fst_5027_; lean_object* v___x_5029_; uint8_t v_isShared_5030_; uint8_t v_isSharedCheck_5107_; 
v_a_5026_ = lean_ctor_get(v___x_5025_, 0);
lean_inc(v_a_5026_);
lean_dec_ref_known(v___x_5025_, 1);
v_fst_5027_ = lean_ctor_get(v_a_5026_, 0);
v_isSharedCheck_5107_ = !lean_is_exclusive(v_a_5026_);
if (v_isSharedCheck_5107_ == 0)
{
lean_object* v_unused_5108_; 
v_unused_5108_ = lean_ctor_get(v_a_5026_, 1);
lean_dec(v_unused_5108_);
v___x_5029_ = v_a_5026_;
v_isShared_5030_ = v_isSharedCheck_5107_;
goto v_resetjp_5028_;
}
else
{
lean_inc(v_fst_5027_);
lean_dec(v_a_5026_);
v___x_5029_ = lean_box(0);
v_isShared_5030_ = v_isSharedCheck_5107_;
goto v_resetjp_5028_;
}
v_resetjp_5028_:
{
lean_object* v_id_5031_; lean_object* v_structId_5032_; lean_object* v___x_5033_; 
v_id_5031_ = lean_ctor_get(v_a_5018_, 0);
lean_inc(v_id_5031_);
v_structId_5032_ = lean_ctor_get(v_a_5018_, 1);
lean_inc(v_structId_5032_);
lean_dec(v_a_5018_);
v___x_5033_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5003_, v_a_5006_);
if (lean_obj_tag(v___x_5033_) == 0)
{
lean_object* v_a_5034_; uint8_t v___x_5035_; lean_object* v___x_5036_; 
v_a_5034_ = lean_ctor_get(v___x_5033_, 0);
lean_inc(v_a_5034_);
lean_dec_ref_known(v___x_5033_, 1);
v___x_5035_ = 0;
v___x_5036_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5021_, v___x_5035_, v_a_5034_, v_structId_5032_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_);
if (lean_obj_tag(v___x_5036_) == 0)
{
lean_object* v_a_5037_; lean_object* v___x_5039_; uint8_t v_isShared_5040_; uint8_t v_isSharedCheck_5090_; 
v_a_5037_ = lean_ctor_get(v___x_5036_, 0);
v_isSharedCheck_5090_ = !lean_is_exclusive(v___x_5036_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5039_ = v___x_5036_;
v_isShared_5040_ = v_isSharedCheck_5090_;
goto v_resetjp_5038_;
}
else
{
lean_inc(v_a_5037_);
lean_dec(v___x_5036_);
v___x_5039_ = lean_box(0);
v_isShared_5040_ = v_isSharedCheck_5090_;
goto v_resetjp_5038_;
}
v_resetjp_5038_:
{
if (lean_obj_tag(v_a_5037_) == 1)
{
lean_object* v_val_5041_; lean_object* v___x_5042_; 
lean_del_object(v___x_5039_);
v_val_5041_ = lean_ctor_get(v_a_5037_, 0);
lean_inc(v_val_5041_);
lean_dec_ref_known(v_a_5037_, 1);
v___x_5042_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5004_, v_a_5006_);
if (lean_obj_tag(v___x_5042_) == 0)
{
lean_object* v_a_5043_; lean_object* v___x_5044_; 
v_a_5043_ = lean_ctor_get(v___x_5042_, 0);
lean_inc(v_a_5043_);
lean_dec_ref_known(v___x_5042_, 1);
v___x_5044_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5027_, v___x_5035_, v_a_5043_, v_structId_5032_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_);
if (lean_obj_tag(v___x_5044_) == 0)
{
lean_object* v_a_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5069_; 
v_a_5045_ = lean_ctor_get(v___x_5044_, 0);
v_isSharedCheck_5069_ = !lean_is_exclusive(v___x_5044_);
if (v_isSharedCheck_5069_ == 0)
{
v___x_5047_ = v___x_5044_;
v_isShared_5048_ = v_isSharedCheck_5069_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_a_5045_);
lean_dec(v___x_5044_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5069_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
if (lean_obj_tag(v_a_5045_) == 1)
{
lean_object* v_val_5049_; lean_object* v___x_5051_; 
v_val_5049_ = lean_ctor_get(v_a_5045_, 0);
lean_inc_n(v_val_5049_, 2);
lean_dec_ref_known(v_a_5045_, 1);
lean_inc(v_val_5041_);
if (v_isShared_5030_ == 0)
{
lean_ctor_set_tag(v___x_5029_, 3);
lean_ctor_set(v___x_5029_, 1, v_val_5049_);
lean_ctor_set(v___x_5029_, 0, v_val_5041_);
v___x_5051_ = v___x_5029_;
goto v_reusejp_5050_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v_val_5041_);
lean_ctor_set(v_reuseFailAlloc_5064_, 1, v_val_5049_);
v___x_5051_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5050_;
}
v_reusejp_5050_:
{
lean_object* v___x_5052_; lean_object* v___x_5053_; uint8_t v___x_5054_; 
v___x_5052_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5051_);
v___x_5053_ = lean_box(0);
v___x_5054_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_5052_, v___x_5053_);
if (v___x_5054_ == 0)
{
lean_object* v___x_5055_; lean_object* v___x_5057_; 
lean_del_object(v___x_5047_);
v___x_5055_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5055_, 0, v_a_5003_);
lean_ctor_set(v___x_5055_, 1, v_b_5004_);
lean_ctor_set(v___x_5055_, 2, v_id_5031_);
lean_ctor_set(v___x_5055_, 3, v_val_5041_);
lean_ctor_set(v___x_5055_, 4, v_val_5049_);
if (v_isShared_5024_ == 0)
{
lean_ctor_set(v___x_5023_, 1, v___x_5055_);
lean_ctor_set(v___x_5023_, 0, v___x_5052_);
v___x_5057_ = v___x_5023_;
goto v_reusejp_5056_;
}
else
{
lean_object* v_reuseFailAlloc_5059_; 
v_reuseFailAlloc_5059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5059_, 0, v___x_5052_);
lean_ctor_set(v_reuseFailAlloc_5059_, 1, v___x_5055_);
v___x_5057_ = v_reuseFailAlloc_5059_;
goto v_reusejp_5056_;
}
v_reusejp_5056_:
{
lean_object* v___x_5058_; 
v___x_5058_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_5057_, v_structId_5032_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_);
lean_dec(v_structId_5032_);
return v___x_5058_;
}
}
else
{
lean_object* v___x_5060_; lean_object* v___x_5062_; 
lean_dec(v___x_5052_);
lean_dec(v_val_5049_);
lean_dec(v_val_5041_);
lean_dec(v_structId_5032_);
lean_dec(v_id_5031_);
lean_del_object(v___x_5023_);
lean_dec_ref(v_b_5004_);
lean_dec_ref(v_a_5003_);
v___x_5060_ = lean_box(0);
if (v_isShared_5048_ == 0)
{
lean_ctor_set(v___x_5047_, 0, v___x_5060_);
v___x_5062_ = v___x_5047_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v___x_5060_);
v___x_5062_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
return v___x_5062_;
}
}
}
}
else
{
lean_object* v___x_5065_; lean_object* v___x_5067_; 
lean_dec(v_a_5045_);
lean_dec(v_val_5041_);
lean_dec(v_structId_5032_);
lean_dec(v_id_5031_);
lean_del_object(v___x_5029_);
lean_del_object(v___x_5023_);
lean_dec_ref(v_b_5004_);
lean_dec_ref(v_a_5003_);
v___x_5065_ = lean_box(0);
if (v_isShared_5048_ == 0)
{
lean_ctor_set(v___x_5047_, 0, v___x_5065_);
v___x_5067_ = v___x_5047_;
goto v_reusejp_5066_;
}
else
{
lean_object* v_reuseFailAlloc_5068_; 
v_reuseFailAlloc_5068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5068_, 0, v___x_5065_);
v___x_5067_ = v_reuseFailAlloc_5068_;
goto v_reusejp_5066_;
}
v_reusejp_5066_:
{
return v___x_5067_;
}
}
}
}
else
{
lean_object* v_a_5070_; lean_object* v___x_5072_; uint8_t v_isShared_5073_; uint8_t v_isSharedCheck_5077_; 
lean_dec(v_val_5041_);
lean_dec(v_structId_5032_);
lean_dec(v_id_5031_);
lean_del_object(v___x_5029_);
lean_del_object(v___x_5023_);
lean_dec_ref(v_b_5004_);
lean_dec_ref(v_a_5003_);
v_a_5070_ = lean_ctor_get(v___x_5044_, 0);
v_isSharedCheck_5077_ = !lean_is_exclusive(v___x_5044_);
if (v_isSharedCheck_5077_ == 0)
{
v___x_5072_ = v___x_5044_;
v_isShared_5073_ = v_isSharedCheck_5077_;
goto v_resetjp_5071_;
}
else
{
lean_inc(v_a_5070_);
lean_dec(v___x_5044_);
v___x_5072_ = lean_box(0);
v_isShared_5073_ = v_isSharedCheck_5077_;
goto v_resetjp_5071_;
}
v_resetjp_5071_:
{
lean_object* v___x_5075_; 
if (v_isShared_5073_ == 0)
{
v___x_5075_ = v___x_5072_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v_a_5070_);
v___x_5075_ = v_reuseFailAlloc_5076_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
return v___x_5075_;
}
}
}
}
else
{
lean_object* v_a_5078_; lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5085_; 
lean_dec(v_val_5041_);
lean_dec(v_structId_5032_);
lean_dec(v_id_5031_);
lean_del_object(v___x_5029_);
lean_dec(v_fst_5027_);
lean_del_object(v___x_5023_);
lean_dec_ref(v_b_5004_);
lean_dec_ref(v_a_5003_);
v_a_5078_ = lean_ctor_get(v___x_5042_, 0);
v_isSharedCheck_5085_ = !lean_is_exclusive(v___x_5042_);
if (v_isSharedCheck_5085_ == 0)
{
v___x_5080_ = v___x_5042_;
v_isShared_5081_ = v_isSharedCheck_5085_;
goto v_resetjp_5079_;
}
else
{
lean_inc(v_a_5078_);
lean_dec(v___x_5042_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5085_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
lean_object* v___x_5083_; 
if (v_isShared_5081_ == 0)
{
v___x_5083_ = v___x_5080_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v_a_5078_);
v___x_5083_ = v_reuseFailAlloc_5084_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
return v___x_5083_;
}
}
}
}
else
{
lean_object* v___x_5086_; lean_object* v___x_5088_; 
lean_dec(v_a_5037_);
lean_dec(v_structId_5032_);
lean_dec(v_id_5031_);
lean_del_object(v___x_5029_);
lean_dec(v_fst_5027_);
lean_del_object(v___x_5023_);
lean_dec_ref(v_b_5004_);
lean_dec_ref(v_a_5003_);
v___x_5086_ = lean_box(0);
if (v_isShared_5040_ == 0)
{
lean_ctor_set(v___x_5039_, 0, v___x_5086_);
v___x_5088_ = v___x_5039_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v___x_5086_);
v___x_5088_ = v_reuseFailAlloc_5089_;
goto v_reusejp_5087_;
}
v_reusejp_5087_:
{
return v___x_5088_;
}
}
}
}
else
{
lean_object* v_a_5091_; lean_object* v___x_5093_; uint8_t v_isShared_5094_; uint8_t v_isSharedCheck_5098_; 
lean_dec(v_structId_5032_);
lean_dec(v_id_5031_);
lean_del_object(v___x_5029_);
lean_dec(v_fst_5027_);
lean_del_object(v___x_5023_);
lean_dec_ref(v_b_5004_);
lean_dec_ref(v_a_5003_);
v_a_5091_ = lean_ctor_get(v___x_5036_, 0);
v_isSharedCheck_5098_ = !lean_is_exclusive(v___x_5036_);
if (v_isSharedCheck_5098_ == 0)
{
v___x_5093_ = v___x_5036_;
v_isShared_5094_ = v_isSharedCheck_5098_;
goto v_resetjp_5092_;
}
else
{
lean_inc(v_a_5091_);
lean_dec(v___x_5036_);
v___x_5093_ = lean_box(0);
v_isShared_5094_ = v_isSharedCheck_5098_;
goto v_resetjp_5092_;
}
v_resetjp_5092_:
{
lean_object* v___x_5096_; 
if (v_isShared_5094_ == 0)
{
v___x_5096_ = v___x_5093_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5097_; 
v_reuseFailAlloc_5097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5097_, 0, v_a_5091_);
v___x_5096_ = v_reuseFailAlloc_5097_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
return v___x_5096_;
}
}
}
}
else
{
lean_object* v_a_5099_; lean_object* v___x_5101_; uint8_t v_isShared_5102_; uint8_t v_isSharedCheck_5106_; 
lean_dec(v_structId_5032_);
lean_dec(v_id_5031_);
lean_del_object(v___x_5029_);
lean_dec(v_fst_5027_);
lean_del_object(v___x_5023_);
lean_dec(v_fst_5021_);
lean_dec_ref(v_b_5004_);
lean_dec_ref(v_a_5003_);
v_a_5099_ = lean_ctor_get(v___x_5033_, 0);
v_isSharedCheck_5106_ = !lean_is_exclusive(v___x_5033_);
if (v_isSharedCheck_5106_ == 0)
{
v___x_5101_ = v___x_5033_;
v_isShared_5102_ = v_isSharedCheck_5106_;
goto v_resetjp_5100_;
}
else
{
lean_inc(v_a_5099_);
lean_dec(v___x_5033_);
v___x_5101_ = lean_box(0);
v_isShared_5102_ = v_isSharedCheck_5106_;
goto v_resetjp_5100_;
}
v_resetjp_5100_:
{
lean_object* v___x_5104_; 
if (v_isShared_5102_ == 0)
{
v___x_5104_ = v___x_5101_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_a_5099_);
v___x_5104_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
return v___x_5104_;
}
}
}
}
}
else
{
lean_object* v_a_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5116_; 
lean_del_object(v___x_5023_);
lean_dec(v_fst_5021_);
lean_dec(v_a_5018_);
lean_dec_ref(v_b_5004_);
lean_dec_ref(v_a_5003_);
v_a_5109_ = lean_ctor_get(v___x_5025_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v___x_5025_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5111_ = v___x_5025_;
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_a_5109_);
lean_dec(v___x_5025_);
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
lean_object* v_a_5119_; lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5126_; 
lean_dec(v_a_5018_);
lean_dec_ref(v_b_5004_);
lean_dec_ref(v_a_5003_);
v_a_5119_ = lean_ctor_get(v___x_5019_, 0);
v_isSharedCheck_5126_ = !lean_is_exclusive(v___x_5019_);
if (v_isSharedCheck_5126_ == 0)
{
v___x_5121_ = v___x_5019_;
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
else
{
lean_inc(v_a_5119_);
lean_dec(v___x_5019_);
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
lean_object* v_a_5127_; lean_object* v___x_5129_; uint8_t v_isShared_5130_; uint8_t v_isSharedCheck_5134_; 
lean_dec_ref(v_b_5004_);
lean_dec_ref(v_a_5003_);
v_a_5127_ = lean_ctor_get(v___x_5017_, 0);
v_isSharedCheck_5134_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5134_ == 0)
{
v___x_5129_ = v___x_5017_;
v_isShared_5130_ = v_isSharedCheck_5134_;
goto v_resetjp_5128_;
}
else
{
lean_inc(v_a_5127_);
lean_dec(v___x_5017_);
v___x_5129_ = lean_box(0);
v_isShared_5130_ = v_isSharedCheck_5134_;
goto v_resetjp_5128_;
}
v_resetjp_5128_:
{
lean_object* v___x_5132_; 
if (v_isShared_5130_ == 0)
{
v___x_5132_ = v___x_5129_;
goto v_reusejp_5131_;
}
else
{
lean_object* v_reuseFailAlloc_5133_; 
v_reuseFailAlloc_5133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5133_, 0, v_a_5127_);
v___x_5132_ = v_reuseFailAlloc_5133_;
goto v_reusejp_5131_;
}
v_reusejp_5131_:
{
return v___x_5132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq___boxed(lean_object* v_a_5135_, lean_object* v_b_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_){
_start:
{
lean_object* v_res_5149_; 
v_res_5149_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5135_, v_b_5136_, v_a_5137_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_, v_a_5142_, v_a_5143_, v_a_5144_, v_a_5145_, v_a_5146_, v_a_5147_);
lean_dec(v_a_5147_);
lean_dec_ref(v_a_5146_);
lean_dec(v_a_5145_);
lean_dec_ref(v_a_5144_);
lean_dec(v_a_5143_);
lean_dec_ref(v_a_5142_);
lean_dec(v_a_5141_);
lean_dec_ref(v_a_5140_);
lean_dec(v_a_5139_);
lean_dec(v_a_5138_);
lean_dec(v_a_5137_);
return v_res_5149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq(lean_object* v_a_5150_, lean_object* v_b_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_){
_start:
{
size_t v___x_5163_; size_t v___x_5164_; uint8_t v___x_5165_; 
v___x_5163_ = lean_ptr_addr(v_a_5150_);
v___x_5164_ = lean_ptr_addr(v_b_5151_);
v___x_5165_ = lean_usize_dec_eq(v___x_5163_, v___x_5164_);
if (v___x_5165_ == 0)
{
lean_object* v___x_5166_; 
v___x_5166_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5150_, v_b_5151_, v_a_5152_, v_a_5160_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v_a_5167_; 
v_a_5167_ = lean_ctor_get(v___x_5166_, 0);
lean_inc(v_a_5167_);
lean_dec_ref_known(v___x_5166_, 1);
if (lean_obj_tag(v_a_5167_) == 1)
{
lean_object* v_val_5168_; lean_object* v___x_5169_; 
v_val_5168_ = lean_ctor_get(v_a_5167_, 0);
lean_inc(v_val_5168_);
lean_dec_ref_known(v_a_5167_, 1);
v___x_5169_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_val_5168_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_);
if (lean_obj_tag(v___x_5169_) == 0)
{
lean_object* v_a_5170_; uint8_t v___x_5171_; 
v_a_5170_ = lean_ctor_get(v___x_5169_, 0);
lean_inc(v_a_5170_);
lean_dec_ref_known(v___x_5169_, 1);
v___x_5171_ = lean_unbox(v_a_5170_);
lean_dec(v_a_5170_);
if (v___x_5171_ == 0)
{
lean_object* v___x_5172_; 
v___x_5172_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5168_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_);
if (lean_obj_tag(v___x_5172_) == 0)
{
lean_object* v_a_5173_; uint8_t v___x_5174_; 
v_a_5173_ = lean_ctor_get(v___x_5172_, 0);
lean_inc(v_a_5173_);
lean_dec_ref_known(v___x_5172_, 1);
v___x_5174_ = lean_unbox(v_a_5173_);
lean_dec(v_a_5173_);
if (v___x_5174_ == 0)
{
lean_object* v___x_5175_; 
v___x_5175_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_5150_, v_b_5151_, v_val_5168_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_);
lean_dec(v_val_5168_);
return v___x_5175_;
}
else
{
lean_object* v___x_5176_; 
lean_dec(v_val_5168_);
v___x_5176_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_5150_, v_b_5151_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_);
return v___x_5176_;
}
}
else
{
lean_object* v_a_5177_; lean_object* v___x_5179_; uint8_t v_isShared_5180_; uint8_t v_isSharedCheck_5184_; 
lean_dec(v_val_5168_);
lean_dec_ref(v_b_5151_);
lean_dec_ref(v_a_5150_);
v_a_5177_ = lean_ctor_get(v___x_5172_, 0);
v_isSharedCheck_5184_ = !lean_is_exclusive(v___x_5172_);
if (v_isSharedCheck_5184_ == 0)
{
v___x_5179_ = v___x_5172_;
v_isShared_5180_ = v_isSharedCheck_5184_;
goto v_resetjp_5178_;
}
else
{
lean_inc(v_a_5177_);
lean_dec(v___x_5172_);
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
lean_object* v___x_5185_; 
v___x_5185_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5168_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_);
if (lean_obj_tag(v___x_5185_) == 0)
{
lean_object* v_a_5186_; uint8_t v___x_5187_; 
v_a_5186_ = lean_ctor_get(v___x_5185_, 0);
lean_inc(v_a_5186_);
lean_dec_ref_known(v___x_5185_, 1);
v___x_5187_ = lean_unbox(v_a_5186_);
lean_dec(v_a_5186_);
if (v___x_5187_ == 0)
{
lean_object* v___x_5188_; 
v___x_5188_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_5150_, v_b_5151_, v_val_5168_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_);
lean_dec(v_val_5168_);
return v___x_5188_;
}
else
{
lean_object* v___x_5189_; 
v___x_5189_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_5150_, v_b_5151_, v_val_5168_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_);
lean_dec(v_val_5168_);
return v___x_5189_;
}
}
else
{
lean_object* v_a_5190_; lean_object* v___x_5192_; uint8_t v_isShared_5193_; uint8_t v_isSharedCheck_5197_; 
lean_dec(v_val_5168_);
lean_dec_ref(v_b_5151_);
lean_dec_ref(v_a_5150_);
v_a_5190_ = lean_ctor_get(v___x_5185_, 0);
v_isSharedCheck_5197_ = !lean_is_exclusive(v___x_5185_);
if (v_isSharedCheck_5197_ == 0)
{
v___x_5192_ = v___x_5185_;
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
else
{
lean_inc(v_a_5190_);
lean_dec(v___x_5185_);
v___x_5192_ = lean_box(0);
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
v_resetjp_5191_:
{
lean_object* v___x_5195_; 
if (v_isShared_5193_ == 0)
{
v___x_5195_ = v___x_5192_;
goto v_reusejp_5194_;
}
else
{
lean_object* v_reuseFailAlloc_5196_; 
v_reuseFailAlloc_5196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_a_5190_);
v___x_5195_ = v_reuseFailAlloc_5196_;
goto v_reusejp_5194_;
}
v_reusejp_5194_:
{
return v___x_5195_;
}
}
}
}
}
else
{
lean_object* v_a_5198_; lean_object* v___x_5200_; uint8_t v_isShared_5201_; uint8_t v_isSharedCheck_5205_; 
lean_dec(v_val_5168_);
lean_dec_ref(v_b_5151_);
lean_dec_ref(v_a_5150_);
v_a_5198_ = lean_ctor_get(v___x_5169_, 0);
v_isSharedCheck_5205_ = !lean_is_exclusive(v___x_5169_);
if (v_isSharedCheck_5205_ == 0)
{
v___x_5200_ = v___x_5169_;
v_isShared_5201_ = v_isSharedCheck_5205_;
goto v_resetjp_5199_;
}
else
{
lean_inc(v_a_5198_);
lean_dec(v___x_5169_);
v___x_5200_ = lean_box(0);
v_isShared_5201_ = v_isSharedCheck_5205_;
goto v_resetjp_5199_;
}
v_resetjp_5199_:
{
lean_object* v___x_5203_; 
if (v_isShared_5201_ == 0)
{
v___x_5203_ = v___x_5200_;
goto v_reusejp_5202_;
}
else
{
lean_object* v_reuseFailAlloc_5204_; 
v_reuseFailAlloc_5204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_a_5198_);
v___x_5203_ = v_reuseFailAlloc_5204_;
goto v_reusejp_5202_;
}
v_reusejp_5202_:
{
return v___x_5203_;
}
}
}
}
else
{
lean_object* v___x_5206_; 
lean_dec(v_a_5167_);
v___x_5206_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5150_, v_b_5151_, v_a_5152_, v_a_5160_);
if (lean_obj_tag(v___x_5206_) == 0)
{
lean_object* v_a_5207_; lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5229_; 
v_a_5207_ = lean_ctor_get(v___x_5206_, 0);
v_isSharedCheck_5229_ = !lean_is_exclusive(v___x_5206_);
if (v_isSharedCheck_5229_ == 0)
{
v___x_5209_ = v___x_5206_;
v_isShared_5210_ = v_isSharedCheck_5229_;
goto v_resetjp_5208_;
}
else
{
lean_inc(v_a_5207_);
lean_dec(v___x_5206_);
v___x_5209_ = lean_box(0);
v_isShared_5210_ = v_isSharedCheck_5229_;
goto v_resetjp_5208_;
}
v_resetjp_5208_:
{
if (lean_obj_tag(v_a_5207_) == 1)
{
lean_object* v_val_5211_; lean_object* v___x_5212_; 
lean_del_object(v___x_5209_);
v_val_5211_ = lean_ctor_get(v_a_5207_, 0);
lean_inc(v_val_5211_);
lean_dec_ref_known(v_a_5207_, 1);
v___x_5212_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_5211_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_);
if (lean_obj_tag(v___x_5212_) == 0)
{
lean_object* v_a_5213_; lean_object* v_orderedAddInst_x3f_5214_; 
v_a_5213_ = lean_ctor_get(v___x_5212_, 0);
lean_inc(v_a_5213_);
lean_dec_ref_known(v___x_5212_, 1);
v_orderedAddInst_x3f_5214_ = lean_ctor_get(v_a_5213_, 9);
lean_inc(v_orderedAddInst_x3f_5214_);
lean_dec(v_a_5213_);
if (lean_obj_tag(v_orderedAddInst_x3f_5214_) == 0)
{
lean_object* v___x_5215_; 
v___x_5215_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5150_, v_b_5151_, v_val_5211_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_);
lean_dec(v_val_5211_);
return v___x_5215_;
}
else
{
lean_object* v___x_5216_; 
lean_dec_ref_known(v_orderedAddInst_x3f_5214_, 1);
v___x_5216_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5150_, v_b_5151_, v_val_5211_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_);
lean_dec(v_val_5211_);
return v___x_5216_;
}
}
else
{
lean_object* v_a_5217_; lean_object* v___x_5219_; uint8_t v_isShared_5220_; uint8_t v_isSharedCheck_5224_; 
lean_dec(v_val_5211_);
lean_dec_ref(v_b_5151_);
lean_dec_ref(v_a_5150_);
v_a_5217_ = lean_ctor_get(v___x_5212_, 0);
v_isSharedCheck_5224_ = !lean_is_exclusive(v___x_5212_);
if (v_isSharedCheck_5224_ == 0)
{
v___x_5219_ = v___x_5212_;
v_isShared_5220_ = v_isSharedCheck_5224_;
goto v_resetjp_5218_;
}
else
{
lean_inc(v_a_5217_);
lean_dec(v___x_5212_);
v___x_5219_ = lean_box(0);
v_isShared_5220_ = v_isSharedCheck_5224_;
goto v_resetjp_5218_;
}
v_resetjp_5218_:
{
lean_object* v___x_5222_; 
if (v_isShared_5220_ == 0)
{
v___x_5222_ = v___x_5219_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_a_5217_);
v___x_5222_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
return v___x_5222_;
}
}
}
}
else
{
lean_object* v___x_5225_; lean_object* v___x_5227_; 
lean_dec(v_a_5207_);
lean_dec_ref(v_b_5151_);
lean_dec_ref(v_a_5150_);
v___x_5225_ = lean_box(0);
if (v_isShared_5210_ == 0)
{
lean_ctor_set(v___x_5209_, 0, v___x_5225_);
v___x_5227_ = v___x_5209_;
goto v_reusejp_5226_;
}
else
{
lean_object* v_reuseFailAlloc_5228_; 
v_reuseFailAlloc_5228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5228_, 0, v___x_5225_);
v___x_5227_ = v_reuseFailAlloc_5228_;
goto v_reusejp_5226_;
}
v_reusejp_5226_:
{
return v___x_5227_;
}
}
}
}
else
{
lean_object* v_a_5230_; lean_object* v___x_5232_; uint8_t v_isShared_5233_; uint8_t v_isSharedCheck_5237_; 
lean_dec_ref(v_b_5151_);
lean_dec_ref(v_a_5150_);
v_a_5230_ = lean_ctor_get(v___x_5206_, 0);
v_isSharedCheck_5237_ = !lean_is_exclusive(v___x_5206_);
if (v_isSharedCheck_5237_ == 0)
{
v___x_5232_ = v___x_5206_;
v_isShared_5233_ = v_isSharedCheck_5237_;
goto v_resetjp_5231_;
}
else
{
lean_inc(v_a_5230_);
lean_dec(v___x_5206_);
v___x_5232_ = lean_box(0);
v_isShared_5233_ = v_isSharedCheck_5237_;
goto v_resetjp_5231_;
}
v_resetjp_5231_:
{
lean_object* v___x_5235_; 
if (v_isShared_5233_ == 0)
{
v___x_5235_ = v___x_5232_;
goto v_reusejp_5234_;
}
else
{
lean_object* v_reuseFailAlloc_5236_; 
v_reuseFailAlloc_5236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5236_, 0, v_a_5230_);
v___x_5235_ = v_reuseFailAlloc_5236_;
goto v_reusejp_5234_;
}
v_reusejp_5234_:
{
return v___x_5235_;
}
}
}
}
}
else
{
lean_object* v_a_5238_; lean_object* v___x_5240_; uint8_t v_isShared_5241_; uint8_t v_isSharedCheck_5245_; 
lean_dec_ref(v_b_5151_);
lean_dec_ref(v_a_5150_);
v_a_5238_ = lean_ctor_get(v___x_5166_, 0);
v_isSharedCheck_5245_ = !lean_is_exclusive(v___x_5166_);
if (v_isSharedCheck_5245_ == 0)
{
v___x_5240_ = v___x_5166_;
v_isShared_5241_ = v_isSharedCheck_5245_;
goto v_resetjp_5239_;
}
else
{
lean_inc(v_a_5238_);
lean_dec(v___x_5166_);
v___x_5240_ = lean_box(0);
v_isShared_5241_ = v_isSharedCheck_5245_;
goto v_resetjp_5239_;
}
v_resetjp_5239_:
{
lean_object* v___x_5243_; 
if (v_isShared_5241_ == 0)
{
v___x_5243_ = v___x_5240_;
goto v_reusejp_5242_;
}
else
{
lean_object* v_reuseFailAlloc_5244_; 
v_reuseFailAlloc_5244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5244_, 0, v_a_5238_);
v___x_5243_ = v_reuseFailAlloc_5244_;
goto v_reusejp_5242_;
}
v_reusejp_5242_:
{
return v___x_5243_;
}
}
}
}
else
{
lean_object* v___x_5246_; lean_object* v___x_5247_; 
lean_dec_ref(v_b_5151_);
lean_dec_ref(v_a_5150_);
v___x_5246_ = lean_box(0);
v___x_5247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5247_, 0, v___x_5246_);
return v___x_5247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed(lean_object* v_a_5248_, lean_object* v_b_5249_, lean_object* v_a_5250_, lean_object* v_a_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_){
_start:
{
lean_object* v_res_5261_; 
v_res_5261_ = l_Lean_Meta_Grind_Arith_Linear_processNewEq(v_a_5248_, v_b_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_);
lean_dec(v_a_5259_);
lean_dec_ref(v_a_5258_);
lean_dec(v_a_5257_);
lean_dec_ref(v_a_5256_);
lean_dec(v_a_5255_);
lean_dec_ref(v_a_5254_);
lean_dec(v_a_5253_);
lean_dec_ref(v_a_5252_);
lean_dec(v_a_5251_);
lean_dec(v_a_5250_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object* v_a_5262_, lean_object* v_b_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_){
_start:
{
uint8_t v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; 
v___x_5276_ = 0;
v___x_5277_ = lean_unsigned_to_nat(0u);
v___x_5278_ = lean_box(v___x_5276_);
lean_inc_ref(v_a_5262_);
v___x_5279_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5279_, 0, v_a_5262_);
lean_closure_set(v___x_5279_, 1, v___x_5278_);
lean_closure_set(v___x_5279_, 2, v___x_5277_);
v___x_5280_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5279_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_);
if (lean_obj_tag(v___x_5280_) == 0)
{
lean_object* v_a_5281_; lean_object* v___x_5283_; uint8_t v_isShared_5284_; uint8_t v_isSharedCheck_5382_; 
v_a_5281_ = lean_ctor_get(v___x_5280_, 0);
v_isSharedCheck_5382_ = !lean_is_exclusive(v___x_5280_);
if (v_isSharedCheck_5382_ == 0)
{
v___x_5283_ = v___x_5280_;
v_isShared_5284_ = v_isSharedCheck_5382_;
goto v_resetjp_5282_;
}
else
{
lean_inc(v_a_5281_);
lean_dec(v___x_5280_);
v___x_5283_ = lean_box(0);
v_isShared_5284_ = v_isSharedCheck_5382_;
goto v_resetjp_5282_;
}
v_resetjp_5282_:
{
if (lean_obj_tag(v_a_5281_) == 1)
{
lean_object* v_val_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; 
lean_del_object(v___x_5283_);
v_val_5285_ = lean_ctor_get(v_a_5281_, 0);
lean_inc(v_val_5285_);
lean_dec_ref_known(v_a_5281_, 1);
v___x_5286_ = lean_box(v___x_5276_);
lean_inc_ref(v_b_5263_);
v___x_5287_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5287_, 0, v_b_5263_);
lean_closure_set(v___x_5287_, 1, v___x_5286_);
lean_closure_set(v___x_5287_, 2, v___x_5277_);
v___x_5288_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5287_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_);
if (lean_obj_tag(v___x_5288_) == 0)
{
lean_object* v_a_5289_; lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5369_; 
v_a_5289_ = lean_ctor_get(v___x_5288_, 0);
v_isSharedCheck_5369_ = !lean_is_exclusive(v___x_5288_);
if (v_isSharedCheck_5369_ == 0)
{
v___x_5291_ = v___x_5288_;
v_isShared_5292_ = v_isSharedCheck_5369_;
goto v_resetjp_5290_;
}
else
{
lean_inc(v_a_5289_);
lean_dec(v___x_5288_);
v___x_5291_ = lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5369_;
goto v_resetjp_5290_;
}
v_resetjp_5290_:
{
if (lean_obj_tag(v_a_5289_) == 1)
{
lean_object* v_val_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; 
lean_del_object(v___x_5291_);
v_val_5293_ = lean_ctor_get(v_a_5289_, 0);
lean_inc_n(v_val_5293_, 2);
lean_dec_ref_known(v_a_5289_, 1);
lean_inc(v_val_5285_);
v___x_5294_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_5294_, 0, v_val_5285_);
lean_ctor_set(v___x_5294_, 1, v_val_5293_);
v___x_5295_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_5294_);
lean_inc_ref(v_b_5263_);
lean_inc_ref(v_a_5262_);
v___x_5296_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5296_, 0, v_a_5262_);
lean_ctor_set(v___x_5296_, 1, v_b_5263_);
lean_ctor_set(v___x_5296_, 2, v_val_5285_);
lean_ctor_set(v___x_5296_, 3, v_val_5293_);
v___x_5297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5297_, 0, v___x_5295_);
lean_ctor_set(v___x_5297_, 1, v___x_5296_);
v___x_5298_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(v___x_5297_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_);
if (lean_obj_tag(v___x_5298_) == 0)
{
lean_object* v_a_5299_; lean_object* v_p_5300_; lean_object* v___x_5301_; 
v_a_5299_ = lean_ctor_get(v___x_5298_, 0);
lean_inc(v_a_5299_);
lean_dec_ref_known(v___x_5298_, 1);
v_p_5300_ = lean_ctor_get(v_a_5299_, 0);
v___x_5301_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5262_, v_a_5265_);
lean_dec_ref(v_a_5262_);
if (lean_obj_tag(v___x_5301_) == 0)
{
lean_object* v_a_5302_; lean_object* v___x_5303_; 
v_a_5302_ = lean_ctor_get(v___x_5301_, 0);
lean_inc(v_a_5302_);
lean_dec_ref_known(v___x_5301_, 1);
v___x_5303_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5263_, v_a_5265_);
lean_dec_ref(v_b_5263_);
if (lean_obj_tag(v___x_5303_) == 0)
{
lean_object* v_a_5304_; lean_object* v___y_5306_; uint8_t v___x_5340_; 
v_a_5304_ = lean_ctor_get(v___x_5303_, 0);
lean_inc(v_a_5304_);
lean_dec_ref_known(v___x_5303_, 1);
v___x_5340_ = lean_nat_dec_le(v_a_5302_, v_a_5304_);
if (v___x_5340_ == 0)
{
lean_dec(v_a_5304_);
v___y_5306_ = v_a_5302_;
goto v___jp_5305_;
}
else
{
lean_dec(v_a_5302_);
v___y_5306_ = v_a_5304_;
goto v___jp_5305_;
}
v___jp_5305_:
{
lean_object* v___x_5307_; 
lean_inc(v___y_5306_);
lean_inc_ref(v_p_5300_);
v___x_5307_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_5300_, v___y_5306_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_);
if (lean_obj_tag(v___x_5307_) == 0)
{
lean_object* v_a_5308_; lean_object* v___x_5309_; 
v_a_5308_ = lean_ctor_get(v___x_5307_, 0);
lean_inc(v_a_5308_);
lean_dec_ref_known(v___x_5307_, 1);
v___x_5309_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5308_, v___x_5276_, v___y_5306_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_);
if (lean_obj_tag(v___x_5309_) == 0)
{
lean_object* v_a_5310_; lean_object* v___x_5312_; uint8_t v_isShared_5313_; uint8_t v_isSharedCheck_5323_; 
v_a_5310_ = lean_ctor_get(v___x_5309_, 0);
v_isSharedCheck_5323_ = !lean_is_exclusive(v___x_5309_);
if (v_isSharedCheck_5323_ == 0)
{
v___x_5312_ = v___x_5309_;
v_isShared_5313_ = v_isSharedCheck_5323_;
goto v_resetjp_5311_;
}
else
{
lean_inc(v_a_5310_);
lean_dec(v___x_5309_);
v___x_5312_ = lean_box(0);
v_isShared_5313_ = v_isSharedCheck_5323_;
goto v_resetjp_5311_;
}
v_resetjp_5311_:
{
if (lean_obj_tag(v_a_5310_) == 1)
{
lean_object* v_val_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; 
lean_del_object(v___x_5312_);
v_val_5314_ = lean_ctor_get(v_a_5310_, 0);
lean_inc_n(v_val_5314_, 2);
lean_dec_ref_known(v_a_5310_, 1);
v___x_5315_ = l_Lean_Grind_Linarith_Expr_norm(v_val_5314_);
v___x_5316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5316_, 0, v_a_5299_);
lean_ctor_set(v___x_5316_, 1, v_val_5314_);
v___x_5317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5317_, 0, v___x_5315_);
lean_ctor_set(v___x_5317_, 1, v___x_5316_);
v___x_5318_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5317_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_);
return v___x_5318_;
}
else
{
lean_object* v___x_5319_; lean_object* v___x_5321_; 
lean_dec(v_a_5310_);
lean_dec(v_a_5299_);
v___x_5319_ = lean_box(0);
if (v_isShared_5313_ == 0)
{
lean_ctor_set(v___x_5312_, 0, v___x_5319_);
v___x_5321_ = v___x_5312_;
goto v_reusejp_5320_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v___x_5319_);
v___x_5321_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5320_;
}
v_reusejp_5320_:
{
return v___x_5321_;
}
}
}
}
else
{
lean_object* v_a_5324_; lean_object* v___x_5326_; uint8_t v_isShared_5327_; uint8_t v_isSharedCheck_5331_; 
lean_dec(v_a_5299_);
v_a_5324_ = lean_ctor_get(v___x_5309_, 0);
v_isSharedCheck_5331_ = !lean_is_exclusive(v___x_5309_);
if (v_isSharedCheck_5331_ == 0)
{
v___x_5326_ = v___x_5309_;
v_isShared_5327_ = v_isSharedCheck_5331_;
goto v_resetjp_5325_;
}
else
{
lean_inc(v_a_5324_);
lean_dec(v___x_5309_);
v___x_5326_ = lean_box(0);
v_isShared_5327_ = v_isSharedCheck_5331_;
goto v_resetjp_5325_;
}
v_resetjp_5325_:
{
lean_object* v___x_5329_; 
if (v_isShared_5327_ == 0)
{
v___x_5329_ = v___x_5326_;
goto v_reusejp_5328_;
}
else
{
lean_object* v_reuseFailAlloc_5330_; 
v_reuseFailAlloc_5330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5330_, 0, v_a_5324_);
v___x_5329_ = v_reuseFailAlloc_5330_;
goto v_reusejp_5328_;
}
v_reusejp_5328_:
{
return v___x_5329_;
}
}
}
}
else
{
lean_object* v_a_5332_; lean_object* v___x_5334_; uint8_t v_isShared_5335_; uint8_t v_isSharedCheck_5339_; 
lean_dec(v___y_5306_);
lean_dec(v_a_5299_);
v_a_5332_ = lean_ctor_get(v___x_5307_, 0);
v_isSharedCheck_5339_ = !lean_is_exclusive(v___x_5307_);
if (v_isSharedCheck_5339_ == 0)
{
v___x_5334_ = v___x_5307_;
v_isShared_5335_ = v_isSharedCheck_5339_;
goto v_resetjp_5333_;
}
else
{
lean_inc(v_a_5332_);
lean_dec(v___x_5307_);
v___x_5334_ = lean_box(0);
v_isShared_5335_ = v_isSharedCheck_5339_;
goto v_resetjp_5333_;
}
v_resetjp_5333_:
{
lean_object* v___x_5337_; 
if (v_isShared_5335_ == 0)
{
v___x_5337_ = v___x_5334_;
goto v_reusejp_5336_;
}
else
{
lean_object* v_reuseFailAlloc_5338_; 
v_reuseFailAlloc_5338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5338_, 0, v_a_5332_);
v___x_5337_ = v_reuseFailAlloc_5338_;
goto v_reusejp_5336_;
}
v_reusejp_5336_:
{
return v___x_5337_;
}
}
}
}
}
else
{
lean_object* v_a_5341_; lean_object* v___x_5343_; uint8_t v_isShared_5344_; uint8_t v_isSharedCheck_5348_; 
lean_dec(v_a_5302_);
lean_dec(v_a_5299_);
v_a_5341_ = lean_ctor_get(v___x_5303_, 0);
v_isSharedCheck_5348_ = !lean_is_exclusive(v___x_5303_);
if (v_isSharedCheck_5348_ == 0)
{
v___x_5343_ = v___x_5303_;
v_isShared_5344_ = v_isSharedCheck_5348_;
goto v_resetjp_5342_;
}
else
{
lean_inc(v_a_5341_);
lean_dec(v___x_5303_);
v___x_5343_ = lean_box(0);
v_isShared_5344_ = v_isSharedCheck_5348_;
goto v_resetjp_5342_;
}
v_resetjp_5342_:
{
lean_object* v___x_5346_; 
if (v_isShared_5344_ == 0)
{
v___x_5346_ = v___x_5343_;
goto v_reusejp_5345_;
}
else
{
lean_object* v_reuseFailAlloc_5347_; 
v_reuseFailAlloc_5347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5347_, 0, v_a_5341_);
v___x_5346_ = v_reuseFailAlloc_5347_;
goto v_reusejp_5345_;
}
v_reusejp_5345_:
{
return v___x_5346_;
}
}
}
}
else
{
lean_object* v_a_5349_; lean_object* v___x_5351_; uint8_t v_isShared_5352_; uint8_t v_isSharedCheck_5356_; 
lean_dec(v_a_5299_);
lean_dec_ref(v_b_5263_);
v_a_5349_ = lean_ctor_get(v___x_5301_, 0);
v_isSharedCheck_5356_ = !lean_is_exclusive(v___x_5301_);
if (v_isSharedCheck_5356_ == 0)
{
v___x_5351_ = v___x_5301_;
v_isShared_5352_ = v_isSharedCheck_5356_;
goto v_resetjp_5350_;
}
else
{
lean_inc(v_a_5349_);
lean_dec(v___x_5301_);
v___x_5351_ = lean_box(0);
v_isShared_5352_ = v_isSharedCheck_5356_;
goto v_resetjp_5350_;
}
v_resetjp_5350_:
{
lean_object* v___x_5354_; 
if (v_isShared_5352_ == 0)
{
v___x_5354_ = v___x_5351_;
goto v_reusejp_5353_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v_a_5349_);
v___x_5354_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5353_;
}
v_reusejp_5353_:
{
return v___x_5354_;
}
}
}
}
else
{
lean_object* v_a_5357_; lean_object* v___x_5359_; uint8_t v_isShared_5360_; uint8_t v_isSharedCheck_5364_; 
lean_dec_ref(v_b_5263_);
lean_dec_ref(v_a_5262_);
v_a_5357_ = lean_ctor_get(v___x_5298_, 0);
v_isSharedCheck_5364_ = !lean_is_exclusive(v___x_5298_);
if (v_isSharedCheck_5364_ == 0)
{
v___x_5359_ = v___x_5298_;
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
else
{
lean_inc(v_a_5357_);
lean_dec(v___x_5298_);
v___x_5359_ = lean_box(0);
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
v_resetjp_5358_:
{
lean_object* v___x_5362_; 
if (v_isShared_5360_ == 0)
{
v___x_5362_ = v___x_5359_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v_a_5357_);
v___x_5362_ = v_reuseFailAlloc_5363_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
return v___x_5362_;
}
}
}
}
else
{
lean_object* v___x_5365_; lean_object* v___x_5367_; 
lean_dec(v_a_5289_);
lean_dec(v_val_5285_);
lean_dec_ref(v_b_5263_);
lean_dec_ref(v_a_5262_);
v___x_5365_ = lean_box(0);
if (v_isShared_5292_ == 0)
{
lean_ctor_set(v___x_5291_, 0, v___x_5365_);
v___x_5367_ = v___x_5291_;
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
lean_dec(v_val_5285_);
lean_dec_ref(v_b_5263_);
lean_dec_ref(v_a_5262_);
v_a_5370_ = lean_ctor_get(v___x_5288_, 0);
v_isSharedCheck_5377_ = !lean_is_exclusive(v___x_5288_);
if (v_isSharedCheck_5377_ == 0)
{
v___x_5372_ = v___x_5288_;
v_isShared_5373_ = v_isSharedCheck_5377_;
goto v_resetjp_5371_;
}
else
{
lean_inc(v_a_5370_);
lean_dec(v___x_5288_);
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
lean_object* v___x_5378_; lean_object* v___x_5380_; 
lean_dec(v_a_5281_);
lean_dec_ref(v_b_5263_);
lean_dec_ref(v_a_5262_);
v___x_5378_ = lean_box(0);
if (v_isShared_5284_ == 0)
{
lean_ctor_set(v___x_5283_, 0, v___x_5378_);
v___x_5380_ = v___x_5283_;
goto v_reusejp_5379_;
}
else
{
lean_object* v_reuseFailAlloc_5381_; 
v_reuseFailAlloc_5381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5381_, 0, v___x_5378_);
v___x_5380_ = v_reuseFailAlloc_5381_;
goto v_reusejp_5379_;
}
v_reusejp_5379_:
{
return v___x_5380_;
}
}
}
}
else
{
lean_object* v_a_5383_; lean_object* v___x_5385_; uint8_t v_isShared_5386_; uint8_t v_isSharedCheck_5390_; 
lean_dec_ref(v_b_5263_);
lean_dec_ref(v_a_5262_);
v_a_5383_ = lean_ctor_get(v___x_5280_, 0);
v_isSharedCheck_5390_ = !lean_is_exclusive(v___x_5280_);
if (v_isSharedCheck_5390_ == 0)
{
v___x_5385_ = v___x_5280_;
v_isShared_5386_ = v_isSharedCheck_5390_;
goto v_resetjp_5384_;
}
else
{
lean_inc(v_a_5383_);
lean_dec(v___x_5280_);
v___x_5385_ = lean_box(0);
v_isShared_5386_ = v_isSharedCheck_5390_;
goto v_resetjp_5384_;
}
v_resetjp_5384_:
{
lean_object* v___x_5388_; 
if (v_isShared_5386_ == 0)
{
v___x_5388_ = v___x_5385_;
goto v_reusejp_5387_;
}
else
{
lean_object* v_reuseFailAlloc_5389_; 
v_reuseFailAlloc_5389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5389_, 0, v_a_5383_);
v___x_5388_ = v_reuseFailAlloc_5389_;
goto v_reusejp_5387_;
}
v_reusejp_5387_:
{
return v___x_5388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq___boxed(lean_object* v_a_5391_, lean_object* v_b_5392_, lean_object* v_a_5393_, lean_object* v_a_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_){
_start:
{
lean_object* v_res_5405_; 
v_res_5405_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5391_, v_b_5392_, v_a_5393_, v_a_5394_, v_a_5395_, v_a_5396_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_);
lean_dec(v_a_5403_);
lean_dec_ref(v_a_5402_);
lean_dec(v_a_5401_);
lean_dec_ref(v_a_5400_);
lean_dec(v_a_5399_);
lean_dec_ref(v_a_5398_);
lean_dec(v_a_5397_);
lean_dec_ref(v_a_5396_);
lean_dec(v_a_5395_);
lean_dec(v_a_5394_);
lean_dec(v_a_5393_);
return v_res_5405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(lean_object* v_a_5406_, lean_object* v_b_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_){
_start:
{
lean_object* v___x_5420_; 
v___x_5420_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5406_, v_a_5409_);
if (lean_obj_tag(v___x_5420_) == 0)
{
lean_object* v_a_5421_; uint8_t v___x_5422_; lean_object* v___x_5423_; 
v_a_5421_ = lean_ctor_get(v___x_5420_, 0);
lean_inc(v_a_5421_);
lean_dec_ref_known(v___x_5420_, 1);
v___x_5422_ = 0;
lean_inc_ref(v_a_5406_);
v___x_5423_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5406_, v___x_5422_, v_a_5421_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_);
if (lean_obj_tag(v___x_5423_) == 0)
{
lean_object* v_a_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5467_; 
v_a_5424_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5467_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5467_ == 0)
{
v___x_5426_ = v___x_5423_;
v_isShared_5427_ = v_isSharedCheck_5467_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_a_5424_);
lean_dec(v___x_5423_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5467_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
if (lean_obj_tag(v_a_5424_) == 1)
{
lean_object* v_val_5428_; lean_object* v___x_5429_; 
lean_del_object(v___x_5426_);
v_val_5428_ = lean_ctor_get(v_a_5424_, 0);
lean_inc(v_val_5428_);
lean_dec_ref_known(v_a_5424_, 1);
v___x_5429_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5407_, v_a_5409_);
if (lean_obj_tag(v___x_5429_) == 0)
{
lean_object* v_a_5430_; lean_object* v___x_5431_; 
v_a_5430_ = lean_ctor_get(v___x_5429_, 0);
lean_inc(v_a_5430_);
lean_dec_ref_known(v___x_5429_, 1);
lean_inc_ref(v_b_5407_);
v___x_5431_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_5407_, v___x_5422_, v_a_5430_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_);
if (lean_obj_tag(v___x_5431_) == 0)
{
lean_object* v_a_5432_; lean_object* v___x_5434_; uint8_t v_isShared_5435_; uint8_t v_isSharedCheck_5446_; 
v_a_5432_ = lean_ctor_get(v___x_5431_, 0);
v_isSharedCheck_5446_ = !lean_is_exclusive(v___x_5431_);
if (v_isSharedCheck_5446_ == 0)
{
v___x_5434_ = v___x_5431_;
v_isShared_5435_ = v_isSharedCheck_5446_;
goto v_resetjp_5433_;
}
else
{
lean_inc(v_a_5432_);
lean_dec(v___x_5431_);
v___x_5434_ = lean_box(0);
v_isShared_5435_ = v_isSharedCheck_5446_;
goto v_resetjp_5433_;
}
v_resetjp_5433_:
{
if (lean_obj_tag(v_a_5432_) == 1)
{
lean_object* v_val_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; 
lean_del_object(v___x_5434_);
v_val_5436_ = lean_ctor_get(v_a_5432_, 0);
lean_inc_n(v_val_5436_, 2);
lean_dec_ref_known(v_a_5432_, 1);
lean_inc(v_val_5428_);
v___x_5437_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5437_, 0, v_val_5428_);
lean_ctor_set(v___x_5437_, 1, v_val_5436_);
v___x_5438_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5437_);
v___x_5439_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5439_, 0, v_a_5406_);
lean_ctor_set(v___x_5439_, 1, v_b_5407_);
lean_ctor_set(v___x_5439_, 2, v_val_5428_);
lean_ctor_set(v___x_5439_, 3, v_val_5436_);
v___x_5440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5440_, 0, v___x_5438_);
lean_ctor_set(v___x_5440_, 1, v___x_5439_);
v___x_5441_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5440_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_);
return v___x_5441_;
}
else
{
lean_object* v___x_5442_; lean_object* v___x_5444_; 
lean_dec(v_a_5432_);
lean_dec(v_val_5428_);
lean_dec_ref(v_b_5407_);
lean_dec_ref(v_a_5406_);
v___x_5442_ = lean_box(0);
if (v_isShared_5435_ == 0)
{
lean_ctor_set(v___x_5434_, 0, v___x_5442_);
v___x_5444_ = v___x_5434_;
goto v_reusejp_5443_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v___x_5442_);
v___x_5444_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5443_;
}
v_reusejp_5443_:
{
return v___x_5444_;
}
}
}
}
else
{
lean_object* v_a_5447_; lean_object* v___x_5449_; uint8_t v_isShared_5450_; uint8_t v_isSharedCheck_5454_; 
lean_dec(v_val_5428_);
lean_dec_ref(v_b_5407_);
lean_dec_ref(v_a_5406_);
v_a_5447_ = lean_ctor_get(v___x_5431_, 0);
v_isSharedCheck_5454_ = !lean_is_exclusive(v___x_5431_);
if (v_isSharedCheck_5454_ == 0)
{
v___x_5449_ = v___x_5431_;
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
else
{
lean_inc(v_a_5447_);
lean_dec(v___x_5431_);
v___x_5449_ = lean_box(0);
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
v_resetjp_5448_:
{
lean_object* v___x_5452_; 
if (v_isShared_5450_ == 0)
{
v___x_5452_ = v___x_5449_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_a_5447_);
v___x_5452_ = v_reuseFailAlloc_5453_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
return v___x_5452_;
}
}
}
}
else
{
lean_object* v_a_5455_; lean_object* v___x_5457_; uint8_t v_isShared_5458_; uint8_t v_isSharedCheck_5462_; 
lean_dec(v_val_5428_);
lean_dec_ref(v_b_5407_);
lean_dec_ref(v_a_5406_);
v_a_5455_ = lean_ctor_get(v___x_5429_, 0);
v_isSharedCheck_5462_ = !lean_is_exclusive(v___x_5429_);
if (v_isSharedCheck_5462_ == 0)
{
v___x_5457_ = v___x_5429_;
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
else
{
lean_inc(v_a_5455_);
lean_dec(v___x_5429_);
v___x_5457_ = lean_box(0);
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
v_resetjp_5456_:
{
lean_object* v___x_5460_; 
if (v_isShared_5458_ == 0)
{
v___x_5460_ = v___x_5457_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_a_5455_);
v___x_5460_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
return v___x_5460_;
}
}
}
}
else
{
lean_object* v___x_5463_; lean_object* v___x_5465_; 
lean_dec(v_a_5424_);
lean_dec_ref(v_b_5407_);
lean_dec_ref(v_a_5406_);
v___x_5463_ = lean_box(0);
if (v_isShared_5427_ == 0)
{
lean_ctor_set(v___x_5426_, 0, v___x_5463_);
v___x_5465_ = v___x_5426_;
goto v_reusejp_5464_;
}
else
{
lean_object* v_reuseFailAlloc_5466_; 
v_reuseFailAlloc_5466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5466_, 0, v___x_5463_);
v___x_5465_ = v_reuseFailAlloc_5466_;
goto v_reusejp_5464_;
}
v_reusejp_5464_:
{
return v___x_5465_;
}
}
}
}
else
{
lean_object* v_a_5468_; lean_object* v___x_5470_; uint8_t v_isShared_5471_; uint8_t v_isSharedCheck_5475_; 
lean_dec_ref(v_b_5407_);
lean_dec_ref(v_a_5406_);
v_a_5468_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5475_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5475_ == 0)
{
v___x_5470_ = v___x_5423_;
v_isShared_5471_ = v_isSharedCheck_5475_;
goto v_resetjp_5469_;
}
else
{
lean_inc(v_a_5468_);
lean_dec(v___x_5423_);
v___x_5470_ = lean_box(0);
v_isShared_5471_ = v_isSharedCheck_5475_;
goto v_resetjp_5469_;
}
v_resetjp_5469_:
{
lean_object* v___x_5473_; 
if (v_isShared_5471_ == 0)
{
v___x_5473_ = v___x_5470_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5474_; 
v_reuseFailAlloc_5474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5474_, 0, v_a_5468_);
v___x_5473_ = v_reuseFailAlloc_5474_;
goto v_reusejp_5472_;
}
v_reusejp_5472_:
{
return v___x_5473_;
}
}
}
}
else
{
lean_object* v_a_5476_; lean_object* v___x_5478_; uint8_t v_isShared_5479_; uint8_t v_isSharedCheck_5483_; 
lean_dec_ref(v_b_5407_);
lean_dec_ref(v_a_5406_);
v_a_5476_ = lean_ctor_get(v___x_5420_, 0);
v_isSharedCheck_5483_ = !lean_is_exclusive(v___x_5420_);
if (v_isSharedCheck_5483_ == 0)
{
v___x_5478_ = v___x_5420_;
v_isShared_5479_ = v_isSharedCheck_5483_;
goto v_resetjp_5477_;
}
else
{
lean_inc(v_a_5476_);
lean_dec(v___x_5420_);
v___x_5478_ = lean_box(0);
v_isShared_5479_ = v_isSharedCheck_5483_;
goto v_resetjp_5477_;
}
v_resetjp_5477_:
{
lean_object* v___x_5481_; 
if (v_isShared_5479_ == 0)
{
v___x_5481_ = v___x_5478_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5482_; 
v_reuseFailAlloc_5482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5482_, 0, v_a_5476_);
v___x_5481_ = v_reuseFailAlloc_5482_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
return v___x_5481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq___boxed(lean_object* v_a_5484_, lean_object* v_b_5485_, lean_object* v_a_5486_, lean_object* v_a_5487_, lean_object* v_a_5488_, lean_object* v_a_5489_, lean_object* v_a_5490_, lean_object* v_a_5491_, lean_object* v_a_5492_, lean_object* v_a_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_){
_start:
{
lean_object* v_res_5498_; 
v_res_5498_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5484_, v_b_5485_, v_a_5486_, v_a_5487_, v_a_5488_, v_a_5489_, v_a_5490_, v_a_5491_, v_a_5492_, v_a_5493_, v_a_5494_, v_a_5495_, v_a_5496_);
lean_dec(v_a_5496_);
lean_dec_ref(v_a_5495_);
lean_dec(v_a_5494_);
lean_dec_ref(v_a_5493_);
lean_dec(v_a_5492_);
lean_dec_ref(v_a_5491_);
lean_dec(v_a_5490_);
lean_dec_ref(v_a_5489_);
lean_dec(v_a_5488_);
lean_dec(v_a_5487_);
lean_dec(v_a_5486_);
return v_res_5498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(lean_object* v_a_5499_, lean_object* v_b_5500_, lean_object* v_a_5501_, lean_object* v_a_5502_, lean_object* v_a_5503_, lean_object* v_a_5504_, lean_object* v_a_5505_, lean_object* v_a_5506_, lean_object* v_a_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_){
_start:
{
lean_object* v___x_5513_; 
v___x_5513_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_);
if (lean_obj_tag(v___x_5513_) == 0)
{
lean_object* v_a_5514_; lean_object* v_addRightCancelInst_x3f_5515_; 
v_a_5514_ = lean_ctor_get(v___x_5513_, 0);
lean_inc(v_a_5514_);
lean_dec_ref_known(v___x_5513_, 1);
v_addRightCancelInst_x3f_5515_ = lean_ctor_get(v_a_5514_, 11);
if (lean_obj_tag(v_addRightCancelInst_x3f_5515_) == 0)
{
lean_object* v___x_5516_; 
lean_dec(v_a_5514_);
v___x_5516_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(v_a_5499_, v_b_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_);
return v___x_5516_;
}
else
{
lean_object* v_id_5517_; lean_object* v_structId_5518_; lean_object* v___x_5519_; 
v_id_5517_ = lean_ctor_get(v_a_5514_, 0);
lean_inc(v_id_5517_);
v_structId_5518_ = lean_ctor_get(v_a_5514_, 1);
lean_inc(v_structId_5518_);
lean_dec(v_a_5514_);
lean_inc_ref(v_a_5499_);
v___x_5519_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5499_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_);
if (lean_obj_tag(v___x_5519_) == 0)
{
lean_object* v_a_5520_; lean_object* v_fst_5521_; lean_object* v___x_5523_; uint8_t v_isShared_5524_; uint8_t v_isSharedCheck_5609_; 
v_a_5520_ = lean_ctor_get(v___x_5519_, 0);
lean_inc(v_a_5520_);
lean_dec_ref_known(v___x_5519_, 1);
v_fst_5521_ = lean_ctor_get(v_a_5520_, 0);
v_isSharedCheck_5609_ = !lean_is_exclusive(v_a_5520_);
if (v_isSharedCheck_5609_ == 0)
{
lean_object* v_unused_5610_; 
v_unused_5610_ = lean_ctor_get(v_a_5520_, 1);
lean_dec(v_unused_5610_);
v___x_5523_ = v_a_5520_;
v_isShared_5524_ = v_isSharedCheck_5609_;
goto v_resetjp_5522_;
}
else
{
lean_inc(v_fst_5521_);
lean_dec(v_a_5520_);
v___x_5523_ = lean_box(0);
v_isShared_5524_ = v_isSharedCheck_5609_;
goto v_resetjp_5522_;
}
v_resetjp_5522_:
{
lean_object* v___x_5525_; 
lean_inc_ref(v_b_5500_);
v___x_5525_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_);
if (lean_obj_tag(v___x_5525_) == 0)
{
lean_object* v_a_5526_; lean_object* v_fst_5527_; lean_object* v___x_5529_; uint8_t v_isShared_5530_; uint8_t v_isSharedCheck_5599_; 
v_a_5526_ = lean_ctor_get(v___x_5525_, 0);
lean_inc(v_a_5526_);
lean_dec_ref_known(v___x_5525_, 1);
v_fst_5527_ = lean_ctor_get(v_a_5526_, 0);
v_isSharedCheck_5599_ = !lean_is_exclusive(v_a_5526_);
if (v_isSharedCheck_5599_ == 0)
{
lean_object* v_unused_5600_; 
v_unused_5600_ = lean_ctor_get(v_a_5526_, 1);
lean_dec(v_unused_5600_);
v___x_5529_ = v_a_5526_;
v_isShared_5530_ = v_isSharedCheck_5599_;
goto v_resetjp_5528_;
}
else
{
lean_inc(v_fst_5527_);
lean_dec(v_a_5526_);
v___x_5529_ = lean_box(0);
v_isShared_5530_ = v_isSharedCheck_5599_;
goto v_resetjp_5528_;
}
v_resetjp_5528_:
{
lean_object* v___x_5531_; 
v___x_5531_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5499_, v_a_5502_);
if (lean_obj_tag(v___x_5531_) == 0)
{
lean_object* v_a_5532_; uint8_t v___x_5533_; lean_object* v___x_5534_; 
v_a_5532_ = lean_ctor_get(v___x_5531_, 0);
lean_inc(v_a_5532_);
lean_dec_ref_known(v___x_5531_, 1);
v___x_5533_ = 0;
v___x_5534_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5521_, v___x_5533_, v_a_5532_, v_structId_5518_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_);
if (lean_obj_tag(v___x_5534_) == 0)
{
lean_object* v_a_5535_; lean_object* v___x_5537_; uint8_t v_isShared_5538_; uint8_t v_isSharedCheck_5582_; 
v_a_5535_ = lean_ctor_get(v___x_5534_, 0);
v_isSharedCheck_5582_ = !lean_is_exclusive(v___x_5534_);
if (v_isSharedCheck_5582_ == 0)
{
v___x_5537_ = v___x_5534_;
v_isShared_5538_ = v_isSharedCheck_5582_;
goto v_resetjp_5536_;
}
else
{
lean_inc(v_a_5535_);
lean_dec(v___x_5534_);
v___x_5537_ = lean_box(0);
v_isShared_5538_ = v_isSharedCheck_5582_;
goto v_resetjp_5536_;
}
v_resetjp_5536_:
{
if (lean_obj_tag(v_a_5535_) == 1)
{
lean_object* v_val_5539_; lean_object* v___x_5540_; 
lean_del_object(v___x_5537_);
v_val_5539_ = lean_ctor_get(v_a_5535_, 0);
lean_inc(v_val_5539_);
lean_dec_ref_known(v_a_5535_, 1);
v___x_5540_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5500_, v_a_5502_);
if (lean_obj_tag(v___x_5540_) == 0)
{
lean_object* v_a_5541_; lean_object* v___x_5542_; 
v_a_5541_ = lean_ctor_get(v___x_5540_, 0);
lean_inc(v_a_5541_);
lean_dec_ref_known(v___x_5540_, 1);
v___x_5542_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5527_, v___x_5533_, v_a_5541_, v_structId_5518_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_);
if (lean_obj_tag(v___x_5542_) == 0)
{
lean_object* v_a_5543_; lean_object* v___x_5545_; uint8_t v_isShared_5546_; uint8_t v_isSharedCheck_5561_; 
v_a_5543_ = lean_ctor_get(v___x_5542_, 0);
v_isSharedCheck_5561_ = !lean_is_exclusive(v___x_5542_);
if (v_isSharedCheck_5561_ == 0)
{
v___x_5545_ = v___x_5542_;
v_isShared_5546_ = v_isSharedCheck_5561_;
goto v_resetjp_5544_;
}
else
{
lean_inc(v_a_5543_);
lean_dec(v___x_5542_);
v___x_5545_ = lean_box(0);
v_isShared_5546_ = v_isSharedCheck_5561_;
goto v_resetjp_5544_;
}
v_resetjp_5544_:
{
if (lean_obj_tag(v_a_5543_) == 1)
{
lean_object* v_val_5547_; lean_object* v___x_5549_; 
lean_del_object(v___x_5545_);
v_val_5547_ = lean_ctor_get(v_a_5543_, 0);
lean_inc_n(v_val_5547_, 2);
lean_dec_ref_known(v_a_5543_, 1);
lean_inc(v_val_5539_);
if (v_isShared_5530_ == 0)
{
lean_ctor_set_tag(v___x_5529_, 3);
lean_ctor_set(v___x_5529_, 1, v_val_5547_);
lean_ctor_set(v___x_5529_, 0, v_val_5539_);
v___x_5549_ = v___x_5529_;
goto v_reusejp_5548_;
}
else
{
lean_object* v_reuseFailAlloc_5556_; 
v_reuseFailAlloc_5556_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5556_, 0, v_val_5539_);
lean_ctor_set(v_reuseFailAlloc_5556_, 1, v_val_5547_);
v___x_5549_ = v_reuseFailAlloc_5556_;
goto v_reusejp_5548_;
}
v_reusejp_5548_:
{
lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5553_; 
v___x_5550_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5549_);
v___x_5551_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5551_, 0, v_a_5499_);
lean_ctor_set(v___x_5551_, 1, v_b_5500_);
lean_ctor_set(v___x_5551_, 2, v_id_5517_);
lean_ctor_set(v___x_5551_, 3, v_val_5539_);
lean_ctor_set(v___x_5551_, 4, v_val_5547_);
if (v_isShared_5524_ == 0)
{
lean_ctor_set(v___x_5523_, 1, v___x_5551_);
lean_ctor_set(v___x_5523_, 0, v___x_5550_);
v___x_5553_ = v___x_5523_;
goto v_reusejp_5552_;
}
else
{
lean_object* v_reuseFailAlloc_5555_; 
v_reuseFailAlloc_5555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5555_, 0, v___x_5550_);
lean_ctor_set(v_reuseFailAlloc_5555_, 1, v___x_5551_);
v___x_5553_ = v_reuseFailAlloc_5555_;
goto v_reusejp_5552_;
}
v_reusejp_5552_:
{
lean_object* v___x_5554_; 
v___x_5554_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5553_, v_structId_5518_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_);
lean_dec(v_structId_5518_);
return v___x_5554_;
}
}
}
else
{
lean_object* v___x_5557_; lean_object* v___x_5559_; 
lean_dec(v_a_5543_);
lean_dec(v_val_5539_);
lean_del_object(v___x_5529_);
lean_del_object(v___x_5523_);
lean_dec(v_structId_5518_);
lean_dec(v_id_5517_);
lean_dec_ref(v_b_5500_);
lean_dec_ref(v_a_5499_);
v___x_5557_ = lean_box(0);
if (v_isShared_5546_ == 0)
{
lean_ctor_set(v___x_5545_, 0, v___x_5557_);
v___x_5559_ = v___x_5545_;
goto v_reusejp_5558_;
}
else
{
lean_object* v_reuseFailAlloc_5560_; 
v_reuseFailAlloc_5560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5560_, 0, v___x_5557_);
v___x_5559_ = v_reuseFailAlloc_5560_;
goto v_reusejp_5558_;
}
v_reusejp_5558_:
{
return v___x_5559_;
}
}
}
}
else
{
lean_object* v_a_5562_; lean_object* v___x_5564_; uint8_t v_isShared_5565_; uint8_t v_isSharedCheck_5569_; 
lean_dec(v_val_5539_);
lean_del_object(v___x_5529_);
lean_del_object(v___x_5523_);
lean_dec(v_structId_5518_);
lean_dec(v_id_5517_);
lean_dec_ref(v_b_5500_);
lean_dec_ref(v_a_5499_);
v_a_5562_ = lean_ctor_get(v___x_5542_, 0);
v_isSharedCheck_5569_ = !lean_is_exclusive(v___x_5542_);
if (v_isSharedCheck_5569_ == 0)
{
v___x_5564_ = v___x_5542_;
v_isShared_5565_ = v_isSharedCheck_5569_;
goto v_resetjp_5563_;
}
else
{
lean_inc(v_a_5562_);
lean_dec(v___x_5542_);
v___x_5564_ = lean_box(0);
v_isShared_5565_ = v_isSharedCheck_5569_;
goto v_resetjp_5563_;
}
v_resetjp_5563_:
{
lean_object* v___x_5567_; 
if (v_isShared_5565_ == 0)
{
v___x_5567_ = v___x_5564_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_a_5562_);
v___x_5567_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
return v___x_5567_;
}
}
}
}
else
{
lean_object* v_a_5570_; lean_object* v___x_5572_; uint8_t v_isShared_5573_; uint8_t v_isSharedCheck_5577_; 
lean_dec(v_val_5539_);
lean_del_object(v___x_5529_);
lean_dec(v_fst_5527_);
lean_del_object(v___x_5523_);
lean_dec(v_structId_5518_);
lean_dec(v_id_5517_);
lean_dec_ref(v_b_5500_);
lean_dec_ref(v_a_5499_);
v_a_5570_ = lean_ctor_get(v___x_5540_, 0);
v_isSharedCheck_5577_ = !lean_is_exclusive(v___x_5540_);
if (v_isSharedCheck_5577_ == 0)
{
v___x_5572_ = v___x_5540_;
v_isShared_5573_ = v_isSharedCheck_5577_;
goto v_resetjp_5571_;
}
else
{
lean_inc(v_a_5570_);
lean_dec(v___x_5540_);
v___x_5572_ = lean_box(0);
v_isShared_5573_ = v_isSharedCheck_5577_;
goto v_resetjp_5571_;
}
v_resetjp_5571_:
{
lean_object* v___x_5575_; 
if (v_isShared_5573_ == 0)
{
v___x_5575_ = v___x_5572_;
goto v_reusejp_5574_;
}
else
{
lean_object* v_reuseFailAlloc_5576_; 
v_reuseFailAlloc_5576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5576_, 0, v_a_5570_);
v___x_5575_ = v_reuseFailAlloc_5576_;
goto v_reusejp_5574_;
}
v_reusejp_5574_:
{
return v___x_5575_;
}
}
}
}
else
{
lean_object* v___x_5578_; lean_object* v___x_5580_; 
lean_dec(v_a_5535_);
lean_del_object(v___x_5529_);
lean_dec(v_fst_5527_);
lean_del_object(v___x_5523_);
lean_dec(v_structId_5518_);
lean_dec(v_id_5517_);
lean_dec_ref(v_b_5500_);
lean_dec_ref(v_a_5499_);
v___x_5578_ = lean_box(0);
if (v_isShared_5538_ == 0)
{
lean_ctor_set(v___x_5537_, 0, v___x_5578_);
v___x_5580_ = v___x_5537_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v___x_5578_);
v___x_5580_ = v_reuseFailAlloc_5581_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
return v___x_5580_;
}
}
}
}
else
{
lean_object* v_a_5583_; lean_object* v___x_5585_; uint8_t v_isShared_5586_; uint8_t v_isSharedCheck_5590_; 
lean_del_object(v___x_5529_);
lean_dec(v_fst_5527_);
lean_del_object(v___x_5523_);
lean_dec(v_structId_5518_);
lean_dec(v_id_5517_);
lean_dec_ref(v_b_5500_);
lean_dec_ref(v_a_5499_);
v_a_5583_ = lean_ctor_get(v___x_5534_, 0);
v_isSharedCheck_5590_ = !lean_is_exclusive(v___x_5534_);
if (v_isSharedCheck_5590_ == 0)
{
v___x_5585_ = v___x_5534_;
v_isShared_5586_ = v_isSharedCheck_5590_;
goto v_resetjp_5584_;
}
else
{
lean_inc(v_a_5583_);
lean_dec(v___x_5534_);
v___x_5585_ = lean_box(0);
v_isShared_5586_ = v_isSharedCheck_5590_;
goto v_resetjp_5584_;
}
v_resetjp_5584_:
{
lean_object* v___x_5588_; 
if (v_isShared_5586_ == 0)
{
v___x_5588_ = v___x_5585_;
goto v_reusejp_5587_;
}
else
{
lean_object* v_reuseFailAlloc_5589_; 
v_reuseFailAlloc_5589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5589_, 0, v_a_5583_);
v___x_5588_ = v_reuseFailAlloc_5589_;
goto v_reusejp_5587_;
}
v_reusejp_5587_:
{
return v___x_5588_;
}
}
}
}
else
{
lean_object* v_a_5591_; lean_object* v___x_5593_; uint8_t v_isShared_5594_; uint8_t v_isSharedCheck_5598_; 
lean_del_object(v___x_5529_);
lean_dec(v_fst_5527_);
lean_del_object(v___x_5523_);
lean_dec(v_fst_5521_);
lean_dec(v_structId_5518_);
lean_dec(v_id_5517_);
lean_dec_ref(v_b_5500_);
lean_dec_ref(v_a_5499_);
v_a_5591_ = lean_ctor_get(v___x_5531_, 0);
v_isSharedCheck_5598_ = !lean_is_exclusive(v___x_5531_);
if (v_isSharedCheck_5598_ == 0)
{
v___x_5593_ = v___x_5531_;
v_isShared_5594_ = v_isSharedCheck_5598_;
goto v_resetjp_5592_;
}
else
{
lean_inc(v_a_5591_);
lean_dec(v___x_5531_);
v___x_5593_ = lean_box(0);
v_isShared_5594_ = v_isSharedCheck_5598_;
goto v_resetjp_5592_;
}
v_resetjp_5592_:
{
lean_object* v___x_5596_; 
if (v_isShared_5594_ == 0)
{
v___x_5596_ = v___x_5593_;
goto v_reusejp_5595_;
}
else
{
lean_object* v_reuseFailAlloc_5597_; 
v_reuseFailAlloc_5597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5597_, 0, v_a_5591_);
v___x_5596_ = v_reuseFailAlloc_5597_;
goto v_reusejp_5595_;
}
v_reusejp_5595_:
{
return v___x_5596_;
}
}
}
}
}
else
{
lean_object* v_a_5601_; lean_object* v___x_5603_; uint8_t v_isShared_5604_; uint8_t v_isSharedCheck_5608_; 
lean_del_object(v___x_5523_);
lean_dec(v_fst_5521_);
lean_dec(v_structId_5518_);
lean_dec(v_id_5517_);
lean_dec_ref(v_b_5500_);
lean_dec_ref(v_a_5499_);
v_a_5601_ = lean_ctor_get(v___x_5525_, 0);
v_isSharedCheck_5608_ = !lean_is_exclusive(v___x_5525_);
if (v_isSharedCheck_5608_ == 0)
{
v___x_5603_ = v___x_5525_;
v_isShared_5604_ = v_isSharedCheck_5608_;
goto v_resetjp_5602_;
}
else
{
lean_inc(v_a_5601_);
lean_dec(v___x_5525_);
v___x_5603_ = lean_box(0);
v_isShared_5604_ = v_isSharedCheck_5608_;
goto v_resetjp_5602_;
}
v_resetjp_5602_:
{
lean_object* v___x_5606_; 
if (v_isShared_5604_ == 0)
{
v___x_5606_ = v___x_5603_;
goto v_reusejp_5605_;
}
else
{
lean_object* v_reuseFailAlloc_5607_; 
v_reuseFailAlloc_5607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5607_, 0, v_a_5601_);
v___x_5606_ = v_reuseFailAlloc_5607_;
goto v_reusejp_5605_;
}
v_reusejp_5605_:
{
return v___x_5606_;
}
}
}
}
}
else
{
lean_object* v_a_5611_; lean_object* v___x_5613_; uint8_t v_isShared_5614_; uint8_t v_isSharedCheck_5618_; 
lean_dec(v_structId_5518_);
lean_dec(v_id_5517_);
lean_dec_ref(v_b_5500_);
lean_dec_ref(v_a_5499_);
v_a_5611_ = lean_ctor_get(v___x_5519_, 0);
v_isSharedCheck_5618_ = !lean_is_exclusive(v___x_5519_);
if (v_isSharedCheck_5618_ == 0)
{
v___x_5613_ = v___x_5519_;
v_isShared_5614_ = v_isSharedCheck_5618_;
goto v_resetjp_5612_;
}
else
{
lean_inc(v_a_5611_);
lean_dec(v___x_5519_);
v___x_5613_ = lean_box(0);
v_isShared_5614_ = v_isSharedCheck_5618_;
goto v_resetjp_5612_;
}
v_resetjp_5612_:
{
lean_object* v___x_5616_; 
if (v_isShared_5614_ == 0)
{
v___x_5616_ = v___x_5613_;
goto v_reusejp_5615_;
}
else
{
lean_object* v_reuseFailAlloc_5617_; 
v_reuseFailAlloc_5617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5617_, 0, v_a_5611_);
v___x_5616_ = v_reuseFailAlloc_5617_;
goto v_reusejp_5615_;
}
v_reusejp_5615_:
{
return v___x_5616_;
}
}
}
}
}
else
{
lean_object* v_a_5619_; lean_object* v___x_5621_; uint8_t v_isShared_5622_; uint8_t v_isSharedCheck_5626_; 
lean_dec_ref(v_b_5500_);
lean_dec_ref(v_a_5499_);
v_a_5619_ = lean_ctor_get(v___x_5513_, 0);
v_isSharedCheck_5626_ = !lean_is_exclusive(v___x_5513_);
if (v_isSharedCheck_5626_ == 0)
{
v___x_5621_ = v___x_5513_;
v_isShared_5622_ = v_isSharedCheck_5626_;
goto v_resetjp_5620_;
}
else
{
lean_inc(v_a_5619_);
lean_dec(v___x_5513_);
v___x_5621_ = lean_box(0);
v_isShared_5622_ = v_isSharedCheck_5626_;
goto v_resetjp_5620_;
}
v_resetjp_5620_:
{
lean_object* v___x_5624_; 
if (v_isShared_5622_ == 0)
{
v___x_5624_ = v___x_5621_;
goto v_reusejp_5623_;
}
else
{
lean_object* v_reuseFailAlloc_5625_; 
v_reuseFailAlloc_5625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5625_, 0, v_a_5619_);
v___x_5624_ = v_reuseFailAlloc_5625_;
goto v_reusejp_5623_;
}
v_reusejp_5623_:
{
return v___x_5624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq___boxed(lean_object* v_a_5627_, lean_object* v_b_5628_, lean_object* v_a_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_, lean_object* v_a_5638_, lean_object* v_a_5639_, lean_object* v_a_5640_){
_start:
{
lean_object* v_res_5641_; 
v_res_5641_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5627_, v_b_5628_, v_a_5629_, v_a_5630_, v_a_5631_, v_a_5632_, v_a_5633_, v_a_5634_, v_a_5635_, v_a_5636_, v_a_5637_, v_a_5638_, v_a_5639_);
lean_dec(v_a_5639_);
lean_dec_ref(v_a_5638_);
lean_dec(v_a_5637_);
lean_dec_ref(v_a_5636_);
lean_dec(v_a_5635_);
lean_dec_ref(v_a_5634_);
lean_dec(v_a_5633_);
lean_dec_ref(v_a_5632_);
lean_dec(v_a_5631_);
lean_dec(v_a_5630_);
lean_dec(v_a_5629_);
return v_res_5641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(lean_object* v_a_5642_, lean_object* v_b_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_){
_start:
{
lean_object* v___x_5655_; 
v___x_5655_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5642_, v_b_5643_, v_a_5644_, v_a_5652_);
if (lean_obj_tag(v___x_5655_) == 0)
{
lean_object* v_a_5656_; 
v_a_5656_ = lean_ctor_get(v___x_5655_, 0);
lean_inc(v_a_5656_);
lean_dec_ref_known(v___x_5655_, 1);
if (lean_obj_tag(v_a_5656_) == 1)
{
lean_object* v_val_5657_; lean_object* v___x_5658_; 
v_val_5657_ = lean_ctor_get(v_a_5656_, 0);
lean_inc(v_val_5657_);
lean_dec_ref_known(v_a_5656_, 1);
v___x_5658_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5657_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_);
if (lean_obj_tag(v___x_5658_) == 0)
{
lean_object* v_a_5659_; uint8_t v___x_5660_; 
v_a_5659_ = lean_ctor_get(v___x_5658_, 0);
lean_inc(v_a_5659_);
lean_dec_ref_known(v___x_5658_, 1);
v___x_5660_ = lean_unbox(v_a_5659_);
lean_dec(v_a_5659_);
if (v___x_5660_ == 0)
{
lean_object* v___x_5661_; 
v___x_5661_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5642_, v_b_5643_, v_val_5657_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_);
lean_dec(v_val_5657_);
return v___x_5661_;
}
else
{
lean_object* v___x_5662_; 
v___x_5662_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5642_, v_b_5643_, v_val_5657_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_);
lean_dec(v_val_5657_);
return v___x_5662_;
}
}
else
{
lean_object* v_a_5663_; lean_object* v___x_5665_; uint8_t v_isShared_5666_; uint8_t v_isSharedCheck_5670_; 
lean_dec(v_val_5657_);
lean_dec_ref(v_b_5643_);
lean_dec_ref(v_a_5642_);
v_a_5663_ = lean_ctor_get(v___x_5658_, 0);
v_isSharedCheck_5670_ = !lean_is_exclusive(v___x_5658_);
if (v_isSharedCheck_5670_ == 0)
{
v___x_5665_ = v___x_5658_;
v_isShared_5666_ = v_isSharedCheck_5670_;
goto v_resetjp_5664_;
}
else
{
lean_inc(v_a_5663_);
lean_dec(v___x_5658_);
v___x_5665_ = lean_box(0);
v_isShared_5666_ = v_isSharedCheck_5670_;
goto v_resetjp_5664_;
}
v_resetjp_5664_:
{
lean_object* v___x_5668_; 
if (v_isShared_5666_ == 0)
{
v___x_5668_ = v___x_5665_;
goto v_reusejp_5667_;
}
else
{
lean_object* v_reuseFailAlloc_5669_; 
v_reuseFailAlloc_5669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5669_, 0, v_a_5663_);
v___x_5668_ = v_reuseFailAlloc_5669_;
goto v_reusejp_5667_;
}
v_reusejp_5667_:
{
return v___x_5668_;
}
}
}
}
else
{
lean_object* v___x_5671_; 
lean_dec(v_a_5656_);
v___x_5671_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5642_, v_b_5643_, v_a_5644_, v_a_5652_);
if (lean_obj_tag(v___x_5671_) == 0)
{
lean_object* v_a_5672_; lean_object* v___x_5674_; uint8_t v_isShared_5675_; uint8_t v_isSharedCheck_5682_; 
v_a_5672_ = lean_ctor_get(v___x_5671_, 0);
v_isSharedCheck_5682_ = !lean_is_exclusive(v___x_5671_);
if (v_isSharedCheck_5682_ == 0)
{
v___x_5674_ = v___x_5671_;
v_isShared_5675_ = v_isSharedCheck_5682_;
goto v_resetjp_5673_;
}
else
{
lean_inc(v_a_5672_);
lean_dec(v___x_5671_);
v___x_5674_ = lean_box(0);
v_isShared_5675_ = v_isSharedCheck_5682_;
goto v_resetjp_5673_;
}
v_resetjp_5673_:
{
if (lean_obj_tag(v_a_5672_) == 1)
{
lean_object* v_val_5676_; lean_object* v___x_5677_; 
lean_del_object(v___x_5674_);
v_val_5676_ = lean_ctor_get(v_a_5672_, 0);
lean_inc(v_val_5676_);
lean_dec_ref_known(v_a_5672_, 1);
v___x_5677_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5642_, v_b_5643_, v_val_5676_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_);
lean_dec(v_val_5676_);
return v___x_5677_;
}
else
{
lean_object* v___x_5678_; lean_object* v___x_5680_; 
lean_dec(v_a_5672_);
lean_dec_ref(v_b_5643_);
lean_dec_ref(v_a_5642_);
v___x_5678_ = lean_box(0);
if (v_isShared_5675_ == 0)
{
lean_ctor_set(v___x_5674_, 0, v___x_5678_);
v___x_5680_ = v___x_5674_;
goto v_reusejp_5679_;
}
else
{
lean_object* v_reuseFailAlloc_5681_; 
v_reuseFailAlloc_5681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5681_, 0, v___x_5678_);
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
else
{
lean_object* v_a_5683_; lean_object* v___x_5685_; uint8_t v_isShared_5686_; uint8_t v_isSharedCheck_5690_; 
lean_dec_ref(v_b_5643_);
lean_dec_ref(v_a_5642_);
v_a_5683_ = lean_ctor_get(v___x_5671_, 0);
v_isSharedCheck_5690_ = !lean_is_exclusive(v___x_5671_);
if (v_isSharedCheck_5690_ == 0)
{
v___x_5685_ = v___x_5671_;
v_isShared_5686_ = v_isSharedCheck_5690_;
goto v_resetjp_5684_;
}
else
{
lean_inc(v_a_5683_);
lean_dec(v___x_5671_);
v___x_5685_ = lean_box(0);
v_isShared_5686_ = v_isSharedCheck_5690_;
goto v_resetjp_5684_;
}
v_resetjp_5684_:
{
lean_object* v___x_5688_; 
if (v_isShared_5686_ == 0)
{
v___x_5688_ = v___x_5685_;
goto v_reusejp_5687_;
}
else
{
lean_object* v_reuseFailAlloc_5689_; 
v_reuseFailAlloc_5689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5689_, 0, v_a_5683_);
v___x_5688_ = v_reuseFailAlloc_5689_;
goto v_reusejp_5687_;
}
v_reusejp_5687_:
{
return v___x_5688_;
}
}
}
}
}
else
{
lean_object* v_a_5691_; lean_object* v___x_5693_; uint8_t v_isShared_5694_; uint8_t v_isSharedCheck_5698_; 
lean_dec_ref(v_b_5643_);
lean_dec_ref(v_a_5642_);
v_a_5691_ = lean_ctor_get(v___x_5655_, 0);
v_isSharedCheck_5698_ = !lean_is_exclusive(v___x_5655_);
if (v_isSharedCheck_5698_ == 0)
{
v___x_5693_ = v___x_5655_;
v_isShared_5694_ = v_isSharedCheck_5698_;
goto v_resetjp_5692_;
}
else
{
lean_inc(v_a_5691_);
lean_dec(v___x_5655_);
v___x_5693_ = lean_box(0);
v_isShared_5694_ = v_isSharedCheck_5698_;
goto v_resetjp_5692_;
}
v_resetjp_5692_:
{
lean_object* v___x_5696_; 
if (v_isShared_5694_ == 0)
{
v___x_5696_ = v___x_5693_;
goto v_reusejp_5695_;
}
else
{
lean_object* v_reuseFailAlloc_5697_; 
v_reuseFailAlloc_5697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5697_, 0, v_a_5691_);
v___x_5696_ = v_reuseFailAlloc_5697_;
goto v_reusejp_5695_;
}
v_reusejp_5695_:
{
return v___x_5696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed(lean_object* v_a_5699_, lean_object* v_b_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_, lean_object* v_a_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_){
_start:
{
lean_object* v_res_5712_; 
v_res_5712_ = l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(v_a_5699_, v_b_5700_, v_a_5701_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_);
lean_dec(v_a_5710_);
lean_dec_ref(v_a_5709_);
lean_dec(v_a_5708_);
lean_dec_ref(v_a_5707_);
lean_dec(v_a_5706_);
lean_dec_ref(v_a_5705_);
lean_dec(v_a_5704_);
lean_dec_ref(v_a_5703_);
lean_dec(v_a_5702_);
lean_dec(v_a_5701_);
return v_res_5712_;
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
