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
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_Lean_Meta_Grind_Arith_Linear_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs(lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_div(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
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
lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_17_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_18_ = lean_int_dec_eq(v_k_3_, v___x_17_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_21_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_a_20_);
lean_dec_ref_known(v___x_19_, 1);
v___x_21_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_);
if (lean_obj_tag(v___x_21_) == 0)
{
lean_object* v_a_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_40_; 
v_a_22_ = lean_ctor_get(v___x_21_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_40_ == 0)
{
v___x_24_ = v___x_21_;
v_isShared_25_ = v_isSharedCheck_40_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_a_22_);
lean_dec(v___x_21_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_40_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v_vars_26_; lean_object* v_zsmulFn_27_; lean_object* v_size_28_; lean_object* v___x_29_; lean_object* v___y_31_; lean_object* v___x_36_; uint8_t v___x_37_; 
v_vars_26_ = lean_ctor_get(v_a_22_, 30);
lean_inc_ref(v_vars_26_);
lean_dec(v_a_22_);
v_zsmulFn_27_ = lean_ctor_get(v_a_20_, 23);
lean_inc_ref(v_zsmulFn_27_);
lean_dec(v_a_20_);
v_size_28_ = lean_ctor_get(v_vars_26_, 2);
v___x_29_ = l_Lean_mkIntLit(v_k_3_);
v___x_36_ = l_Lean_instInhabitedExpr;
v___x_37_ = lean_nat_dec_lt(v_x_4_, v_size_28_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; 
lean_dec_ref(v_vars_26_);
v___x_38_ = l_outOfBounds___redArg(v___x_36_);
v___y_31_ = v___x_38_;
goto v___jp_30_;
}
else
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_PersistentArray_get_x21___redArg(v___x_36_, v_vars_26_, v_x_4_);
lean_dec_ref(v_vars_26_);
v___y_31_ = v___x_39_;
goto v___jp_30_;
}
v___jp_30_:
{
lean_object* v___x_32_; lean_object* v___x_34_; 
v___x_32_ = l_Lean_mkAppB(v_zsmulFn_27_, v___x_29_, v___y_31_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 0, v___x_32_);
v___x_34_ = v___x_24_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v___x_32_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
}
else
{
lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_48_; 
lean_dec(v_a_20_);
v_a_41_ = lean_ctor_get(v___x_21_, 0);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_48_ == 0)
{
v___x_43_ = v___x_21_;
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_dec(v___x_21_);
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
v_a_49_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_56_ == 0)
{
v___x_51_ = v___x_19_;
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_a_49_);
lean_dec(v___x_19_);
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
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_74_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_74_ == 0)
{
v___x_60_ = v___x_57_;
v_isShared_61_ = v_isSharedCheck_74_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_57_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_74_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v_vars_62_; lean_object* v_size_63_; lean_object* v___x_64_; uint8_t v___x_65_; 
v_vars_62_ = lean_ctor_get(v_a_58_, 30);
lean_inc_ref(v_vars_62_);
lean_dec(v_a_58_);
v_size_63_ = lean_ctor_get(v_vars_62_, 2);
v___x_64_ = l_Lean_instInhabitedExpr;
v___x_65_ = lean_nat_dec_lt(v_x_4_, v_size_63_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; lean_object* v___x_68_; 
lean_dec_ref(v_vars_62_);
v___x_66_ = l_outOfBounds___redArg(v___x_64_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v___x_66_);
v___x_68_ = v___x_60_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_66_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
else
{
lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_70_ = l_Lean_PersistentArray_get_x21___redArg(v___x_64_, v_vars_62_, v_x_4_);
lean_dec_ref(v_vars_62_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v___x_70_);
v___x_72_ = v___x_60_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
v_a_75_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_57_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_57_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__1(lean_object* v_p_98_, lean_object* v_acc_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__1___boxed(lean_object* v_p_131_, lean_object* v_acc_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__1(v_p_131_, v_acc_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec(v___y_134_);
lean_dec(v___y_133_);
lean_dec(v_p_131_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(lean_object* v_p_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
if (lean_obj_tag(v_p_146_) == 0)
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_168_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_168_ == 0)
{
v___x_162_ = v___x_159_;
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v_zero_164_; lean_object* v___x_166_; 
v_zero_164_ = lean_ctor_get(v_a_160_, 17);
lean_inc_ref(v_zero_164_);
lean_dec(v_a_160_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v_zero_164_);
v___x_166_ = v___x_162_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_zero_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
v_a_169_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_159_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_159_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_169_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
else
{
lean_object* v_k_177_; lean_object* v_v_178_; lean_object* v_p_179_; lean_object* v___x_180_; 
v_k_177_ = lean_ctor_get(v_p_146_, 0);
v_v_178_ = lean_ctor_get(v_p_146_, 1);
v_p_179_ = lean_ctor_get(v_p_146_, 2);
v___x_180_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0(v_k_177_, v_v_178_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_182_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_181_);
lean_dec_ref_known(v___x_180_, 1);
v___x_182_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__1(v_p_179_, v_a_181_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
return v___x_182_;
}
else
{
return v___x_180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0___boxed(lean_object* v_p_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec(v___y_185_);
lean_dec(v___y_184_);
lean_dec(v_p_183_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3(lean_object* v_a_200_, lean_object* v_b_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_230_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_230_ == 0)
{
v___x_217_ = v___x_214_;
v_isShared_218_ = v_isSharedCheck_230_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_214_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_230_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v_type_219_; lean_object* v_u_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v_type_219_ = lean_ctor_get(v_a_215_, 2);
lean_inc_ref(v_type_219_);
v_u_220_ = lean_ctor_get(v_a_215_, 3);
lean_inc(v_u_220_);
lean_dec(v_a_215_);
v___x_221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3___closed__1));
v___x_222_ = l_Lean_Level_succ___override(v_u_220_);
v___x_223_ = lean_box(0);
v___x_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v___x_225_ = l_Lean_mkConst(v___x_221_, v___x_224_);
v___x_226_ = l_Lean_mkApp3(v___x_225_, v_type_219_, v_a_200_, v_b_201_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_226_);
v___x_228_ = v___x_217_;
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
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_dec_ref(v_b_201_);
lean_dec_ref(v_a_200_);
v_a_231_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_214_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_214_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3___boxed(lean_object* v_a_239_, lean_object* v_b_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3(v_a_239_, v_b_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec(v___y_242_);
lean_dec(v___y_241_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(lean_object* v_c_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_p_267_; lean_object* v___x_268_; 
v_p_267_ = lean_ctor_get(v_c_254_, 0);
v___x_268_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_267_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_270_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_a_269_);
lean_dec_ref_known(v___x_268_, 1);
v___x_270_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v_ofNatZero_272_; lean_object* v___x_273_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref_known(v___x_270_, 1);
v_ofNatZero_272_ = lean_ctor_get(v_a_271_, 18);
lean_inc_ref(v_ofNatZero_272_);
lean_dec(v_a_271_);
v___x_273_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3(v_a_269_, v_ofNatZero_272_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
return v___x_273_;
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec(v_a_269_);
v_a_274_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_270_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_270_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
else
{
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1___boxed(lean_object* v_c_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v_c_282_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(lean_object* v_msgData_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_302_; lean_object* v_env_303_; lean_object* v___x_304_; lean_object* v_mctx_305_; lean_object* v_lctx_306_; lean_object* v_options_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_302_ = lean_st_ref_get(v___y_300_);
v_env_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc_ref(v_env_303_);
lean_dec(v___x_302_);
v___x_304_ = lean_st_ref_get(v___y_298_);
v_mctx_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc_ref(v_mctx_305_);
lean_dec(v___x_304_);
v_lctx_306_ = lean_ctor_get(v___y_297_, 2);
v_options_307_ = lean_ctor_get(v___y_299_, 2);
lean_inc_ref(v_options_307_);
lean_inc_ref(v_lctx_306_);
v___x_308_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_308_, 0, v_env_303_);
lean_ctor_set(v___x_308_, 1, v_mctx_305_);
lean_ctor_set(v___x_308_, 2, v_lctx_306_);
lean_ctor_set(v___x_308_, 3, v_options_307_);
v___x_309_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v_msgData_296_);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5___boxed(lean_object* v_msgData_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msgData_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
return v_res_317_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_318_; double v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_float_of_nat(v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(lean_object* v_cls_323_, lean_object* v_msg_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_ref_330_; lean_object* v___x_331_; lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_376_; 
v_ref_330_ = lean_ctor_get(v___y_327_, 5);
v___x_331_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msg_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_376_ == 0)
{
v___x_334_ = v___x_331_;
v_isShared_335_ = v_isSharedCheck_376_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_376_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v_traceState_337_; lean_object* v_env_338_; lean_object* v_nextMacroScope_339_; lean_object* v_ngen_340_; lean_object* v_auxDeclNGen_341_; lean_object* v_cache_342_; lean_object* v_messages_343_; lean_object* v_infoState_344_; lean_object* v_snapshotTasks_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_375_; 
v___x_336_ = lean_st_ref_take(v___y_328_);
v_traceState_337_ = lean_ctor_get(v___x_336_, 4);
v_env_338_ = lean_ctor_get(v___x_336_, 0);
v_nextMacroScope_339_ = lean_ctor_get(v___x_336_, 1);
v_ngen_340_ = lean_ctor_get(v___x_336_, 2);
v_auxDeclNGen_341_ = lean_ctor_get(v___x_336_, 3);
v_cache_342_ = lean_ctor_get(v___x_336_, 5);
v_messages_343_ = lean_ctor_get(v___x_336_, 6);
v_infoState_344_ = lean_ctor_get(v___x_336_, 7);
v_snapshotTasks_345_ = lean_ctor_get(v___x_336_, 8);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_375_ == 0)
{
v___x_347_ = v___x_336_;
v_isShared_348_ = v_isSharedCheck_375_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_snapshotTasks_345_);
lean_inc(v_infoState_344_);
lean_inc(v_messages_343_);
lean_inc(v_cache_342_);
lean_inc(v_traceState_337_);
lean_inc(v_auxDeclNGen_341_);
lean_inc(v_ngen_340_);
lean_inc(v_nextMacroScope_339_);
lean_inc(v_env_338_);
lean_dec(v___x_336_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_375_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
uint64_t v_tid_349_; lean_object* v_traces_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_374_; 
v_tid_349_ = lean_ctor_get_uint64(v_traceState_337_, sizeof(void*)*1);
v_traces_350_ = lean_ctor_get(v_traceState_337_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v_traceState_337_);
if (v_isSharedCheck_374_ == 0)
{
v___x_352_ = v_traceState_337_;
v_isShared_353_ = v_isSharedCheck_374_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_traces_350_);
lean_dec(v_traceState_337_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_374_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; double v___x_355_; uint8_t v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_354_ = lean_box(0);
v___x_355_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0);
v___x_356_ = 0;
v___x_357_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__1));
v___x_358_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_358_, 0, v_cls_323_);
lean_ctor_set(v___x_358_, 1, v___x_354_);
lean_ctor_set(v___x_358_, 2, v___x_357_);
lean_ctor_set_float(v___x_358_, sizeof(void*)*3, v___x_355_);
lean_ctor_set_float(v___x_358_, sizeof(void*)*3 + 8, v___x_355_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*3 + 16, v___x_356_);
v___x_359_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__2));
v___x_360_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v_a_332_);
lean_ctor_set(v___x_360_, 2, v___x_359_);
lean_inc(v_ref_330_);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v_ref_330_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = l_Lean_PersistentArray_push___redArg(v_traces_350_, v___x_361_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_362_);
v___x_364_ = v___x_352_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_362_);
lean_ctor_set_uint64(v_reuseFailAlloc_373_, sizeof(void*)*1, v_tid_349_);
v___x_364_ = v_reuseFailAlloc_373_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_366_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 4, v___x_364_);
v___x_366_ = v___x_347_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_env_338_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_nextMacroScope_339_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_ngen_340_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v_auxDeclNGen_341_);
lean_ctor_set(v_reuseFailAlloc_372_, 4, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_372_, 5, v_cache_342_);
lean_ctor_set(v_reuseFailAlloc_372_, 6, v_messages_343_);
lean_ctor_set(v_reuseFailAlloc_372_, 7, v_infoState_344_);
lean_ctor_set(v_reuseFailAlloc_372_, 8, v_snapshotTasks_345_);
v___x_366_ = v_reuseFailAlloc_372_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_367_ = lean_st_ref_set(v___y_328_, v___x_366_);
v___x_368_ = lean_box(0);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_368_);
v___x_370_ = v___x_334_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___boxed(lean_object* v_cls_377_, lean_object* v_msg_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_377_, v_msg_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_384_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_399_ = l_Lean_Name_append(v___x_398_, v___x_397_);
return v___x_399_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8));
v___x_402_ = l_Lean_stringToMessageData(v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(lean_object* v_p_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_539_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_539_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_539_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_539_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
if (lean_obj_tag(v_a_417_) == 1)
{
lean_object* v_val_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_534_; 
v_val_421_ = lean_ctor_get(v_a_417_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v_a_417_);
if (v_isSharedCheck_534_ == 0)
{
v___x_423_ = v_a_417_;
v_isShared_424_ = v_isSharedCheck_534_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_val_421_);
lean_dec(v_a_417_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_534_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v_snd_425_; lean_object* v_snd_426_; lean_object* v_options_427_; lean_object* v_fst_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_532_; 
v_snd_425_ = lean_ctor_get(v_val_421_, 1);
lean_inc(v_snd_425_);
v_snd_426_ = lean_ctor_get(v_snd_425_, 1);
lean_inc(v_snd_426_);
v_options_427_ = lean_ctor_get(v_a_413_, 2);
v_fst_428_ = lean_ctor_get(v_val_421_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v_val_421_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; 
v_unused_533_ = lean_ctor_get(v_val_421_, 1);
lean_dec(v_unused_533_);
v___x_430_ = v_val_421_;
v_isShared_431_ = v_isSharedCheck_532_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_fst_428_);
lean_dec(v_val_421_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_532_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v_fst_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_530_; 
v_fst_432_ = lean_ctor_get(v_snd_425_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v_snd_425_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; 
v_unused_531_ = lean_ctor_get(v_snd_425_, 1);
lean_dec(v_unused_531_);
v___x_434_ = v_snd_425_;
v_isShared_435_ = v_isSharedCheck_530_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_fst_432_);
lean_dec(v_snd_425_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_530_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v_p_436_; lean_object* v_inheritedTraceOptions_437_; uint8_t v_hasTrace_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_p_436_ = lean_ctor_get(v_snd_426_, 0);
v_inheritedTraceOptions_437_ = lean_ctor_get(v_a_413_, 13);
v_hasTrace_438_ = lean_ctor_get_uint8(v_options_427_, sizeof(void*)*1);
v___x_439_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_436_, v_fst_432_);
lean_inc(v_p_403_);
v___x_440_ = l_Lean_Grind_Linarith_Poly_mul(v_p_403_, v___x_439_);
v___x_441_ = lean_int_neg(v_fst_428_);
lean_inc(v_p_436_);
v___x_442_ = l_Lean_Grind_Linarith_Poly_mul(v_p_436_, v___x_441_);
lean_dec(v___x_441_);
v___x_443_ = l_Lean_Grind_Linarith_Poly_combine(v___x_440_, v___x_442_);
if (v_hasTrace_438_ == 0)
{
lean_dec(v___x_439_);
lean_dec(v_fst_428_);
lean_dec(v_p_403_);
goto v___jp_444_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_458_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_459_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_437_, v_options_427_, v___x_458_);
if (v___x_459_ == 0)
{
lean_dec(v___x_439_);
lean_dec(v_fst_428_);
lean_dec(v_p_403_);
goto v___jp_444_;
}
else
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
lean_dec(v_p_403_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_462_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_460_, 1);
v___x_462_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_432_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
v___x_464_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_426_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_466_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 1);
v___x_466_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v___x_443_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_467_);
lean_dec_ref_known(v___x_466_, 1);
v___x_468_ = l_Lean_MessageData_ofExpr(v_a_461_);
v___x_469_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_468_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = l_Int_repr(v_fst_428_);
lean_dec(v_fst_428_);
v___x_472_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
v___x_473_ = l_Lean_MessageData_ofFormat(v___x_472_);
v___x_474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_470_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
lean_ctor_set(v___x_475_, 1, v___x_469_);
v___x_476_ = l_Lean_MessageData_ofExpr(v_a_463_);
v___x_477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v___x_469_);
v___x_479_ = l_Lean_MessageData_ofExpr(v_a_465_);
v___x_480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_478_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
v___x_481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_469_);
v___x_482_ = l_Int_repr(v___x_439_);
lean_dec(v___x_439_);
v___x_483_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
v___x_484_ = l_Lean_MessageData_ofFormat(v___x_483_);
v___x_485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_481_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___x_469_);
v___x_487_ = l_Lean_MessageData_ofExpr(v_a_467_);
v___x_488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_457_, v___x_488_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_dec_ref_known(v___x_489_, 1);
goto v___jp_444_;
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v___x_443_);
lean_del_object(v___x_434_);
lean_dec(v_fst_432_);
lean_del_object(v___x_430_);
lean_dec(v_snd_426_);
lean_del_object(v___x_423_);
lean_del_object(v___x_419_);
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec(v_a_465_);
lean_dec(v_a_463_);
lean_dec(v_a_461_);
lean_dec(v___x_443_);
lean_dec(v___x_439_);
lean_del_object(v___x_434_);
lean_dec(v_fst_432_);
lean_del_object(v___x_430_);
lean_dec(v_fst_428_);
lean_dec(v_snd_426_);
lean_del_object(v___x_423_);
lean_del_object(v___x_419_);
v_a_498_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_466_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_466_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_dec(v_a_463_);
lean_dec(v_a_461_);
lean_dec(v___x_443_);
lean_dec(v___x_439_);
lean_del_object(v___x_434_);
lean_dec(v_fst_432_);
lean_del_object(v___x_430_);
lean_dec(v_fst_428_);
lean_dec(v_snd_426_);
lean_del_object(v___x_423_);
lean_del_object(v___x_419_);
v_a_506_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_464_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_464_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec(v_a_461_);
lean_dec(v___x_443_);
lean_dec(v___x_439_);
lean_del_object(v___x_434_);
lean_dec(v_fst_432_);
lean_del_object(v___x_430_);
lean_dec(v_fst_428_);
lean_dec(v_snd_426_);
lean_del_object(v___x_423_);
lean_del_object(v___x_419_);
v_a_514_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_462_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_462_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec(v___x_443_);
lean_dec(v___x_439_);
lean_del_object(v___x_434_);
lean_dec(v_fst_432_);
lean_del_object(v___x_430_);
lean_dec(v_fst_428_);
lean_dec(v_snd_426_);
lean_del_object(v___x_423_);
lean_del_object(v___x_419_);
v_a_522_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_460_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_460_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
v___jp_444_:
{
lean_object* v___x_446_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v___x_443_);
lean_ctor_set(v___x_434_, 0, v_snd_426_);
v___x_446_ = v___x_434_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_snd_426_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v___x_443_);
v___x_446_ = v_reuseFailAlloc_456_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_448_; 
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v___x_446_);
lean_ctor_set(v___x_430_, 0, v_fst_432_);
v___x_448_ = v___x_430_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_fst_432_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v___x_446_);
v___x_448_ = v_reuseFailAlloc_455_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_450_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_448_);
v___x_450_ = v___x_423_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_448_);
v___x_450_ = v_reuseFailAlloc_454_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_452_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_450_);
v___x_452_ = v___x_419_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
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
lean_object* v___x_535_; lean_object* v___x_537_; 
lean_dec(v_a_417_);
lean_dec(v_p_403_);
v___x_535_ = lean_box(0);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_535_);
v___x_537_ = v___x_419_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_p_403_);
v_a_540_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_416_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_416_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___boxed(lean_object* v_p_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec(v_a_550_);
lean_dec(v_a_549_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(lean_object* v_cls_562_, lean_object* v_msg_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_562_, v_msg_563_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___boxed(lean_object* v_cls_577_, lean_object* v_msg_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_cls_577_, v_msg_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec(v___y_580_);
lean_dec(v___y_579_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(lean_object* v_c_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_p_605_; lean_object* v___x_606_; 
v_p_605_ = lean_ctor_get(v_c_592_, 0);
v___x_606_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_605_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_608_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref_known(v___x_606_, 1);
v___x_608_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v_ofNatZero_610_; lean_object* v___x_611_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref_known(v___x_608_, 1);
v_ofNatZero_610_ = lean_ctor_get(v_a_609_, 18);
lean_inc_ref(v_ofNatZero_610_);
lean_dec(v_a_609_);
v___x_611_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3(v_a_607_, v_ofNatZero_610_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_620_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_620_ == 0)
{
v___x_614_ = v___x_611_;
v_isShared_615_ = v_isSharedCheck_620_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_611_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_620_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_616_ = l_Lean_mkNot(v_a_612_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_616_);
v___x_618_ = v___x_614_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
else
{
return v___x_611_;
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec(v_a_607_);
v_a_621_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_608_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_608_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
else
{
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0___boxed(lean_object* v_c_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v_c_629_);
return v_res_642_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_nat_to_int(v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2(void){
_start:
{
lean_object* v_cls_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_cls_649_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_651_ = l_Lean_Name_append(v___x_650_, v_cls_649_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(lean_object* v_a_652_, lean_object* v_x_653_, lean_object* v_c_u2081_654_, lean_object* v_b_655_, lean_object* v_c_u2082_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v_options_723_; uint8_t v_hasTrace_724_; 
v_options_723_ = lean_ctor_get(v_a_666_, 2);
v_hasTrace_724_ = lean_ctor_get_uint8(v_options_723_, sizeof(void*)*1);
if (v_hasTrace_724_ == 0)
{
v___y_670_ = v_a_657_;
v___y_671_ = v_a_658_;
v___y_672_ = v_a_659_;
v___y_673_ = v_a_660_;
v___y_674_ = v_a_661_;
v___y_675_ = v_a_662_;
v___y_676_ = v_a_663_;
v___y_677_ = v_a_664_;
v___y_678_ = v_a_665_;
v___y_679_ = v_a_666_;
v___y_680_ = v_a_667_;
goto v___jp_669_;
}
else
{
lean_object* v_inheritedTraceOptions_725_; lean_object* v_cls_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_inheritedTraceOptions_725_ = lean_ctor_get(v_a_666_, 13);
v_cls_726_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_727_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2);
v___x_728_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_725_, v_options_723_, v___x_727_);
if (v___x_728_ == 0)
{
v___y_670_ = v_a_657_;
v___y_671_ = v_a_658_;
v___y_672_ = v_a_659_;
v___y_673_ = v_a_660_;
v___y_674_ = v_a_661_;
v___y_675_ = v_a_662_;
v___y_676_ = v_a_663_;
v___y_677_ = v_a_664_;
v___y_678_ = v_a_665_;
v___y_679_ = v_a_666_;
v___y_680_ = v_a_667_;
goto v___jp_669_;
}
else
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_653_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_731_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
v___x_731_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_654_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_733_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref_known(v___x_731_, 1);
v___x_733_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_u2082_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = l_Lean_MessageData_ofExpr(v_a_730_);
v___x_736_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_735_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = l_Lean_MessageData_ofExpr(v_a_732_);
v___x_739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v___x_736_);
v___x_741_ = l_Lean_MessageData_ofExpr(v_a_734_);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_726_, v___x_742_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_dec_ref_known(v___x_743_, 1);
v___y_670_ = v_a_657_;
v___y_671_ = v_a_658_;
v___y_672_ = v_a_659_;
v___y_673_ = v_a_660_;
v___y_674_ = v_a_661_;
v___y_675_ = v_a_662_;
v___y_676_ = v_a_663_;
v___y_677_ = v_a_664_;
v___y_678_ = v_a_665_;
v___y_679_ = v_a_666_;
v___y_680_ = v_a_667_;
goto v___jp_669_;
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec_ref(v_c_u2082_656_);
lean_dec(v_b_655_);
lean_dec_ref(v_c_u2081_654_);
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec(v_a_732_);
lean_dec(v_a_730_);
lean_dec_ref(v_c_u2082_656_);
lean_dec(v_b_655_);
lean_dec_ref(v_c_u2081_654_);
v_a_752_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_733_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_733_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec(v_a_730_);
lean_dec_ref(v_c_u2082_656_);
lean_dec(v_b_655_);
lean_dec_ref(v_c_u2081_654_);
v_a_760_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_731_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_731_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec_ref(v_c_u2082_656_);
lean_dec(v_b_655_);
lean_dec_ref(v_c_u2081_654_);
v_a_768_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_729_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_729_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
v___jp_669_:
{
lean_object* v_p_681_; lean_object* v_p_682_; lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v_p_681_ = lean_ctor_get(v_c_u2081_654_, 0);
v_p_682_ = lean_ctor_get(v_c_u2082_656_, 0);
v___x_683_ = lean_int_emod(v_b_655_, v_a_652_);
v___x_684_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_685_ = lean_int_dec_eq(v___x_683_, v___x_684_);
lean_dec(v___x_683_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_706_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_706_ == 0)
{
v___x_689_ = v___x_686_;
v_isShared_690_ = v_isSharedCheck_706_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_686_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_706_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
uint8_t v___x_691_; 
v___x_691_ = lean_unbox(v_a_687_);
lean_dec(v_a_687_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_694_; 
lean_dec_ref(v_c_u2082_656_);
lean_dec(v_b_655_);
lean_dec_ref(v_c_u2081_654_);
v___x_692_ = lean_box(0);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_692_);
v___x_694_ = v___x_689_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
lean_inc(v_p_681_);
v___x_696_ = l_Lean_Grind_Linarith_Poly_mul(v_p_681_, v_b_655_);
v___x_697_ = lean_int_neg(v_a_652_);
lean_inc(v_p_682_);
v___x_698_ = l_Lean_Grind_Linarith_Poly_mul(v_p_682_, v___x_697_);
v___x_699_ = l_Lean_Grind_Linarith_Poly_combine(v___x_696_, v___x_698_);
v___x_700_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_700_, 0, v___x_697_);
lean_ctor_set(v___x_700_, 1, v_b_655_);
lean_ctor_set(v___x_700_, 2, v_c_u2081_654_);
lean_ctor_set(v___x_700_, 3, v_c_u2082_656_);
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_702_);
v___x_704_ = v___x_689_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec_ref(v_c_u2082_656_);
lean_dec(v_b_655_);
lean_dec_ref(v_c_u2081_654_);
v_a_707_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_686_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_686_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_715_ = lean_int_neg(v_b_655_);
lean_dec(v_b_655_);
v___x_716_ = lean_int_ediv(v___x_715_, v_a_652_);
lean_dec(v___x_715_);
lean_inc(v_p_681_);
v___x_717_ = l_Lean_Grind_Linarith_Poly_mul(v_p_681_, v___x_716_);
lean_inc(v_p_682_);
v___x_718_ = l_Lean_Grind_Linarith_Poly_combine(v___x_717_, v_p_682_);
v___x_719_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_719_, 0, v___x_716_);
lean_ctor_set(v___x_719_, 1, v_c_u2081_654_);
lean_ctor_set(v___x_719_, 2, v_c_u2082_656_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___boxed(lean_object** _args){
lean_object* v_a_776_ = _args[0];
lean_object* v_x_777_ = _args[1];
lean_object* v_c_u2081_778_ = _args[2];
lean_object* v_b_779_ = _args[3];
lean_object* v_c_u2082_780_ = _args[4];
lean_object* v_a_781_ = _args[5];
lean_object* v_a_782_ = _args[6];
lean_object* v_a_783_ = _args[7];
lean_object* v_a_784_ = _args[8];
lean_object* v_a_785_ = _args[9];
lean_object* v_a_786_ = _args[10];
lean_object* v_a_787_ = _args[11];
lean_object* v_a_788_ = _args[12];
lean_object* v_a_789_ = _args[13];
lean_object* v_a_790_ = _args[14];
lean_object* v_a_791_ = _args[15];
lean_object* v_a_792_ = _args[16];
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_776_, v_x_777_, v_c_u2081_778_, v_b_779_, v_c_u2082_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec(v_a_782_);
lean_dec(v_a_781_);
lean_dec(v_x_777_);
lean_dec(v_a_776_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(lean_object* v_a_794_, lean_object* v_b_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_a_794_, v_a_796_, v_a_797_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_828_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_828_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_828_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_828_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
if (lean_obj_tag(v_a_800_) == 1)
{
lean_object* v_val_804_; lean_object* v___x_805_; 
lean_del_object(v___x_802_);
v_val_804_ = lean_ctor_get(v_a_800_, 0);
v___x_805_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_b_795_, v_a_796_, v_a_797_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_823_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_823_ == 0)
{
v___x_808_ = v___x_805_;
v_isShared_809_ = v_isSharedCheck_823_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_823_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
if (lean_obj_tag(v_a_806_) == 1)
{
lean_object* v_val_810_; uint8_t v___x_811_; 
v_val_810_ = lean_ctor_get(v_a_806_, 0);
lean_inc(v_val_810_);
lean_dec_ref_known(v_a_806_, 1);
v___x_811_ = lean_nat_dec_eq(v_val_804_, v_val_810_);
lean_dec(v_val_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; lean_object* v___x_814_; 
lean_dec_ref_known(v_a_800_, 1);
v___x_812_ = lean_box(0);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_812_);
v___x_814_ = v___x_808_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
else
{
lean_object* v___x_817_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v_a_800_);
v___x_817_ = v___x_808_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_800_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
else
{
lean_object* v___x_819_; lean_object* v___x_821_; 
lean_dec(v_a_806_);
lean_dec_ref_known(v_a_800_, 1);
v___x_819_ = lean_box(0);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_819_);
v___x_821_ = v___x_808_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
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
else
{
lean_dec_ref_known(v_a_800_, 1);
return v___x_805_;
}
}
else
{
lean_object* v___x_824_; lean_object* v___x_826_; 
lean_dec(v_a_800_);
v___x_824_ = lean_box(0);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_824_);
v___x_826_ = v___x_802_;
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
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg___boxed(lean_object* v_a_829_, lean_object* v_b_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_829_, v_b_830_, v_a_831_, v_a_832_);
lean_dec_ref(v_a_832_);
lean_dec(v_a_831_);
lean_dec_ref(v_b_830_);
lean_dec_ref(v_a_829_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(lean_object* v_a_835_, lean_object* v_b_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_835_, v_b_836_, v_a_837_, v_a_845_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___boxed(lean_object* v_a_849_, lean_object* v_b_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(v_a_849_, v_b_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
lean_dec(v_a_860_);
lean_dec_ref(v_a_859_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_b_850_);
lean_dec_ref(v_a_849_);
return v_res_862_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_864_ = lean_int_neg(v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(lean_object* v_a_865_, lean_object* v_b_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
uint8_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_879_ = 0;
v___x_880_ = lean_unsigned_to_nat(0u);
v___x_881_ = lean_box(v___x_879_);
lean_inc_ref(v_a_865_);
v___x_882_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_882_, 0, v_a_865_);
lean_closure_set(v___x_882_, 1, v___x_881_);
lean_closure_set(v___x_882_, 2, v___x_880_);
v___x_883_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_882_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_1035_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_1035_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_1035_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
if (lean_obj_tag(v_a_884_) == 1)
{
lean_object* v_val_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
lean_del_object(v___x_886_);
v_val_888_ = lean_ctor_get(v_a_884_, 0);
lean_inc(v_val_888_);
lean_dec_ref_known(v_a_884_, 1);
v___x_889_ = lean_box(v___x_879_);
lean_inc_ref(v_b_866_);
v___x_890_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_890_, 0, v_b_866_);
lean_closure_set(v___x_890_, 1, v___x_889_);
lean_closure_set(v___x_890_, 2, v___x_880_);
v___x_891_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_890_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_1022_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_1022_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_1022_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
if (lean_obj_tag(v_a_892_) == 1)
{
lean_object* v_val_896_; lean_object* v___x_897_; 
lean_del_object(v___x_894_);
v_val_896_ = lean_ctor_get(v_a_892_, 0);
lean_inc(v_val_896_);
lean_dec_ref_known(v_a_892_, 1);
v___x_897_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_865_, v_a_868_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_899_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
v___x_899_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_866_, v_a_868_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___y_902_; uint8_t v___x_1001_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
v___x_1001_ = lean_nat_dec_le(v_a_898_, v_a_900_);
if (v___x_1001_ == 0)
{
lean_dec(v_a_900_);
v___y_902_ = v_a_898_;
goto v___jp_901_;
}
else
{
lean_dec(v_a_898_);
v___y_902_ = v_a_900_;
goto v___jp_901_;
}
v___jp_901_:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
lean_inc(v_val_896_);
lean_inc(v_val_888_);
v___x_903_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_903_, 0, v_val_888_);
lean_ctor_set(v___x_903_, 1, v_val_896_);
v___x_904_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_903_);
v___x_905_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_905_, 0, v_a_865_);
lean_ctor_set(v___x_905_, 1, v_b_866_);
lean_ctor_set(v___x_905_, 2, v_val_888_);
lean_ctor_set(v___x_905_, 3, v_val_896_);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(v___x_906_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v_p_909_; lean_object* v___x_910_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v___x_907_, 1);
v_p_909_ = lean_ctor_get(v_a_908_, 0);
lean_inc(v___y_902_);
lean_inc_ref(v_p_909_);
v___x_910_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_909_, v___y_902_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_912_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_910_, 1);
lean_inc(v___y_902_);
v___x_912_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_911_, v___x_879_, v___y_902_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_976_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_976_ == 0)
{
v___x_915_ = v___x_912_;
v_isShared_916_ = v_isSharedCheck_976_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_912_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_976_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
if (lean_obj_tag(v_a_913_) == 1)
{
lean_object* v_val_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v_val_917_ = lean_ctor_get(v_a_913_, 0);
lean_inc_n(v_val_917_, 2);
lean_dec_ref_known(v_a_913_, 1);
v___x_918_ = l_Lean_Grind_Linarith_Expr_norm(v_val_917_);
v___x_919_ = lean_box(0);
v___x_920_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_918_, v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
lean_del_object(v___x_915_);
lean_inc(v_a_908_);
v___x_921_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_921_, 0, v_a_908_);
lean_ctor_set(v___x_921_, 1, v_val_917_);
lean_inc(v___x_918_);
v___x_922_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_922_, 0, v___x_918_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*2, v___x_879_);
v___x_923_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_922_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_966_; 
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; 
v_unused_967_ = lean_ctor_get(v___x_923_, 0);
lean_dec(v_unused_967_);
v___x_925_ = v___x_923_;
v_isShared_926_ = v_isSharedCheck_966_;
goto v_resetjp_924_;
}
else
{
lean_dec(v___x_923_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_966_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_927_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_909_);
v___x_928_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_927_, v_p_909_);
if (v_isShared_926_ == 0)
{
lean_ctor_set_tag(v___x_925_, 1);
lean_ctor_set(v___x_925_, 0, v_a_908_);
v___x_930_ = v___x_925_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_908_);
v___x_930_ = v_reuseFailAlloc_965_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_inc_ref(v___x_928_);
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_928_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
lean_inc(v___y_902_);
v___x_932_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v___x_928_, v___y_902_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_934_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 1);
v___x_934_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_933_, v___x_879_, v___y_902_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_948_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_948_ == 0)
{
v___x_937_ = v___x_934_;
v_isShared_938_ = v_isSharedCheck_948_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_934_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_948_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
if (lean_obj_tag(v_a_935_) == 1)
{
lean_object* v_val_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
lean_del_object(v___x_937_);
v_val_939_ = lean_ctor_get(v_a_935_, 0);
lean_inc(v_val_939_);
lean_dec_ref_known(v_a_935_, 1);
v___x_940_ = l_Lean_Grind_Linarith_Poly_mul(v___x_918_, v___x_927_);
v___x_941_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_931_);
lean_ctor_set(v___x_941_, 1, v_val_939_);
v___x_942_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
lean_ctor_set_uint8(v___x_942_, sizeof(void*)*2, v___x_879_);
v___x_943_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_942_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
return v___x_943_;
}
else
{
lean_object* v___x_944_; lean_object* v___x_946_; 
lean_dec(v_a_935_);
lean_dec_ref_known(v___x_931_, 2);
lean_dec(v___x_918_);
v___x_944_ = lean_box(0);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_944_);
v___x_946_ = v___x_937_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec_ref_known(v___x_931_, 2);
lean_dec(v___x_918_);
v_a_949_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_934_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_934_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_dec_ref_known(v___x_931_, 2);
lean_dec(v___x_918_);
lean_dec(v___y_902_);
v_a_957_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_932_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_932_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
}
else
{
lean_dec(v___x_918_);
lean_dec(v_a_908_);
lean_dec(v___y_902_);
return v___x_923_;
}
}
else
{
lean_object* v___x_968_; lean_object* v___x_970_; 
lean_dec(v___x_918_);
lean_dec(v_val_917_);
lean_dec(v_a_908_);
lean_dec(v___y_902_);
v___x_968_ = lean_box(0);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_968_);
v___x_970_ = v___x_915_;
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
}
else
{
lean_object* v___x_972_; lean_object* v___x_974_; 
lean_dec(v_a_913_);
lean_dec(v_a_908_);
lean_dec(v___y_902_);
v___x_972_ = lean_box(0);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_972_);
v___x_974_ = v___x_915_;
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
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec(v_a_908_);
lean_dec(v___y_902_);
v_a_977_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_912_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_912_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec(v_a_908_);
lean_dec(v___y_902_);
v_a_985_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_910_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_910_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v___y_902_);
v_a_993_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_907_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_907_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec(v_a_898_);
lean_dec(v_val_896_);
lean_dec(v_val_888_);
lean_dec_ref(v_b_866_);
lean_dec_ref(v_a_865_);
v_a_1002_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_899_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_899_);
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
lean_dec(v_val_896_);
lean_dec(v_val_888_);
lean_dec_ref(v_b_866_);
lean_dec_ref(v_a_865_);
v_a_1010_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_897_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_897_);
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
else
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
lean_dec(v_a_892_);
lean_dec(v_val_888_);
lean_dec_ref(v_b_866_);
lean_dec_ref(v_a_865_);
v___x_1018_ = lean_box(0);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_1018_);
v___x_1020_ = v___x_894_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
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
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v_val_888_);
lean_dec_ref(v_b_866_);
lean_dec_ref(v_a_865_);
v_a_1023_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_891_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_891_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
lean_dec(v_a_884_);
lean_dec_ref(v_b_866_);
lean_dec_ref(v_a_865_);
v___x_1031_ = lean_box(0);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_1031_);
v___x_1033_ = v___x_886_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
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
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec_ref(v_b_866_);
lean_dec_ref(v_a_865_);
v_a_1036_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_883_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_883_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___boxed(lean_object* v_a_1044_, lean_object* v_b_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_1044_, v_b_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec(v_a_1046_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(lean_object* v_a_1059_, lean_object* v_b_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1059_, v_a_1062_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; uint8_t v___x_1075_; lean_object* v___x_1076_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v___x_1075_ = 0;
lean_inc_ref(v_a_1059_);
v___x_1076_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1059_, v___x_1075_, v_a_1074_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1131_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1131_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1131_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
if (lean_obj_tag(v_a_1077_) == 1)
{
lean_object* v_val_1081_; lean_object* v___x_1082_; 
lean_del_object(v___x_1079_);
v_val_1081_ = lean_ctor_get(v_a_1077_, 0);
lean_inc(v_val_1081_);
lean_dec_ref_known(v_a_1077_, 1);
v___x_1082_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1060_, v_a_1062_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1084_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v___x_1082_, 1);
lean_inc_ref(v_b_1060_);
v___x_1084_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_1060_, v___x_1075_, v_a_1083_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
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
lean_inc(v_val_1081_);
v___x_1090_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1090_, 0, v_val_1081_);
lean_ctor_set(v___x_1090_, 1, v_val_1089_);
v___x_1091_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1090_);
v___x_1092_ = lean_box(0);
v___x_1093_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_1091_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_del_object(v___x_1087_);
lean_inc(v_val_1089_);
lean_inc(v_val_1081_);
lean_inc_ref(v_b_1060_);
lean_inc_ref(v_a_1059_);
v___x_1094_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1094_, 0, v_a_1059_);
lean_ctor_set(v___x_1094_, 1, v_b_1060_);
lean_ctor_set(v___x_1094_, 2, v_val_1081_);
lean_ctor_set(v___x_1094_, 3, v_val_1089_);
lean_inc(v___x_1091_);
v___x_1095_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1095_, 0, v___x_1091_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*2, v___x_1075_);
v___x_1096_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1095_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec_ref_known(v___x_1096_, 1);
v___x_1097_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_1098_ = l_Lean_Grind_Linarith_Poly_mul(v___x_1091_, v___x_1097_);
v___x_1099_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1099_, 0, v_b_1060_);
lean_ctor_set(v___x_1099_, 1, v_a_1059_);
lean_ctor_set(v___x_1099_, 2, v_val_1089_);
lean_ctor_set(v___x_1099_, 3, v_val_1081_);
v___x_1100_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
lean_ctor_set_uint8(v___x_1100_, sizeof(void*)*2, v___x_1075_);
v___x_1101_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1100_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
return v___x_1101_;
}
else
{
lean_dec(v___x_1091_);
lean_dec(v_val_1089_);
lean_dec(v_val_1081_);
lean_dec_ref(v_b_1060_);
lean_dec_ref(v_a_1059_);
return v___x_1096_;
}
}
else
{
lean_object* v___x_1102_; lean_object* v___x_1104_; 
lean_dec(v___x_1091_);
lean_dec(v_val_1089_);
lean_dec(v_val_1081_);
lean_dec_ref(v_b_1060_);
lean_dec_ref(v_a_1059_);
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
lean_dec(v_val_1081_);
lean_dec_ref(v_b_1060_);
lean_dec_ref(v_a_1059_);
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
lean_dec(v_val_1081_);
lean_dec_ref(v_b_1060_);
lean_dec_ref(v_a_1059_);
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
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v_val_1081_);
lean_dec_ref(v_b_1060_);
lean_dec_ref(v_a_1059_);
v_a_1119_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1082_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1082_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
else
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
lean_dec(v_a_1077_);
lean_dec_ref(v_b_1060_);
lean_dec_ref(v_a_1059_);
v___x_1127_ = lean_box(0);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1127_);
v___x_1129_ = v___x_1079_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1127_);
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
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec_ref(v_b_1060_);
lean_dec_ref(v_a_1059_);
v_a_1132_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1076_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1076_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec_ref(v_b_1060_);
lean_dec_ref(v_a_1059_);
v_a_1140_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1073_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1073_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27___boxed(lean_object* v_a_1148_, lean_object* v_b_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_1148_, v_b_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec(v_a_1150_);
return v_res_1162_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(lean_object* v_msg_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v___x_1177_; lean_object* v___f_1178_; lean_object* v___x_3370__overap_1179_; lean_object* v___x_1180_; 
v___x_1177_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0);
v___f_1178_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1178_, 0, v___x_1177_);
v___x_3370__overap_1179_ = lean_panic_fn_borrowed(v___f_1178_, v_msg_1164_);
lean_dec_ref(v___f_1178_);
lean_inc(v___y_1175_);
lean_inc_ref(v___y_1174_);
lean_inc(v___y_1173_);
lean_inc_ref(v___y_1172_);
lean_inc(v___y_1171_);
lean_inc_ref(v___y_1170_);
lean_inc(v___y_1169_);
lean_inc_ref(v___y_1168_);
lean_inc(v___y_1167_);
lean_inc(v___y_1166_);
lean_inc(v___y_1165_);
v___x_1180_ = lean_apply_12(v___x_3370__overap_1179_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, lean_box(0));
return v___x_1180_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(lean_object* v_c_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v_c_1222_; lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v_c_1230_; lean_object* v_p_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; uint8_t v___x_1267_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
lean_dec_ref_known(v___x_1227_, 1);
v___x_1267_ = lean_unbox(v_a_1228_);
lean_dec(v_a_1228_);
if (v___x_1267_ == 0)
{
lean_object* v_p_1268_; 
v_p_1268_ = lean_ctor_get(v_c_1206_, 0);
lean_inc(v_p_1268_);
v_c_1230_ = v_c_1206_;
v_p_1231_ = v_p_1268_;
v___y_1232_ = v_a_1207_;
v___y_1233_ = v_a_1208_;
v___y_1234_ = v_a_1209_;
v___y_1235_ = v_a_1210_;
v___y_1236_ = v_a_1211_;
v___y_1237_ = v_a_1212_;
v___y_1238_ = v_a_1213_;
v___y_1239_ = v_a_1214_;
v___y_1240_ = v_a_1215_;
v___y_1241_ = v_a_1216_;
v___y_1242_ = v_a_1217_;
goto v___jp_1229_;
}
else
{
lean_object* v_p_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; uint8_t v___x_1273_; 
v_p_1269_ = lean_ctor_get(v_c_1206_, 0);
v___x_1270_ = l_Lean_Grind_Linarith_Poly_gcdCoeffs(v_p_1269_);
v___x_1271_ = lean_unsigned_to_nat(1u);
v___x_1272_ = lean_nat_dec_eq(v___x_1270_, v___x_1271_);
v___x_1273_ = lean_bool_not(v___x_1272_);
if (v___x_1273_ == 0)
{
lean_inc(v_p_1269_);
lean_dec(v___x_1270_);
v_c_1230_ = v_c_1206_;
v_p_1231_ = v_p_1269_;
v___y_1232_ = v_a_1207_;
v___y_1233_ = v_a_1208_;
v___y_1234_ = v_a_1209_;
v___y_1235_ = v_a_1210_;
v___y_1236_ = v_a_1211_;
v___y_1237_ = v_a_1212_;
v___y_1238_ = v_a_1213_;
v___y_1239_ = v_a_1214_;
v___y_1240_ = v_a_1215_;
v___y_1241_ = v_a_1216_;
v___y_1242_ = v_a_1217_;
goto v___jp_1229_;
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_inc(v___x_1270_);
v___x_1274_ = lean_nat_to_int(v___x_1270_);
lean_inc(v_p_1269_);
v___x_1275_ = l_Lean_Grind_Linarith_Poly_div(v_p_1269_, v___x_1274_);
lean_dec(v___x_1274_);
v___x_1276_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1270_);
lean_ctor_set(v___x_1276_, 1, v_c_1206_);
lean_inc(v___x_1275_);
v___x_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1275_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v_c_1230_ = v___x_1277_;
v_p_1231_ = v___x_1275_;
v___y_1232_ = v_a_1207_;
v___y_1233_ = v_a_1208_;
v___y_1234_ = v_a_1209_;
v___y_1235_ = v_a_1210_;
v___y_1236_ = v_a_1211_;
v___y_1237_ = v_a_1212_;
v___y_1238_ = v_a_1213_;
v___y_1239_ = v_a_1214_;
v___y_1240_ = v_a_1215_;
v___y_1241_ = v_a_1216_;
v___y_1242_ = v_a_1217_;
goto v___jp_1229_;
}
}
v___jp_1229_:
{
lean_object* v___x_1243_; 
lean_inc(v_p_1231_);
v___x_1243_ = l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(v_p_1231_);
if (lean_obj_tag(v___x_1243_) == 1)
{
lean_object* v_val_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1264_; 
v_val_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1264_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_val_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1264_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v_fst_1248_; lean_object* v_snd_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1263_; 
v_fst_1248_ = lean_ctor_get(v_val_1244_, 0);
v_snd_1249_ = lean_ctor_get(v_val_1244_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_val_1244_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1251_ = v_val_1244_;
v_isShared_1252_ = v_isSharedCheck_1263_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_snd_1249_);
lean_inc(v_fst_1248_);
lean_dec(v_val_1244_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1263_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_1254_ = lean_int_dec_lt(v_fst_1248_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_del_object(v___x_1251_);
lean_del_object(v___x_1246_);
lean_dec(v_p_1231_);
v___y_1220_ = v_snd_1249_;
v___y_1221_ = v_fst_1248_;
v_c_1222_ = v_c_1230_;
goto v___jp_1219_;
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1258_; 
v___x_1255_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_1256_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1231_, v___x_1255_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set_tag(v___x_1246_, 3);
lean_ctor_set(v___x_1246_, 0, v_c_1230_);
v___x_1258_ = v___x_1246_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_c_1230_);
v___x_1258_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
lean_object* v___x_1260_; 
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v___x_1258_);
lean_ctor_set(v___x_1251_, 0, v___x_1256_);
v___x_1260_ = v___x_1251_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1256_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
v___y_1220_ = v_snd_1249_;
v___y_1221_ = v_fst_1248_;
v_c_1222_ = v___x_1260_;
goto v___jp_1219_;
}
}
}
}
}
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec(v___x_1243_);
lean_dec(v_p_1231_);
lean_dec_ref(v_c_1230_);
v___x_1265_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3);
v___x_1266_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v___x_1265_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
return v___x_1266_;
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec_ref(v_c_1206_);
v_a_1278_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1227_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1227_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
v___jp_1219_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1223_ = lean_nat_abs(v___y_1221_);
lean_dec(v___y_1221_);
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___y_1220_);
lean_ctor_set(v___x_1224_, 1, v_c_1222_);
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1223_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
}
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
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_1312_){
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
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1317_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_1320_, lean_object* v_ref_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1321_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_1335_, lean_object* v_ref_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(v_00_u03b1_1335_, v_ref_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec(v___y_1337_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(lean_object* v_c_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v_p_1381_; lean_object* v_fileName_1382_; lean_object* v_fileMap_1383_; lean_object* v_options_1384_; lean_object* v_currRecDepth_1385_; lean_object* v_maxRecDepth_1386_; lean_object* v_ref_1387_; lean_object* v_currNamespace_1388_; lean_object* v_openDecls_1389_; lean_object* v_initHeartbeats_1390_; lean_object* v_maxHeartbeats_1391_; lean_object* v_quotContext_1392_; lean_object* v_currMacroScope_1393_; uint8_t v_diag_1394_; lean_object* v_cancelTk_x3f_1395_; uint8_t v_suppressElabErrors_1396_; lean_object* v_inheritedTraceOptions_1397_; uint8_t v___y_1399_; lean_object* v___x_1493_; uint8_t v___x_1494_; uint8_t v___x_1495_; 
v_p_1381_ = lean_ctor_get(v_c_1350_, 0);
v_fileName_1382_ = lean_ctor_get(v_a_1360_, 0);
lean_inc_ref(v_fileName_1382_);
v_fileMap_1383_ = lean_ctor_get(v_a_1360_, 1);
lean_inc_ref(v_fileMap_1383_);
v_options_1384_ = lean_ctor_get(v_a_1360_, 2);
lean_inc_ref(v_options_1384_);
v_currRecDepth_1385_ = lean_ctor_get(v_a_1360_, 3);
lean_inc(v_currRecDepth_1385_);
v_maxRecDepth_1386_ = lean_ctor_get(v_a_1360_, 4);
lean_inc(v_maxRecDepth_1386_);
v_ref_1387_ = lean_ctor_get(v_a_1360_, 5);
lean_inc(v_ref_1387_);
v_currNamespace_1388_ = lean_ctor_get(v_a_1360_, 6);
lean_inc(v_currNamespace_1388_);
v_openDecls_1389_ = lean_ctor_get(v_a_1360_, 7);
lean_inc(v_openDecls_1389_);
v_initHeartbeats_1390_ = lean_ctor_get(v_a_1360_, 8);
lean_inc(v_initHeartbeats_1390_);
v_maxHeartbeats_1391_ = lean_ctor_get(v_a_1360_, 9);
lean_inc(v_maxHeartbeats_1391_);
v_quotContext_1392_ = lean_ctor_get(v_a_1360_, 10);
lean_inc(v_quotContext_1392_);
v_currMacroScope_1393_ = lean_ctor_get(v_a_1360_, 11);
lean_inc(v_currMacroScope_1393_);
v_diag_1394_ = lean_ctor_get_uint8(v_a_1360_, sizeof(void*)*14);
v_cancelTk_x3f_1395_ = lean_ctor_get(v_a_1360_, 12);
lean_inc(v_cancelTk_x3f_1395_);
v_suppressElabErrors_1396_ = lean_ctor_get_uint8(v_a_1360_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1397_ = lean_ctor_get(v_a_1360_, 13);
lean_inc_ref(v_inheritedTraceOptions_1397_);
lean_dec_ref(v_a_1360_);
v___x_1493_ = lean_unsigned_to_nat(0u);
v___x_1494_ = lean_nat_dec_eq(v_maxRecDepth_1386_, v___x_1493_);
v___x_1495_ = lean_bool_not(v___x_1494_);
if (v___x_1495_ == 0)
{
v___y_1399_ = v___x_1495_;
goto v___jp_1398_;
}
else
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_nat_dec_eq(v_currRecDepth_1385_, v_maxRecDepth_1386_);
v___y_1399_ = v___x_1496_;
goto v___jp_1398_;
}
v___jp_1363_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_1378_, 0, v___y_1364_);
lean_ctor_set(v___x_1378_, 1, v___y_1366_);
lean_ctor_set(v___x_1378_, 2, v_c_1350_);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___y_1365_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v_c_1350_ = v___x_1379_;
v_a_1351_ = v___y_1367_;
v_a_1352_ = v___y_1368_;
v_a_1353_ = v___y_1369_;
v_a_1354_ = v___y_1370_;
v_a_1355_ = v___y_1371_;
v_a_1356_ = v___y_1372_;
v_a_1357_ = v___y_1373_;
v_a_1358_ = v___y_1374_;
v_a_1359_ = v___y_1375_;
v_a_1360_ = v___y_1376_;
v_a_1361_ = v___y_1377_;
goto _start;
}
v___jp_1398_:
{
if (v___y_1399_ == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1400_ = lean_unsigned_to_nat(1u);
v___x_1401_ = lean_nat_add(v_currRecDepth_1385_, v___x_1400_);
lean_dec(v_currRecDepth_1385_);
lean_inc_ref(v_inheritedTraceOptions_1397_);
lean_inc_ref(v_options_1384_);
v___x_1402_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1402_, 0, v_fileName_1382_);
lean_ctor_set(v___x_1402_, 1, v_fileMap_1383_);
lean_ctor_set(v___x_1402_, 2, v_options_1384_);
lean_ctor_set(v___x_1402_, 3, v___x_1401_);
lean_ctor_set(v___x_1402_, 4, v_maxRecDepth_1386_);
lean_ctor_set(v___x_1402_, 5, v_ref_1387_);
lean_ctor_set(v___x_1402_, 6, v_currNamespace_1388_);
lean_ctor_set(v___x_1402_, 7, v_openDecls_1389_);
lean_ctor_set(v___x_1402_, 8, v_initHeartbeats_1390_);
lean_ctor_set(v___x_1402_, 9, v_maxHeartbeats_1391_);
lean_ctor_set(v___x_1402_, 10, v_quotContext_1392_);
lean_ctor_set(v___x_1402_, 11, v_currMacroScope_1393_);
lean_ctor_set(v___x_1402_, 12, v_cancelTk_x3f_1395_);
lean_ctor_set(v___x_1402_, 13, v_inheritedTraceOptions_1397_);
lean_ctor_set_uint8(v___x_1402_, sizeof(void*)*14, v_diag_1394_);
lean_ctor_set_uint8(v___x_1402_, sizeof(void*)*14 + 1, v_suppressElabErrors_1396_);
lean_inc(v_p_1381_);
v___x_1403_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_1381_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v___x_1402_, v_a_1361_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1483_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1406_ = v___x_1403_;
v_isShared_1407_ = v_isSharedCheck_1483_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1403_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1483_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
if (lean_obj_tag(v_a_1404_) == 1)
{
lean_object* v_val_1408_; lean_object* v_snd_1409_; uint8_t v_hasTrace_1410_; 
lean_del_object(v___x_1406_);
v_val_1408_ = lean_ctor_get(v_a_1404_, 0);
lean_inc(v_val_1408_);
lean_dec_ref_known(v_a_1404_, 1);
v_snd_1409_ = lean_ctor_get(v_val_1408_, 1);
lean_inc(v_snd_1409_);
v_hasTrace_1410_ = lean_ctor_get_uint8(v_options_1384_, sizeof(void*)*1);
if (v_hasTrace_1410_ == 0)
{
lean_object* v_fst_1411_; lean_object* v_fst_1412_; lean_object* v_snd_1413_; 
lean_dec_ref(v_inheritedTraceOptions_1397_);
lean_dec_ref(v_options_1384_);
v_fst_1411_ = lean_ctor_get(v_val_1408_, 0);
lean_inc(v_fst_1411_);
lean_dec(v_val_1408_);
v_fst_1412_ = lean_ctor_get(v_snd_1409_, 0);
lean_inc(v_fst_1412_);
v_snd_1413_ = lean_ctor_get(v_snd_1409_, 1);
lean_inc(v_snd_1413_);
lean_dec(v_snd_1409_);
v___y_1364_ = v_fst_1411_;
v___y_1365_ = v_snd_1413_;
v___y_1366_ = v_fst_1412_;
v___y_1367_ = v_a_1351_;
v___y_1368_ = v_a_1352_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v_a_1359_;
v___y_1376_ = v___x_1402_;
v___y_1377_ = v_a_1361_;
goto v___jp_1363_;
}
else
{
lean_object* v_fst_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1478_; 
v_fst_1414_ = lean_ctor_get(v_val_1408_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_val_1408_);
if (v_isSharedCheck_1478_ == 0)
{
lean_object* v_unused_1479_; 
v_unused_1479_ = lean_ctor_get(v_val_1408_, 1);
lean_dec(v_unused_1479_);
v___x_1416_ = v_val_1408_;
v_isShared_1417_ = v_isSharedCheck_1478_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_fst_1414_);
lean_dec(v_val_1408_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1478_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v_fst_1418_; lean_object* v_snd_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1477_; 
v_fst_1418_ = lean_ctor_get(v_snd_1409_, 0);
v_snd_1419_ = lean_ctor_get(v_snd_1409_, 1);
v_isSharedCheck_1477_ = !lean_is_exclusive(v_snd_1409_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1421_ = v_snd_1409_;
v_isShared_1422_ = v_isSharedCheck_1477_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_snd_1419_);
lean_inc(v_fst_1418_);
lean_dec(v_snd_1409_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1477_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_1424_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_1425_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1397_, v_options_1384_, v___x_1424_);
lean_dec_ref(v_options_1384_);
lean_dec_ref(v_inheritedTraceOptions_1397_);
if (v___x_1425_ == 0)
{
lean_del_object(v___x_1421_);
lean_del_object(v___x_1416_);
v___y_1364_ = v_fst_1414_;
v___y_1365_ = v_snd_1419_;
v___y_1366_ = v_fst_1418_;
v___y_1367_ = v_a_1351_;
v___y_1368_ = v_a_1352_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v_a_1359_;
v___y_1376_ = v___x_1402_;
v___y_1377_ = v_a_1361_;
goto v___jp_1363_;
}
else
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_1414_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v___x_1402_, v_a_1361_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v___x_1402_, v_a_1361_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1430_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v___x_1430_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_fst_1418_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v___x_1402_, v_a_1361_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1432_ = l_Lean_MessageData_ofExpr(v_a_1427_);
v___x_1433_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_1422_ == 0)
{
lean_ctor_set_tag(v___x_1421_, 7);
lean_ctor_set(v___x_1421_, 1, v___x_1433_);
lean_ctor_set(v___x_1421_, 0, v___x_1432_);
v___x_1435_ = v___x_1421_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = l_Lean_MessageData_ofExpr(v_a_1429_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set_tag(v___x_1416_, 7);
lean_ctor_set(v___x_1416_, 1, v___x_1436_);
lean_ctor_set(v___x_1416_, 0, v___x_1435_);
v___x_1438_ = v___x_1416_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
lean_ctor_set(v___x_1439_, 1, v___x_1433_);
v___x_1440_ = l_Lean_MessageData_ofExpr(v_a_1431_);
v___x_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1439_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_1423_, v___x_1441_, v_a_1358_, v_a_1359_, v___x_1402_, v_a_1361_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_dec_ref_known(v___x_1442_, 1);
v___y_1364_ = v_fst_1414_;
v___y_1365_ = v_snd_1419_;
v___y_1366_ = v_fst_1418_;
v___y_1367_ = v_a_1351_;
v___y_1368_ = v_a_1352_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v_a_1359_;
v___y_1376_ = v___x_1402_;
v___y_1377_ = v_a_1361_;
goto v___jp_1363_;
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_snd_1419_);
lean_dec(v_fst_1418_);
lean_dec(v_fst_1414_);
lean_dec_ref_known(v___x_1402_, 14);
lean_dec_ref(v_c_1350_);
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1442_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1442_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec(v_a_1429_);
lean_dec(v_a_1427_);
lean_del_object(v___x_1421_);
lean_dec(v_snd_1419_);
lean_dec(v_fst_1418_);
lean_del_object(v___x_1416_);
lean_dec(v_fst_1414_);
lean_dec_ref_known(v___x_1402_, 14);
lean_dec_ref(v_c_1350_);
v_a_1453_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1430_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1430_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec(v_a_1427_);
lean_del_object(v___x_1421_);
lean_dec(v_snd_1419_);
lean_dec(v_fst_1418_);
lean_del_object(v___x_1416_);
lean_dec(v_fst_1414_);
lean_dec_ref_known(v___x_1402_, 14);
lean_dec_ref(v_c_1350_);
v_a_1461_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1428_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1428_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_del_object(v___x_1421_);
lean_dec(v_snd_1419_);
lean_dec(v_fst_1418_);
lean_del_object(v___x_1416_);
lean_dec(v_fst_1414_);
lean_dec_ref_known(v___x_1402_, 14);
lean_dec_ref(v_c_1350_);
v_a_1469_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1426_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1426_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
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
lean_object* v___x_1481_; 
lean_dec(v_a_1404_);
lean_dec_ref_known(v___x_1402_, 14);
lean_dec_ref(v_inheritedTraceOptions_1397_);
lean_dec_ref(v_options_1384_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v_c_1350_);
v___x_1481_ = v___x_1406_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_c_1350_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec_ref_known(v___x_1402_, 14);
lean_dec_ref(v_inheritedTraceOptions_1397_);
lean_dec_ref(v_options_1384_);
lean_dec_ref(v_c_1350_);
v_a_1484_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1403_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1403_);
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
lean_object* v___x_1492_; 
lean_dec_ref(v_inheritedTraceOptions_1397_);
lean_dec(v_cancelTk_x3f_1395_);
lean_dec(v_currMacroScope_1393_);
lean_dec(v_quotContext_1392_);
lean_dec(v_maxHeartbeats_1391_);
lean_dec(v_initHeartbeats_1390_);
lean_dec(v_openDecls_1389_);
lean_dec(v_currNamespace_1388_);
lean_dec(v_maxRecDepth_1386_);
lean_dec(v_currRecDepth_1385_);
lean_dec_ref(v_options_1384_);
lean_dec_ref(v_fileMap_1383_);
lean_dec_ref(v_fileName_1382_);
lean_dec_ref(v_c_1350_);
v___x_1492_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1387_);
return v___x_1492_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object* v_c_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
lean_dec(v_a_1508_);
lean_dec(v_a_1506_);
lean_dec_ref(v_a_1505_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec(v_a_1498_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_ref_1517_; lean_object* v___x_1518_; lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1527_; 
v_ref_1517_ = lean_ctor_get(v___y_1514_, 5);
v___x_1518_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msg_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1521_ = v___x_1518_;
v_isShared_1522_ = v_isSharedCheck_1527_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1518_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1527_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
lean_inc(v_ref_1517_);
v___x_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1523_, 0, v_ref_1517_);
lean_ctor_set(v___x_1523_, 1, v_a_1519_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set_tag(v___x_1521_, 1);
lean_ctor_set(v___x_1521_, 0, v___x_1523_);
v___x_1525_ = v___x_1521_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
return v_res_1534_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0));
v___x_1537_ = l_Lean_stringToMessageData(v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1562_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1562_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1562_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v_leFn_x3f_1555_; 
v_leFn_x3f_1555_ = lean_ctor_get(v_a_1551_, 20);
lean_inc(v_leFn_x3f_1555_);
lean_dec(v_a_1551_);
if (lean_obj_tag(v_leFn_x3f_1555_) == 1)
{
lean_object* v_val_1556_; lean_object* v___x_1558_; 
v_val_1556_ = lean_ctor_get(v_leFn_x3f_1555_, 0);
lean_inc(v_val_1556_);
lean_dec_ref_known(v_leFn_x3f_1555_, 1);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v_val_1556_);
v___x_1558_ = v___x_1553_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_val_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
else
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec(v_leFn_x3f_1555_);
lean_del_object(v___x_1553_);
v___x_1560_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1);
v___x_1561_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1560_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
return v___x_1561_;
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
v_a_1563_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1550_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1550_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___boxed(lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec(v___y_1571_);
return v_res_1583_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0));
v___x_1586_ = l_Lean_stringToMessageData(v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1611_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1602_ = v___x_1599_;
v_isShared_1603_ = v_isSharedCheck_1611_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1599_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1611_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v_ltFn_x3f_1604_; 
v_ltFn_x3f_1604_ = lean_ctor_get(v_a_1600_, 21);
lean_inc(v_ltFn_x3f_1604_);
lean_dec(v_a_1600_);
if (lean_obj_tag(v_ltFn_x3f_1604_) == 1)
{
lean_object* v_val_1605_; lean_object* v___x_1607_; 
v_val_1605_ = lean_ctor_get(v_ltFn_x3f_1604_, 0);
lean_inc(v_val_1605_);
lean_dec_ref_known(v_ltFn_x3f_1604_, 1);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v_val_1605_);
v___x_1607_ = v___x_1602_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_val_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_dec(v_ltFn_x3f_1604_);
lean_del_object(v___x_1602_);
v___x_1609_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1);
v___x_1610_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1609_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
return v___x_1610_;
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
v_a_1612_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1599_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1599_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___boxed(lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec(v___y_1620_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(lean_object* v_p_1633_, uint8_t v_strict_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
if (v_strict_1634_ == 0)
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1649_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v___x_1649_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1633_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1651_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref_known(v___x_1649_, 1);
v___x_1651_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1661_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1661_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1661_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v_ofNatZero_1656_; lean_object* v___x_1657_; lean_object* v___x_1659_; 
v_ofNatZero_1656_ = lean_ctor_get(v_a_1652_, 18);
lean_inc_ref(v_ofNatZero_1656_);
lean_dec(v_a_1652_);
v___x_1657_ = l_Lean_mkAppB(v_a_1648_, v_a_1650_, v_ofNatZero_1656_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1657_);
v___x_1659_ = v___x_1654_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec(v_a_1650_);
lean_dec(v_a_1648_);
v_a_1662_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1651_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1651_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
else
{
lean_dec(v_a_1648_);
return v___x_1649_;
}
}
else
{
return v___x_1647_;
}
}
else
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1672_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref_known(v___x_1670_, 1);
v___x_1672_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1633_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1674_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_a_1673_);
lean_dec_ref_known(v___x_1672_, 1);
v___x_1674_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1684_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1677_ = v___x_1674_;
v_isShared_1678_ = v_isSharedCheck_1684_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1674_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1684_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v_ofNatZero_1679_; lean_object* v___x_1680_; lean_object* v___x_1682_; 
v_ofNatZero_1679_ = lean_ctor_get(v_a_1675_, 18);
lean_inc_ref(v_ofNatZero_1679_);
lean_dec(v_a_1675_);
v___x_1680_ = l_Lean_mkAppB(v_a_1671_, v_a_1673_, v_ofNatZero_1679_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1680_);
v___x_1682_ = v___x_1677_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec(v_a_1673_);
lean_dec(v_a_1671_);
v_a_1685_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1674_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1674_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
else
{
lean_dec(v_a_1671_);
return v___x_1672_;
}
}
else
{
return v___x_1670_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_p_1693_, lean_object* v_strict_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
uint8_t v_strict_boxed_1707_; lean_object* v_res_1708_; 
v_strict_boxed_1707_ = lean_unbox(v_strict_1694_);
v_res_1708_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1693_, v_strict_boxed_1707_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec(v_p_1693_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(lean_object* v_c_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_p_1722_; uint8_t v_strict_1723_; lean_object* v___x_1724_; 
v_p_1722_ = lean_ctor_get(v_c_1709_, 0);
v_strict_1723_ = lean_ctor_get_uint8(v_c_1709_, sizeof(void*)*2);
v___x_1724_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1722_, v_strict_1723_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0___boxed(lean_object* v_c_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v_c_1725_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object* v_a_1739_, lean_object* v_x_1740_, lean_object* v_c_u2081_1741_, lean_object* v_b_1742_, lean_object* v_c_u2082_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v_options_1756_; lean_object* v_p_1757_; lean_object* v_p_1758_; uint8_t v_strict_1759_; lean_object* v_inheritedTraceOptions_1760_; uint8_t v_hasTrace_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v_p_1766_; 
v_options_1756_ = lean_ctor_get(v_a_1753_, 2);
v_p_1757_ = lean_ctor_get(v_c_u2081_1741_, 0);
v_p_1758_ = lean_ctor_get(v_c_u2082_1743_, 0);
v_strict_1759_ = lean_ctor_get_uint8(v_c_u2082_1743_, sizeof(void*)*2);
v_inheritedTraceOptions_1760_ = lean_ctor_get(v_a_1753_, 13);
v_hasTrace_1761_ = lean_ctor_get_uint8(v_options_1756_, sizeof(void*)*1);
v___x_1762_ = lean_nat_to_int(v_a_1739_);
lean_inc(v_p_1758_);
v___x_1763_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1758_, v___x_1762_);
lean_dec(v___x_1762_);
v___x_1764_ = lean_int_neg(v_b_1742_);
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
v___x_1774_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1740_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1776_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref_known(v___x_1774_, 1);
v___x_1776_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_1741_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1778_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref_known(v___x_1776_, 1);
v___x_1778_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_u2082_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
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
v___x_1788_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_1771_, v___x_1787_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_dec_ref_known(v___x_1788_, 1);
goto v___jp_1767_;
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec(v_p_1766_);
lean_dec_ref(v_c_u2082_1743_);
lean_dec_ref(v_c_u2081_1741_);
lean_dec(v_x_1740_);
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
lean_dec_ref(v_c_u2082_1743_);
lean_dec_ref(v_c_u2081_1741_);
lean_dec(v_x_1740_);
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
lean_dec_ref(v_c_u2082_1743_);
lean_dec_ref(v_c_u2081_1741_);
lean_dec(v_x_1740_);
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
lean_dec_ref(v_c_u2082_1743_);
lean_dec_ref(v_c_u2081_1741_);
lean_dec(v_x_1740_);
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
lean_ctor_set(v___x_1768_, 0, v_x_1740_);
lean_ctor_set(v___x_1768_, 1, v_c_u2081_1741_);
lean_ctor_set(v___x_1768_, 2, v_c_u2082_1743_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object** _args){
lean_object* v_a_1821_ = _args[0];
lean_object* v_x_1822_ = _args[1];
lean_object* v_c_u2081_1823_ = _args[2];
lean_object* v_b_1824_ = _args[3];
lean_object* v_c_u2082_1825_ = _args[4];
lean_object* v_a_1826_ = _args[5];
lean_object* v_a_1827_ = _args[6];
lean_object* v_a_1828_ = _args[7];
lean_object* v_a_1829_ = _args[8];
lean_object* v_a_1830_ = _args[9];
lean_object* v_a_1831_ = _args[10];
lean_object* v_a_1832_ = _args[11];
lean_object* v_a_1833_ = _args[12];
lean_object* v_a_1834_ = _args[13];
lean_object* v_a_1835_ = _args[14];
lean_object* v_a_1836_ = _args[15];
lean_object* v_a_1837_ = _args[16];
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1821_, v_x_1822_, v_c_u2081_1823_, v_b_1824_, v_c_u2082_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec(v_a_1827_);
lean_dec(v_a_1826_);
lean_dec(v_b_1824_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1839_, lean_object* v_msg_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1840_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1854_, lean_object* v_msg_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1854_, v_msg_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec(v___y_1856_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(lean_object* v_a_1877_, lean_object* v_x_1878_, lean_object* v_c_u2081_1879_, lean_object* v_as_1880_, size_t v_sz_1881_, size_t v_i_1882_, lean_object* v_b_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
uint8_t v___x_1896_; 
v___x_1896_ = lean_usize_dec_lt(v_i_1882_, v_sz_1881_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; 
lean_dec_ref(v_c_u2081_1879_);
lean_dec(v_x_1878_);
lean_dec(v_a_1877_);
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v_b_1883_);
return v___x_1897_;
}
else
{
lean_object* v_a_1898_; lean_object* v_fst_1899_; lean_object* v_snd_1900_; lean_object* v___x_1901_; 
lean_dec_ref(v_b_1883_);
v_a_1898_ = lean_array_uget_borrowed(v_as_1880_, v_i_1882_);
v_fst_1899_ = lean_ctor_get(v_a_1898_, 0);
v_snd_1900_ = lean_ctor_get(v_a_1898_, 1);
lean_inc(v_snd_1900_);
lean_inc_ref(v_c_u2081_1879_);
lean_inc(v_x_1878_);
lean_inc(v_a_1877_);
v___x_1901_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1877_, v_x_1878_, v_c_u2081_1879_, v_fst_1899_, v_snd_1900_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1903_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1901_, 1);
v___x_1903_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_a_1902_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v___x_1904_; 
lean_dec_ref_known(v___x_1903_, 1);
v___x_1904_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1918_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1918_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1918_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
uint8_t v___x_1909_; 
v___x_1909_ = lean_unbox(v_a_1905_);
lean_dec(v_a_1905_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1910_; size_t v___x_1911_; size_t v___x_1912_; 
lean_del_object(v___x_1907_);
v___x_1910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v___x_1911_ = ((size_t)1ULL);
v___x_1912_ = lean_usize_add(v_i_1882_, v___x_1911_);
v_i_1882_ = v___x_1912_;
v_b_1883_ = v___x_1910_;
goto _start;
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
lean_dec_ref(v_c_u2081_1879_);
lean_dec(v_x_1878_);
lean_dec(v_a_1877_);
v___x_1914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1914_);
v___x_1916_ = v___x_1907_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
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
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec_ref(v_c_u2081_1879_);
lean_dec(v_x_1878_);
lean_dec(v_a_1877_);
v_a_1919_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1904_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1904_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec_ref(v_c_u2081_1879_);
lean_dec(v_x_1878_);
lean_dec(v_a_1877_);
v_a_1927_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1903_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1903_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_dec_ref(v_c_u2081_1879_);
lean_dec(v_x_1878_);
lean_dec(v_a_1877_);
v_a_1935_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1901_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1901_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___boxed(lean_object** _args){
lean_object* v_a_1943_ = _args[0];
lean_object* v_x_1944_ = _args[1];
lean_object* v_c_u2081_1945_ = _args[2];
lean_object* v_as_1946_ = _args[3];
lean_object* v_sz_1947_ = _args[4];
lean_object* v_i_1948_ = _args[5];
lean_object* v_b_1949_ = _args[6];
lean_object* v___y_1950_ = _args[7];
lean_object* v___y_1951_ = _args[8];
lean_object* v___y_1952_ = _args[9];
lean_object* v___y_1953_ = _args[10];
lean_object* v___y_1954_ = _args[11];
lean_object* v___y_1955_ = _args[12];
lean_object* v___y_1956_ = _args[13];
lean_object* v___y_1957_ = _args[14];
lean_object* v___y_1958_ = _args[15];
lean_object* v___y_1959_ = _args[16];
lean_object* v___y_1960_ = _args[17];
lean_object* v___y_1961_ = _args[18];
_start:
{
size_t v_sz_boxed_1962_; size_t v_i_boxed_1963_; lean_object* v_res_1964_; 
v_sz_boxed_1962_ = lean_unbox_usize(v_sz_1947_);
lean_dec(v_sz_1947_);
v_i_boxed_1963_ = lean_unbox_usize(v_i_1948_);
lean_dec(v_i_1948_);
v_res_1964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1943_, v_x_1944_, v_c_u2081_1945_, v_as_1946_, v_sz_boxed_1962_, v_i_boxed_1963_, v_b_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v_as_1946_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(lean_object* v_a_1965_, lean_object* v_x_1966_, lean_object* v_c_u2081_1967_, lean_object* v_todo_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; size_t v_sz_1983_; size_t v___x_1984_; lean_object* v___x_1985_; 
v___x_1981_ = lean_box(0);
v___x_1982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_1983_ = lean_array_size(v_todo_1968_);
v___x_1984_ = ((size_t)0ULL);
v___x_1985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1965_, v_x_1966_, v_c_u2081_1967_, v_todo_1968_, v_sz_1983_, v___x_1984_, v___x_1982_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1998_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_1998_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1998_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v_fst_1990_; 
v_fst_1990_ = lean_ctor_get(v_a_1986_, 0);
lean_inc(v_fst_1990_);
lean_dec(v_a_1986_);
if (lean_obj_tag(v_fst_1990_) == 0)
{
lean_object* v___x_1992_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v___x_1981_);
v___x_1992_ = v___x_1988_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1981_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
else
{
lean_object* v_val_1994_; lean_object* v___x_1996_; 
v_val_1994_ = lean_ctor_get(v_fst_1990_, 0);
lean_inc(v_val_1994_);
lean_dec_ref_known(v_fst_1990_, 1);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v_val_1994_);
v___x_1996_ = v___x_1988_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_val_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
v_a_1999_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1985_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1985_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object* v_a_2007_, lean_object* v_x_2008_, lean_object* v_c_u2081_2009_, lean_object* v_todo_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2007_, v_x_2008_, v_c_u2081_2009_, v_todo_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec_ref(v_todo_2010_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_2024_, lean_object* v_as_2025_, size_t v_sz_2026_, size_t v_i_2027_, lean_object* v_b_2028_){
_start:
{
uint8_t v___x_2029_; 
v___x_2029_ = lean_usize_dec_lt(v_i_2027_, v_sz_2026_);
if (v___x_2029_ == 0)
{
return v_b_2028_;
}
else
{
lean_object* v_snd_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2063_; 
v_snd_2030_ = lean_ctor_get(v_b_2028_, 1);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_b_2028_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; 
v_unused_2064_ = lean_ctor_get(v_b_2028_, 0);
lean_dec(v_unused_2064_);
v___x_2032_ = v_b_2028_;
v_isShared_2033_ = v_isSharedCheck_2063_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_snd_2030_);
lean_dec(v_b_2028_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2063_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v_fst_2034_; lean_object* v_snd_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2062_; 
v_fst_2034_ = lean_ctor_get(v_snd_2030_, 0);
v_snd_2035_ = lean_ctor_get(v_snd_2030_, 1);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_snd_2030_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2037_ = v_snd_2030_;
v_isShared_2038_ = v_isSharedCheck_2062_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_snd_2035_);
lean_inc(v_fst_2034_);
lean_dec(v_snd_2030_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2062_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v_a_2039_; lean_object* v_p_2040_; lean_object* v___x_2041_; lean_object* v_a_2043_; lean_object* v_b_2050_; lean_object* v___x_2051_; uint8_t v___x_2052_; 
v_a_2039_ = lean_array_uget_borrowed(v_as_2025_, v_i_2027_);
v_p_2040_ = lean_ctor_get(v_a_2039_, 0);
v___x_2041_ = lean_box(0);
v_b_2050_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2040_, v_x_2024_);
v___x_2051_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2052_ = lean_int_dec_eq(v_b_2050_, v___x_2051_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2054_; 
lean_inc(v_a_2039_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 1, v_a_2039_);
lean_ctor_set(v___x_2032_, 0, v_b_2050_);
v___x_2054_ = v___x_2032_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_b_2050_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_a_2039_);
v___x_2054_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v_todo_2055_; lean_object* v___x_2056_; 
v_todo_2055_ = lean_array_push(v_snd_2035_, v___x_2054_);
v___x_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2056_, 0, v_fst_2034_);
lean_ctor_set(v___x_2056_, 1, v_todo_2055_);
v_a_2043_ = v___x_2056_;
goto v___jp_2042_;
}
}
else
{
lean_object* v_cs_x27_2058_; lean_object* v___x_2060_; 
lean_dec(v_b_2050_);
lean_inc(v_a_2039_);
v_cs_x27_2058_ = l_Lean_PersistentArray_push___redArg(v_fst_2034_, v_a_2039_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 1, v_snd_2035_);
lean_ctor_set(v___x_2032_, 0, v_cs_x27_2058_);
v___x_2060_ = v___x_2032_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_cs_x27_2058_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_snd_2035_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
v_a_2043_ = v___x_2060_;
goto v___jp_2042_;
}
}
v___jp_2042_:
{
lean_object* v___x_2045_; 
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 1, v_a_2043_);
lean_ctor_set(v___x_2037_, 0, v___x_2041_);
v___x_2045_ = v___x_2037_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_a_2043_);
v___x_2045_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
size_t v___x_2046_; size_t v___x_2047_; 
v___x_2046_ = ((size_t)1ULL);
v___x_2047_ = lean_usize_add(v_i_2027_, v___x_2046_);
v_i_2027_ = v___x_2047_;
v_b_2028_ = v___x_2045_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_2065_, lean_object* v_as_2066_, lean_object* v_sz_2067_, lean_object* v_i_2068_, lean_object* v_b_2069_){
_start:
{
size_t v_sz_boxed_2070_; size_t v_i_boxed_2071_; lean_object* v_res_2072_; 
v_sz_boxed_2070_ = lean_unbox_usize(v_sz_2067_);
lean_dec(v_sz_2067_);
v_i_boxed_2071_ = lean_unbox_usize(v_i_2068_);
lean_dec(v_i_2068_);
v_res_2072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2065_, v_as_2066_, v_sz_boxed_2070_, v_i_boxed_2071_, v_b_2069_);
lean_dec_ref(v_as_2066_);
lean_dec(v_x_2065_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(lean_object* v_x_2073_, lean_object* v_as_2074_, size_t v_sz_2075_, size_t v_i_2076_, lean_object* v_b_2077_){
_start:
{
uint8_t v___x_2078_; 
v___x_2078_ = lean_usize_dec_lt(v_i_2076_, v_sz_2075_);
if (v___x_2078_ == 0)
{
return v_b_2077_;
}
else
{
lean_object* v_snd_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2112_; 
v_snd_2079_ = lean_ctor_get(v_b_2077_, 1);
v_isSharedCheck_2112_ = !lean_is_exclusive(v_b_2077_);
if (v_isSharedCheck_2112_ == 0)
{
lean_object* v_unused_2113_; 
v_unused_2113_ = lean_ctor_get(v_b_2077_, 0);
lean_dec(v_unused_2113_);
v___x_2081_ = v_b_2077_;
v_isShared_2082_ = v_isSharedCheck_2112_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_snd_2079_);
lean_dec(v_b_2077_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2112_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v_fst_2083_; lean_object* v_snd_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2111_; 
v_fst_2083_ = lean_ctor_get(v_snd_2079_, 0);
v_snd_2084_ = lean_ctor_get(v_snd_2079_, 1);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_snd_2079_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2086_ = v_snd_2079_;
v_isShared_2087_ = v_isSharedCheck_2111_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_snd_2084_);
lean_inc(v_fst_2083_);
lean_dec(v_snd_2079_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2111_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v_a_2088_; lean_object* v_p_2089_; lean_object* v___x_2090_; lean_object* v_a_2092_; lean_object* v_b_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; 
v_a_2088_ = lean_array_uget_borrowed(v_as_2074_, v_i_2076_);
v_p_2089_ = lean_ctor_get(v_a_2088_, 0);
v___x_2090_ = lean_box(0);
v_b_2099_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2089_, v_x_2073_);
v___x_2100_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2101_ = lean_int_dec_eq(v_b_2099_, v___x_2100_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2103_; 
lean_inc(v_a_2088_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 1, v_a_2088_);
lean_ctor_set(v___x_2081_, 0, v_b_2099_);
v___x_2103_ = v___x_2081_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_b_2099_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_a_2088_);
v___x_2103_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v_todo_2104_; lean_object* v___x_2105_; 
v_todo_2104_ = lean_array_push(v_snd_2084_, v___x_2103_);
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v_fst_2083_);
lean_ctor_set(v___x_2105_, 1, v_todo_2104_);
v_a_2092_ = v___x_2105_;
goto v___jp_2091_;
}
}
else
{
lean_object* v_cs_x27_2107_; lean_object* v___x_2109_; 
lean_dec(v_b_2099_);
lean_inc(v_a_2088_);
v_cs_x27_2107_ = l_Lean_PersistentArray_push___redArg(v_fst_2083_, v_a_2088_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 1, v_snd_2084_);
lean_ctor_set(v___x_2081_, 0, v_cs_x27_2107_);
v___x_2109_ = v___x_2081_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_cs_x27_2107_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_snd_2084_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
v_a_2092_ = v___x_2109_;
goto v___jp_2091_;
}
}
v___jp_2091_:
{
lean_object* v___x_2094_; 
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 1, v_a_2092_);
lean_ctor_set(v___x_2086_, 0, v___x_2090_);
v___x_2094_ = v___x_2086_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2090_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_a_2092_);
v___x_2094_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
size_t v___x_2095_; size_t v___x_2096_; lean_object* v___x_2097_; 
v___x_2095_ = ((size_t)1ULL);
v___x_2096_ = lean_usize_add(v_i_2076_, v___x_2095_);
v___x_2097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2073_, v_as_2074_, v_sz_2075_, v___x_2096_, v___x_2094_);
return v___x_2097_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2114_, lean_object* v_as_2115_, lean_object* v_sz_2116_, lean_object* v_i_2117_, lean_object* v_b_2118_){
_start:
{
size_t v_sz_boxed_2119_; size_t v_i_boxed_2120_; lean_object* v_res_2121_; 
v_sz_boxed_2119_ = lean_unbox_usize(v_sz_2116_);
lean_dec(v_sz_2116_);
v_i_boxed_2120_ = lean_unbox_usize(v_i_2117_);
lean_dec(v_i_2117_);
v_res_2121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2114_, v_as_2115_, v_sz_boxed_2119_, v_i_boxed_2120_, v_b_2118_);
lean_dec_ref(v_as_2115_);
lean_dec(v_x_2114_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_2122_, lean_object* v_as_2123_, size_t v_sz_2124_, size_t v_i_2125_, lean_object* v_b_2126_){
_start:
{
uint8_t v___x_2127_; 
v___x_2127_ = lean_usize_dec_lt(v_i_2125_, v_sz_2124_);
if (v___x_2127_ == 0)
{
return v_b_2126_;
}
else
{
lean_object* v_snd_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2161_; 
v_snd_2128_ = lean_ctor_get(v_b_2126_, 1);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_b_2126_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; 
v_unused_2162_ = lean_ctor_get(v_b_2126_, 0);
lean_dec(v_unused_2162_);
v___x_2130_ = v_b_2126_;
v_isShared_2131_ = v_isSharedCheck_2161_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_snd_2128_);
lean_dec(v_b_2126_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2161_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v_fst_2132_; lean_object* v_snd_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2160_; 
v_fst_2132_ = lean_ctor_get(v_snd_2128_, 0);
v_snd_2133_ = lean_ctor_get(v_snd_2128_, 1);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_snd_2128_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2135_ = v_snd_2128_;
v_isShared_2136_ = v_isSharedCheck_2160_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_snd_2133_);
lean_inc(v_fst_2132_);
lean_dec(v_snd_2128_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2160_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v_a_2137_; lean_object* v_p_2138_; lean_object* v___x_2139_; lean_object* v_a_2141_; lean_object* v_b_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; 
v_a_2137_ = lean_array_uget_borrowed(v_as_2123_, v_i_2125_);
v_p_2138_ = lean_ctor_get(v_a_2137_, 0);
v___x_2139_ = lean_box(0);
v_b_2148_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2138_, v_x_2122_);
v___x_2149_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2150_ = lean_int_dec_eq(v_b_2148_, v___x_2149_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2152_; 
lean_inc(v_a_2137_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 1, v_a_2137_);
lean_ctor_set(v___x_2130_, 0, v_b_2148_);
v___x_2152_ = v___x_2130_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_b_2148_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_a_2137_);
v___x_2152_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v_todo_2153_; lean_object* v___x_2154_; 
v_todo_2153_ = lean_array_push(v_snd_2133_, v___x_2152_);
v___x_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2154_, 0, v_fst_2132_);
lean_ctor_set(v___x_2154_, 1, v_todo_2153_);
v_a_2141_ = v___x_2154_;
goto v___jp_2140_;
}
}
else
{
lean_object* v_cs_x27_2156_; lean_object* v___x_2158_; 
lean_dec(v_b_2148_);
lean_inc(v_a_2137_);
v_cs_x27_2156_ = l_Lean_PersistentArray_push___redArg(v_fst_2132_, v_a_2137_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 1, v_snd_2133_);
lean_ctor_set(v___x_2130_, 0, v_cs_x27_2156_);
v___x_2158_ = v___x_2130_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_cs_x27_2156_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_snd_2133_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
v_a_2141_ = v___x_2158_;
goto v___jp_2140_;
}
}
v___jp_2140_:
{
lean_object* v___x_2143_; 
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 1, v_a_2141_);
lean_ctor_set(v___x_2135_, 0, v___x_2139_);
v___x_2143_ = v___x_2135_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2139_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_a_2141_);
v___x_2143_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
size_t v___x_2144_; size_t v___x_2145_; 
v___x_2144_ = ((size_t)1ULL);
v___x_2145_ = lean_usize_add(v_i_2125_, v___x_2144_);
v_i_2125_ = v___x_2145_;
v_b_2126_ = v___x_2143_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_2163_, lean_object* v_as_2164_, lean_object* v_sz_2165_, lean_object* v_i_2166_, lean_object* v_b_2167_){
_start:
{
size_t v_sz_boxed_2168_; size_t v_i_boxed_2169_; lean_object* v_res_2170_; 
v_sz_boxed_2168_ = lean_unbox_usize(v_sz_2165_);
lean_dec(v_sz_2165_);
v_i_boxed_2169_ = lean_unbox_usize(v_i_2166_);
lean_dec(v_i_2166_);
v_res_2170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2163_, v_as_2164_, v_sz_boxed_2168_, v_i_boxed_2169_, v_b_2167_);
lean_dec_ref(v_as_2164_);
lean_dec(v_x_2163_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2171_, lean_object* v_as_2172_, size_t v_sz_2173_, size_t v_i_2174_, lean_object* v_b_2175_){
_start:
{
uint8_t v___x_2176_; 
v___x_2176_ = lean_usize_dec_lt(v_i_2174_, v_sz_2173_);
if (v___x_2176_ == 0)
{
return v_b_2175_;
}
else
{
lean_object* v_snd_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2210_; 
v_snd_2177_ = lean_ctor_get(v_b_2175_, 1);
v_isSharedCheck_2210_ = !lean_is_exclusive(v_b_2175_);
if (v_isSharedCheck_2210_ == 0)
{
lean_object* v_unused_2211_; 
v_unused_2211_ = lean_ctor_get(v_b_2175_, 0);
lean_dec(v_unused_2211_);
v___x_2179_ = v_b_2175_;
v_isShared_2180_ = v_isSharedCheck_2210_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_snd_2177_);
lean_dec(v_b_2175_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2210_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v_fst_2181_; lean_object* v_snd_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2209_; 
v_fst_2181_ = lean_ctor_get(v_snd_2177_, 0);
v_snd_2182_ = lean_ctor_get(v_snd_2177_, 1);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_snd_2177_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2184_ = v_snd_2177_;
v_isShared_2185_ = v_isSharedCheck_2209_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_snd_2182_);
lean_inc(v_fst_2181_);
lean_dec(v_snd_2177_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2209_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v_a_2186_; lean_object* v_p_2187_; lean_object* v___x_2188_; lean_object* v_a_2190_; lean_object* v_b_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; 
v_a_2186_ = lean_array_uget_borrowed(v_as_2172_, v_i_2174_);
v_p_2187_ = lean_ctor_get(v_a_2186_, 0);
v___x_2188_ = lean_box(0);
v_b_2197_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2187_, v_x_2171_);
v___x_2198_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2199_ = lean_int_dec_eq(v_b_2197_, v___x_2198_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2201_; 
lean_inc(v_a_2186_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 1, v_a_2186_);
lean_ctor_set(v___x_2179_, 0, v_b_2197_);
v___x_2201_ = v___x_2179_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_b_2197_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_a_2186_);
v___x_2201_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v_todo_2202_; lean_object* v___x_2203_; 
v_todo_2202_ = lean_array_push(v_snd_2182_, v___x_2201_);
v___x_2203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2203_, 0, v_fst_2181_);
lean_ctor_set(v___x_2203_, 1, v_todo_2202_);
v_a_2190_ = v___x_2203_;
goto v___jp_2189_;
}
}
else
{
lean_object* v_cs_x27_2205_; lean_object* v___x_2207_; 
lean_dec(v_b_2197_);
lean_inc(v_a_2186_);
v_cs_x27_2205_ = l_Lean_PersistentArray_push___redArg(v_fst_2181_, v_a_2186_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 1, v_snd_2182_);
lean_ctor_set(v___x_2179_, 0, v_cs_x27_2205_);
v___x_2207_ = v___x_2179_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_cs_x27_2205_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_snd_2182_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
v_a_2190_ = v___x_2207_;
goto v___jp_2189_;
}
}
v___jp_2189_:
{
lean_object* v___x_2192_; 
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 1, v_a_2190_);
lean_ctor_set(v___x_2184_, 0, v___x_2188_);
v___x_2192_ = v___x_2184_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2188_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_a_2190_);
v___x_2192_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
size_t v___x_2193_; size_t v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = ((size_t)1ULL);
v___x_2194_ = lean_usize_add(v_i_2174_, v___x_2193_);
v___x_2195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2171_, v_as_2172_, v_sz_2173_, v___x_2194_, v___x_2192_);
return v___x_2195_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_2212_, lean_object* v_as_2213_, lean_object* v_sz_2214_, lean_object* v_i_2215_, lean_object* v_b_2216_){
_start:
{
size_t v_sz_boxed_2217_; size_t v_i_boxed_2218_; lean_object* v_res_2219_; 
v_sz_boxed_2217_ = lean_unbox_usize(v_sz_2214_);
lean_dec(v_sz_2214_);
v_i_boxed_2218_ = lean_unbox_usize(v_i_2215_);
lean_dec(v_i_2215_);
v_res_2219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2212_, v_as_2213_, v_sz_boxed_2217_, v_i_boxed_2218_, v_b_2216_);
lean_dec_ref(v_as_2213_);
lean_dec(v_x_2212_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(lean_object* v_init_2220_, lean_object* v_x_2221_, lean_object* v_n_2222_, lean_object* v_b_2223_){
_start:
{
if (lean_obj_tag(v_n_2222_) == 0)
{
lean_object* v_cs_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; size_t v_sz_2227_; size_t v___x_2228_; lean_object* v___x_2229_; lean_object* v_fst_2230_; 
v_cs_2224_ = lean_ctor_get(v_n_2222_, 0);
v___x_2225_ = lean_box(0);
v___x_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
lean_ctor_set(v___x_2226_, 1, v_b_2223_);
v_sz_2227_ = lean_array_size(v_cs_2224_);
v___x_2228_ = ((size_t)0ULL);
v___x_2229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2220_, v_x_2221_, v_cs_2224_, v_sz_2227_, v___x_2228_, v___x_2226_);
v_fst_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_fst_2230_);
if (lean_obj_tag(v_fst_2230_) == 0)
{
lean_object* v_snd_2231_; lean_object* v___x_2232_; 
v_snd_2231_ = lean_ctor_get(v___x_2229_, 1);
lean_inc(v_snd_2231_);
lean_dec_ref(v___x_2229_);
v___x_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2232_, 0, v_snd_2231_);
return v___x_2232_;
}
else
{
lean_object* v_val_2233_; 
lean_dec_ref(v___x_2229_);
v_val_2233_ = lean_ctor_get(v_fst_2230_, 0);
lean_inc(v_val_2233_);
lean_dec_ref_known(v_fst_2230_, 1);
return v_val_2233_;
}
}
else
{
lean_object* v_vs_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; size_t v_sz_2237_; size_t v___x_2238_; lean_object* v___x_2239_; lean_object* v_fst_2240_; 
v_vs_2234_ = lean_ctor_get(v_n_2222_, 0);
v___x_2235_ = lean_box(0);
v___x_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
lean_ctor_set(v___x_2236_, 1, v_b_2223_);
v_sz_2237_ = lean_array_size(v_vs_2234_);
v___x_2238_ = ((size_t)0ULL);
v___x_2239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2221_, v_vs_2234_, v_sz_2237_, v___x_2238_, v___x_2236_);
v_fst_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_fst_2240_);
if (lean_obj_tag(v_fst_2240_) == 0)
{
lean_object* v_snd_2241_; lean_object* v___x_2242_; 
v_snd_2241_ = lean_ctor_get(v___x_2239_, 1);
lean_inc(v_snd_2241_);
lean_dec_ref(v___x_2239_);
v___x_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2242_, 0, v_snd_2241_);
return v___x_2242_;
}
else
{
lean_object* v_val_2243_; 
lean_dec_ref(v___x_2239_);
v_val_2243_ = lean_ctor_get(v_fst_2240_, 0);
lean_inc(v_val_2243_);
lean_dec_ref_known(v_fst_2240_, 1);
return v_val_2243_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_2244_, lean_object* v_x_2245_, lean_object* v_as_2246_, size_t v_sz_2247_, size_t v_i_2248_, lean_object* v_b_2249_){
_start:
{
uint8_t v___x_2250_; 
v___x_2250_ = lean_usize_dec_lt(v_i_2248_, v_sz_2247_);
if (v___x_2250_ == 0)
{
return v_b_2249_;
}
else
{
lean_object* v_snd_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2269_; 
v_snd_2251_ = lean_ctor_get(v_b_2249_, 1);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_b_2249_);
if (v_isSharedCheck_2269_ == 0)
{
lean_object* v_unused_2270_; 
v_unused_2270_ = lean_ctor_get(v_b_2249_, 0);
lean_dec(v_unused_2270_);
v___x_2253_ = v_b_2249_;
v_isShared_2254_ = v_isSharedCheck_2269_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_snd_2251_);
lean_dec(v_b_2249_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2269_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v_a_2255_; lean_object* v___x_2256_; 
v_a_2255_ = lean_array_uget_borrowed(v_as_2246_, v_i_2248_);
lean_inc(v_snd_2251_);
v___x_2256_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2244_, v_x_2245_, v_a_2255_, v_snd_2251_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 0, v___x_2257_);
v___x_2259_ = v___x_2253_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2257_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_snd_2251_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2262_; lean_object* v___x_2264_; 
lean_dec(v_snd_2251_);
v_a_2261_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v___x_2256_, 1);
v___x_2262_ = lean_box(0);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 1, v_a_2261_);
lean_ctor_set(v___x_2253_, 0, v___x_2262_);
v___x_2264_ = v___x_2253_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2262_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v_a_2261_);
v___x_2264_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
size_t v___x_2265_; size_t v___x_2266_; 
v___x_2265_ = ((size_t)1ULL);
v___x_2266_ = lean_usize_add(v_i_2248_, v___x_2265_);
v_i_2248_ = v___x_2266_;
v_b_2249_ = v___x_2264_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_2271_, lean_object* v_x_2272_, lean_object* v_as_2273_, lean_object* v_sz_2274_, lean_object* v_i_2275_, lean_object* v_b_2276_){
_start:
{
size_t v_sz_boxed_2277_; size_t v_i_boxed_2278_; lean_object* v_res_2279_; 
v_sz_boxed_2277_ = lean_unbox_usize(v_sz_2274_);
lean_dec(v_sz_2274_);
v_i_boxed_2278_ = lean_unbox_usize(v_i_2275_);
lean_dec(v_i_2275_);
v_res_2279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2271_, v_x_2272_, v_as_2273_, v_sz_boxed_2277_, v_i_boxed_2278_, v_b_2276_);
lean_dec_ref(v_as_2273_);
lean_dec(v_x_2272_);
lean_dec_ref(v_init_2271_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_2280_, lean_object* v_x_2281_, lean_object* v_n_2282_, lean_object* v_b_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2280_, v_x_2281_, v_n_2282_, v_b_2283_);
lean_dec_ref(v_n_2282_);
lean_dec(v_x_2281_);
lean_dec_ref(v_init_2280_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(lean_object* v_x_2285_, lean_object* v_t_2286_, lean_object* v_init_2287_){
_start:
{
lean_object* v_root_2288_; lean_object* v_tail_2289_; lean_object* v___x_2290_; 
v_root_2288_ = lean_ctor_get(v_t_2286_, 0);
v_tail_2289_ = lean_ctor_get(v_t_2286_, 1);
lean_inc_ref(v_init_2287_);
v___x_2290_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2287_, v_x_2285_, v_root_2288_, v_init_2287_);
lean_dec_ref(v_init_2287_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2291_);
lean_dec_ref_known(v___x_2290_, 1);
return v_a_2291_;
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; size_t v_sz_2295_; size_t v___x_2296_; lean_object* v___x_2297_; lean_object* v_fst_2298_; 
v_a_2292_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2292_);
lean_dec_ref_known(v___x_2290_, 1);
v___x_2293_ = lean_box(0);
v___x_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
lean_ctor_set(v___x_2294_, 1, v_a_2292_);
v_sz_2295_ = lean_array_size(v_tail_2289_);
v___x_2296_ = ((size_t)0ULL);
v___x_2297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2285_, v_tail_2289_, v_sz_2295_, v___x_2296_, v___x_2294_);
v_fst_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_fst_2298_);
if (lean_obj_tag(v_fst_2298_) == 0)
{
lean_object* v_snd_2299_; 
v_snd_2299_ = lean_ctor_get(v___x_2297_, 1);
lean_inc(v_snd_2299_);
lean_dec_ref(v___x_2297_);
return v_snd_2299_;
}
else
{
lean_object* v_val_2300_; 
lean_dec_ref(v___x_2297_);
v_val_2300_ = lean_ctor_get(v_fst_2298_, 0);
lean_inc(v_val_2300_);
lean_dec_ref_known(v_fst_2298_, 1);
return v_val_2300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0___boxed(lean_object* v_x_2301_, lean_object* v_t_2302_, lean_object* v_init_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2301_, v_t_2302_, v_init_2303_);
lean_dec_ref(v_t_2302_);
lean_dec(v_x_2301_);
return v_res_2304_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = lean_unsigned_to_nat(32u);
v___x_2306_ = lean_mk_empty_array_with_capacity(v___x_2305_);
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
return v___x_2307_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1(void){
_start:
{
size_t v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v_cs_x27_2313_; 
v___x_2308_ = ((size_t)5ULL);
v___x_2309_ = lean_unsigned_to_nat(0u);
v___x_2310_ = lean_unsigned_to_nat(32u);
v___x_2311_ = lean_mk_empty_array_with_capacity(v___x_2310_);
v___x_2312_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0);
v_cs_x27_2313_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_2313_, 0, v___x_2312_);
lean_ctor_set(v_cs_x27_2313_, 1, v___x_2311_);
lean_ctor_set(v_cs_x27_2313_, 2, v___x_2309_);
lean_ctor_set(v_cs_x27_2313_, 3, v___x_2309_);
lean_ctor_set_usize(v_cs_x27_2313_, 4, v___x_2308_);
return v_cs_x27_2313_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_2316_; lean_object* v_cs_x27_2317_; lean_object* v___x_2318_; 
v_todo_2316_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2));
v_cs_x27_2317_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1);
v___x_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2318_, 0, v_cs_x27_2317_);
lean_ctor_set(v___x_2318_, 1, v_todo_2316_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(lean_object* v_x_2319_, lean_object* v_cs_2320_){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v_fst_2323_; lean_object* v_snd_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
v___x_2321_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3);
v___x_2322_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2319_, v_cs_2320_, v___x_2321_);
v_fst_2323_ = lean_ctor_get(v___x_2322_, 0);
v_snd_2324_ = lean_ctor_get(v___x_2322_, 1);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2322_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_snd_2324_);
lean_inc(v_fst_2323_);
lean_dec(v___x_2322_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_fst_2323_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_snd_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___boxed(lean_object* v_x_2332_, lean_object* v_cs_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2332_, v_cs_2333_);
lean_dec_ref(v_cs_2333_);
lean_dec(v_x_2332_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object* v_x_2335_, lean_object* v_cs_2336_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2335_, v_cs_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___boxed(lean_object* v_x_2338_, lean_object* v_cs_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(v_x_2338_, v_cs_2339_);
lean_dec_ref(v_cs_2339_);
lean_dec(v_x_2338_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(lean_object* v_a_2341_, lean_object* v_y_2342_, lean_object* v_fst_2343_, lean_object* v_s_2344_){
_start:
{
lean_object* v_structs_2345_; lean_object* v_typeIdOf_2346_; lean_object* v_exprToStructId_2347_; lean_object* v_exprToStructIdEntries_2348_; lean_object* v_forbiddenNatModules_2349_; lean_object* v_natStructs_2350_; lean_object* v_natTypeIdOf_2351_; lean_object* v_exprToNatStructId_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; 
v_structs_2345_ = lean_ctor_get(v_s_2344_, 0);
v_typeIdOf_2346_ = lean_ctor_get(v_s_2344_, 1);
v_exprToStructId_2347_ = lean_ctor_get(v_s_2344_, 2);
v_exprToStructIdEntries_2348_ = lean_ctor_get(v_s_2344_, 3);
v_forbiddenNatModules_2349_ = lean_ctor_get(v_s_2344_, 4);
v_natStructs_2350_ = lean_ctor_get(v_s_2344_, 5);
v_natTypeIdOf_2351_ = lean_ctor_get(v_s_2344_, 6);
v_exprToNatStructId_2352_ = lean_ctor_get(v_s_2344_, 7);
v___x_2353_ = lean_array_get_size(v_structs_2345_);
v___x_2354_ = lean_nat_dec_lt(v_a_2341_, v___x_2353_);
if (v___x_2354_ == 0)
{
lean_dec_ref(v_fst_2343_);
return v_s_2344_;
}
else
{
lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2416_; 
lean_inc_ref(v_exprToNatStructId_2352_);
lean_inc_ref(v_natTypeIdOf_2351_);
lean_inc_ref(v_natStructs_2350_);
lean_inc_ref(v_forbiddenNatModules_2349_);
lean_inc_ref(v_exprToStructIdEntries_2348_);
lean_inc_ref(v_exprToStructId_2347_);
lean_inc_ref(v_typeIdOf_2346_);
lean_inc_ref(v_structs_2345_);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_s_2344_);
if (v_isSharedCheck_2416_ == 0)
{
lean_object* v_unused_2417_; lean_object* v_unused_2418_; lean_object* v_unused_2419_; lean_object* v_unused_2420_; lean_object* v_unused_2421_; lean_object* v_unused_2422_; lean_object* v_unused_2423_; lean_object* v_unused_2424_; 
v_unused_2417_ = lean_ctor_get(v_s_2344_, 7);
lean_dec(v_unused_2417_);
v_unused_2418_ = lean_ctor_get(v_s_2344_, 6);
lean_dec(v_unused_2418_);
v_unused_2419_ = lean_ctor_get(v_s_2344_, 5);
lean_dec(v_unused_2419_);
v_unused_2420_ = lean_ctor_get(v_s_2344_, 4);
lean_dec(v_unused_2420_);
v_unused_2421_ = lean_ctor_get(v_s_2344_, 3);
lean_dec(v_unused_2421_);
v_unused_2422_ = lean_ctor_get(v_s_2344_, 2);
lean_dec(v_unused_2422_);
v_unused_2423_ = lean_ctor_get(v_s_2344_, 1);
lean_dec(v_unused_2423_);
v_unused_2424_ = lean_ctor_get(v_s_2344_, 0);
lean_dec(v_unused_2424_);
v___x_2356_ = v_s_2344_;
v_isShared_2357_ = v_isSharedCheck_2416_;
goto v_resetjp_2355_;
}
else
{
lean_dec(v_s_2344_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2416_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v_v_2358_; lean_object* v_id_2359_; lean_object* v_ringId_x3f_2360_; lean_object* v_type_2361_; lean_object* v_u_2362_; lean_object* v_intModuleInst_2363_; lean_object* v_leInst_x3f_2364_; lean_object* v_ltInst_x3f_2365_; lean_object* v_lawfulOrderLTInst_x3f_2366_; lean_object* v_isPreorderInst_x3f_2367_; lean_object* v_orderedAddInst_x3f_2368_; lean_object* v_isLinearInst_x3f_2369_; lean_object* v_noNatDivInst_x3f_2370_; lean_object* v_ringInst_x3f_2371_; lean_object* v_commRingInst_x3f_2372_; lean_object* v_orderedRingInst_x3f_2373_; lean_object* v_fieldInst_x3f_2374_; lean_object* v_charInst_x3f_2375_; lean_object* v_zero_2376_; lean_object* v_ofNatZero_2377_; lean_object* v_one_x3f_2378_; lean_object* v_leFn_x3f_2379_; lean_object* v_ltFn_x3f_2380_; lean_object* v_addFn_2381_; lean_object* v_zsmulFn_2382_; lean_object* v_nsmulFn_2383_; lean_object* v_zsmulFn_x3f_2384_; lean_object* v_nsmulFn_x3f_2385_; lean_object* v_homomulFn_x3f_2386_; lean_object* v_subFn_2387_; lean_object* v_negFn_2388_; lean_object* v_vars_2389_; lean_object* v_varMap_2390_; lean_object* v_lowers_2391_; lean_object* v_uppers_2392_; lean_object* v_diseqs_2393_; lean_object* v_assignment_2394_; uint8_t v_caseSplits_2395_; lean_object* v_conflict_x3f_2396_; lean_object* v_diseqSplits_2397_; lean_object* v_elimEqs_2398_; lean_object* v_elimStack_2399_; lean_object* v_occurs_2400_; lean_object* v_ignored_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2415_; 
v_v_2358_ = lean_array_fget(v_structs_2345_, v_a_2341_);
v_id_2359_ = lean_ctor_get(v_v_2358_, 0);
v_ringId_x3f_2360_ = lean_ctor_get(v_v_2358_, 1);
v_type_2361_ = lean_ctor_get(v_v_2358_, 2);
v_u_2362_ = lean_ctor_get(v_v_2358_, 3);
v_intModuleInst_2363_ = lean_ctor_get(v_v_2358_, 4);
v_leInst_x3f_2364_ = lean_ctor_get(v_v_2358_, 5);
v_ltInst_x3f_2365_ = lean_ctor_get(v_v_2358_, 6);
v_lawfulOrderLTInst_x3f_2366_ = lean_ctor_get(v_v_2358_, 7);
v_isPreorderInst_x3f_2367_ = lean_ctor_get(v_v_2358_, 8);
v_orderedAddInst_x3f_2368_ = lean_ctor_get(v_v_2358_, 9);
v_isLinearInst_x3f_2369_ = lean_ctor_get(v_v_2358_, 10);
v_noNatDivInst_x3f_2370_ = lean_ctor_get(v_v_2358_, 11);
v_ringInst_x3f_2371_ = lean_ctor_get(v_v_2358_, 12);
v_commRingInst_x3f_2372_ = lean_ctor_get(v_v_2358_, 13);
v_orderedRingInst_x3f_2373_ = lean_ctor_get(v_v_2358_, 14);
v_fieldInst_x3f_2374_ = lean_ctor_get(v_v_2358_, 15);
v_charInst_x3f_2375_ = lean_ctor_get(v_v_2358_, 16);
v_zero_2376_ = lean_ctor_get(v_v_2358_, 17);
v_ofNatZero_2377_ = lean_ctor_get(v_v_2358_, 18);
v_one_x3f_2378_ = lean_ctor_get(v_v_2358_, 19);
v_leFn_x3f_2379_ = lean_ctor_get(v_v_2358_, 20);
v_ltFn_x3f_2380_ = lean_ctor_get(v_v_2358_, 21);
v_addFn_2381_ = lean_ctor_get(v_v_2358_, 22);
v_zsmulFn_2382_ = lean_ctor_get(v_v_2358_, 23);
v_nsmulFn_2383_ = lean_ctor_get(v_v_2358_, 24);
v_zsmulFn_x3f_2384_ = lean_ctor_get(v_v_2358_, 25);
v_nsmulFn_x3f_2385_ = lean_ctor_get(v_v_2358_, 26);
v_homomulFn_x3f_2386_ = lean_ctor_get(v_v_2358_, 27);
v_subFn_2387_ = lean_ctor_get(v_v_2358_, 28);
v_negFn_2388_ = lean_ctor_get(v_v_2358_, 29);
v_vars_2389_ = lean_ctor_get(v_v_2358_, 30);
v_varMap_2390_ = lean_ctor_get(v_v_2358_, 31);
v_lowers_2391_ = lean_ctor_get(v_v_2358_, 32);
v_uppers_2392_ = lean_ctor_get(v_v_2358_, 33);
v_diseqs_2393_ = lean_ctor_get(v_v_2358_, 34);
v_assignment_2394_ = lean_ctor_get(v_v_2358_, 35);
v_caseSplits_2395_ = lean_ctor_get_uint8(v_v_2358_, sizeof(void*)*42);
v_conflict_x3f_2396_ = lean_ctor_get(v_v_2358_, 36);
v_diseqSplits_2397_ = lean_ctor_get(v_v_2358_, 37);
v_elimEqs_2398_ = lean_ctor_get(v_v_2358_, 38);
v_elimStack_2399_ = lean_ctor_get(v_v_2358_, 39);
v_occurs_2400_ = lean_ctor_get(v_v_2358_, 40);
v_ignored_2401_ = lean_ctor_get(v_v_2358_, 41);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_v_2358_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2403_ = v_v_2358_;
v_isShared_2404_ = v_isSharedCheck_2415_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_ignored_2401_);
lean_inc(v_occurs_2400_);
lean_inc(v_elimStack_2399_);
lean_inc(v_elimEqs_2398_);
lean_inc(v_diseqSplits_2397_);
lean_inc(v_conflict_x3f_2396_);
lean_inc(v_assignment_2394_);
lean_inc(v_diseqs_2393_);
lean_inc(v_uppers_2392_);
lean_inc(v_lowers_2391_);
lean_inc(v_varMap_2390_);
lean_inc(v_vars_2389_);
lean_inc(v_negFn_2388_);
lean_inc(v_subFn_2387_);
lean_inc(v_homomulFn_x3f_2386_);
lean_inc(v_nsmulFn_x3f_2385_);
lean_inc(v_zsmulFn_x3f_2384_);
lean_inc(v_nsmulFn_2383_);
lean_inc(v_zsmulFn_2382_);
lean_inc(v_addFn_2381_);
lean_inc(v_ltFn_x3f_2380_);
lean_inc(v_leFn_x3f_2379_);
lean_inc(v_one_x3f_2378_);
lean_inc(v_ofNatZero_2377_);
lean_inc(v_zero_2376_);
lean_inc(v_charInst_x3f_2375_);
lean_inc(v_fieldInst_x3f_2374_);
lean_inc(v_orderedRingInst_x3f_2373_);
lean_inc(v_commRingInst_x3f_2372_);
lean_inc(v_ringInst_x3f_2371_);
lean_inc(v_noNatDivInst_x3f_2370_);
lean_inc(v_isLinearInst_x3f_2369_);
lean_inc(v_orderedAddInst_x3f_2368_);
lean_inc(v_isPreorderInst_x3f_2367_);
lean_inc(v_lawfulOrderLTInst_x3f_2366_);
lean_inc(v_ltInst_x3f_2365_);
lean_inc(v_leInst_x3f_2364_);
lean_inc(v_intModuleInst_2363_);
lean_inc(v_u_2362_);
lean_inc(v_type_2361_);
lean_inc(v_ringId_x3f_2360_);
lean_inc(v_id_2359_);
lean_dec(v_v_2358_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2415_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2405_; lean_object* v_xs_x27_2406_; lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2405_ = lean_box(0);
v_xs_x27_2406_ = lean_array_fset(v_structs_2345_, v_a_2341_, v___x_2405_);
v___x_2407_ = l_Lean_PersistentArray_set___redArg(v_lowers_2391_, v_y_2342_, v_fst_2343_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 32, v___x_2407_);
v___x_2409_ = v___x_2403_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_id_2359_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_ringId_x3f_2360_);
lean_ctor_set(v_reuseFailAlloc_2414_, 2, v_type_2361_);
lean_ctor_set(v_reuseFailAlloc_2414_, 3, v_u_2362_);
lean_ctor_set(v_reuseFailAlloc_2414_, 4, v_intModuleInst_2363_);
lean_ctor_set(v_reuseFailAlloc_2414_, 5, v_leInst_x3f_2364_);
lean_ctor_set(v_reuseFailAlloc_2414_, 6, v_ltInst_x3f_2365_);
lean_ctor_set(v_reuseFailAlloc_2414_, 7, v_lawfulOrderLTInst_x3f_2366_);
lean_ctor_set(v_reuseFailAlloc_2414_, 8, v_isPreorderInst_x3f_2367_);
lean_ctor_set(v_reuseFailAlloc_2414_, 9, v_orderedAddInst_x3f_2368_);
lean_ctor_set(v_reuseFailAlloc_2414_, 10, v_isLinearInst_x3f_2369_);
lean_ctor_set(v_reuseFailAlloc_2414_, 11, v_noNatDivInst_x3f_2370_);
lean_ctor_set(v_reuseFailAlloc_2414_, 12, v_ringInst_x3f_2371_);
lean_ctor_set(v_reuseFailAlloc_2414_, 13, v_commRingInst_x3f_2372_);
lean_ctor_set(v_reuseFailAlloc_2414_, 14, v_orderedRingInst_x3f_2373_);
lean_ctor_set(v_reuseFailAlloc_2414_, 15, v_fieldInst_x3f_2374_);
lean_ctor_set(v_reuseFailAlloc_2414_, 16, v_charInst_x3f_2375_);
lean_ctor_set(v_reuseFailAlloc_2414_, 17, v_zero_2376_);
lean_ctor_set(v_reuseFailAlloc_2414_, 18, v_ofNatZero_2377_);
lean_ctor_set(v_reuseFailAlloc_2414_, 19, v_one_x3f_2378_);
lean_ctor_set(v_reuseFailAlloc_2414_, 20, v_leFn_x3f_2379_);
lean_ctor_set(v_reuseFailAlloc_2414_, 21, v_ltFn_x3f_2380_);
lean_ctor_set(v_reuseFailAlloc_2414_, 22, v_addFn_2381_);
lean_ctor_set(v_reuseFailAlloc_2414_, 23, v_zsmulFn_2382_);
lean_ctor_set(v_reuseFailAlloc_2414_, 24, v_nsmulFn_2383_);
lean_ctor_set(v_reuseFailAlloc_2414_, 25, v_zsmulFn_x3f_2384_);
lean_ctor_set(v_reuseFailAlloc_2414_, 26, v_nsmulFn_x3f_2385_);
lean_ctor_set(v_reuseFailAlloc_2414_, 27, v_homomulFn_x3f_2386_);
lean_ctor_set(v_reuseFailAlloc_2414_, 28, v_subFn_2387_);
lean_ctor_set(v_reuseFailAlloc_2414_, 29, v_negFn_2388_);
lean_ctor_set(v_reuseFailAlloc_2414_, 30, v_vars_2389_);
lean_ctor_set(v_reuseFailAlloc_2414_, 31, v_varMap_2390_);
lean_ctor_set(v_reuseFailAlloc_2414_, 32, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2414_, 33, v_uppers_2392_);
lean_ctor_set(v_reuseFailAlloc_2414_, 34, v_diseqs_2393_);
lean_ctor_set(v_reuseFailAlloc_2414_, 35, v_assignment_2394_);
lean_ctor_set(v_reuseFailAlloc_2414_, 36, v_conflict_x3f_2396_);
lean_ctor_set(v_reuseFailAlloc_2414_, 37, v_diseqSplits_2397_);
lean_ctor_set(v_reuseFailAlloc_2414_, 38, v_elimEqs_2398_);
lean_ctor_set(v_reuseFailAlloc_2414_, 39, v_elimStack_2399_);
lean_ctor_set(v_reuseFailAlloc_2414_, 40, v_occurs_2400_);
lean_ctor_set(v_reuseFailAlloc_2414_, 41, v_ignored_2401_);
lean_ctor_set_uint8(v_reuseFailAlloc_2414_, sizeof(void*)*42, v_caseSplits_2395_);
v___x_2409_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2410_; lean_object* v___x_2412_; 
v___x_2410_ = lean_array_fset(v_xs_x27_2406_, v_a_2341_, v___x_2409_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v___x_2410_);
v___x_2412_ = v___x_2356_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2410_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v_typeIdOf_2346_);
lean_ctor_set(v_reuseFailAlloc_2413_, 2, v_exprToStructId_2347_);
lean_ctor_set(v_reuseFailAlloc_2413_, 3, v_exprToStructIdEntries_2348_);
lean_ctor_set(v_reuseFailAlloc_2413_, 4, v_forbiddenNatModules_2349_);
lean_ctor_set(v_reuseFailAlloc_2413_, 5, v_natStructs_2350_);
lean_ctor_set(v_reuseFailAlloc_2413_, 6, v_natTypeIdOf_2351_);
lean_ctor_set(v_reuseFailAlloc_2413_, 7, v_exprToNatStructId_2352_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed(lean_object* v_a_2425_, lean_object* v_y_2426_, lean_object* v_fst_2427_, lean_object* v_s_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(v_a_2425_, v_y_2426_, v_fst_2427_, v_s_2428_);
lean_dec(v_y_2426_);
lean_dec(v_a_2425_);
return v_res_2429_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0(void){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object* v_a_2431_, lean_object* v_x_2432_, lean_object* v_c_2433_, lean_object* v_y_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2482_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2450_ = v___x_2447_;
v_isShared_2451_ = v_isSharedCheck_2482_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2447_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2482_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
uint8_t v___x_2452_; 
v___x_2452_ = lean_unbox(v_a_2448_);
lean_dec(v_a_2448_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; 
lean_del_object(v___x_2450_);
v___x_2453_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___y_2456_; lean_object* v_lowers_2464_; lean_object* v_size_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2454_);
lean_dec_ref_known(v___x_2453_, 1);
v_lowers_2464_ = lean_ctor_get(v_a_2454_, 32);
lean_inc_ref(v_lowers_2464_);
lean_dec(v_a_2454_);
v_size_2465_ = lean_ctor_get(v_lowers_2464_, 2);
v___x_2466_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2467_ = lean_nat_dec_lt(v_y_2434_, v_size_2465_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; 
lean_dec_ref(v_lowers_2464_);
v___x_2468_ = l_outOfBounds___redArg(v___x_2466_);
v___y_2456_ = v___x_2468_;
goto v___jp_2455_;
}
else
{
lean_object* v___x_2469_; 
v___x_2469_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2466_, v_lowers_2464_, v_y_2434_);
lean_dec_ref(v_lowers_2464_);
v___y_2456_ = v___x_2469_;
goto v___jp_2455_;
}
v___jp_2455_:
{
lean_object* v___x_2457_; lean_object* v_fst_2458_; lean_object* v_snd_2459_; lean_object* v___f_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2457_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2432_, v___y_2456_);
lean_dec_ref(v___y_2456_);
v_fst_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_fst_2458_);
v_snd_2459_ = lean_ctor_get(v___x_2457_, 1);
lean_inc(v_snd_2459_);
lean_dec_ref(v___x_2457_);
lean_inc(v_a_2435_);
v___f_2460_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2460_, 0, v_a_2435_);
lean_closure_set(v___f_2460_, 1, v_y_2434_);
lean_closure_set(v___f_2460_, 2, v_fst_2458_);
v___x_2461_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2462_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2461_, v___f_2460_, v_a_2436_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v___x_2463_; 
lean_dec_ref_known(v___x_2462_, 1);
v___x_2463_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2431_, v_x_2432_, v_c_2433_, v_snd_2459_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_);
lean_dec(v_snd_2459_);
return v___x_2463_;
}
else
{
lean_dec(v_snd_2459_);
lean_dec_ref(v_c_2433_);
lean_dec(v_x_2432_);
lean_dec(v_a_2431_);
return v___x_2462_;
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_dec(v_y_2434_);
lean_dec_ref(v_c_2433_);
lean_dec(v_x_2432_);
lean_dec(v_a_2431_);
v_a_2470_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2453_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2453_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
else
{
lean_object* v___x_2478_; lean_object* v___x_2480_; 
lean_dec(v_y_2434_);
lean_dec_ref(v_c_2433_);
lean_dec(v_x_2432_);
lean_dec(v_a_2431_);
v___x_2478_ = lean_box(0);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v___x_2478_);
v___x_2480_ = v___x_2450_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2478_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec(v_y_2434_);
lean_dec_ref(v_c_2433_);
lean_dec(v_x_2432_);
lean_dec(v_a_2431_);
v_a_2483_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2447_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2447_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object* v_a_2491_, lean_object* v_x_2492_, lean_object* v_c_2493_, lean_object* v_y_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_2491_, v_x_2492_, v_c_2493_, v_y_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
lean_dec(v_a_2503_);
lean_dec_ref(v_a_2502_);
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec(v_a_2495_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(lean_object* v_a_2508_, lean_object* v_y_2509_, lean_object* v_fst_2510_, lean_object* v_s_2511_){
_start:
{
lean_object* v_structs_2512_; lean_object* v_typeIdOf_2513_; lean_object* v_exprToStructId_2514_; lean_object* v_exprToStructIdEntries_2515_; lean_object* v_forbiddenNatModules_2516_; lean_object* v_natStructs_2517_; lean_object* v_natTypeIdOf_2518_; lean_object* v_exprToNatStructId_2519_; lean_object* v___x_2520_; uint8_t v___x_2521_; 
v_structs_2512_ = lean_ctor_get(v_s_2511_, 0);
v_typeIdOf_2513_ = lean_ctor_get(v_s_2511_, 1);
v_exprToStructId_2514_ = lean_ctor_get(v_s_2511_, 2);
v_exprToStructIdEntries_2515_ = lean_ctor_get(v_s_2511_, 3);
v_forbiddenNatModules_2516_ = lean_ctor_get(v_s_2511_, 4);
v_natStructs_2517_ = lean_ctor_get(v_s_2511_, 5);
v_natTypeIdOf_2518_ = lean_ctor_get(v_s_2511_, 6);
v_exprToNatStructId_2519_ = lean_ctor_get(v_s_2511_, 7);
v___x_2520_ = lean_array_get_size(v_structs_2512_);
v___x_2521_ = lean_nat_dec_lt(v_a_2508_, v___x_2520_);
if (v___x_2521_ == 0)
{
lean_dec_ref(v_fst_2510_);
return v_s_2511_;
}
else
{
lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2583_; 
lean_inc_ref(v_exprToNatStructId_2519_);
lean_inc_ref(v_natTypeIdOf_2518_);
lean_inc_ref(v_natStructs_2517_);
lean_inc_ref(v_forbiddenNatModules_2516_);
lean_inc_ref(v_exprToStructIdEntries_2515_);
lean_inc_ref(v_exprToStructId_2514_);
lean_inc_ref(v_typeIdOf_2513_);
lean_inc_ref(v_structs_2512_);
v_isSharedCheck_2583_ = !lean_is_exclusive(v_s_2511_);
if (v_isSharedCheck_2583_ == 0)
{
lean_object* v_unused_2584_; lean_object* v_unused_2585_; lean_object* v_unused_2586_; lean_object* v_unused_2587_; lean_object* v_unused_2588_; lean_object* v_unused_2589_; lean_object* v_unused_2590_; lean_object* v_unused_2591_; 
v_unused_2584_ = lean_ctor_get(v_s_2511_, 7);
lean_dec(v_unused_2584_);
v_unused_2585_ = lean_ctor_get(v_s_2511_, 6);
lean_dec(v_unused_2585_);
v_unused_2586_ = lean_ctor_get(v_s_2511_, 5);
lean_dec(v_unused_2586_);
v_unused_2587_ = lean_ctor_get(v_s_2511_, 4);
lean_dec(v_unused_2587_);
v_unused_2588_ = lean_ctor_get(v_s_2511_, 3);
lean_dec(v_unused_2588_);
v_unused_2589_ = lean_ctor_get(v_s_2511_, 2);
lean_dec(v_unused_2589_);
v_unused_2590_ = lean_ctor_get(v_s_2511_, 1);
lean_dec(v_unused_2590_);
v_unused_2591_ = lean_ctor_get(v_s_2511_, 0);
lean_dec(v_unused_2591_);
v___x_2523_ = v_s_2511_;
v_isShared_2524_ = v_isSharedCheck_2583_;
goto v_resetjp_2522_;
}
else
{
lean_dec(v_s_2511_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2583_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v_v_2525_; lean_object* v_id_2526_; lean_object* v_ringId_x3f_2527_; lean_object* v_type_2528_; lean_object* v_u_2529_; lean_object* v_intModuleInst_2530_; lean_object* v_leInst_x3f_2531_; lean_object* v_ltInst_x3f_2532_; lean_object* v_lawfulOrderLTInst_x3f_2533_; lean_object* v_isPreorderInst_x3f_2534_; lean_object* v_orderedAddInst_x3f_2535_; lean_object* v_isLinearInst_x3f_2536_; lean_object* v_noNatDivInst_x3f_2537_; lean_object* v_ringInst_x3f_2538_; lean_object* v_commRingInst_x3f_2539_; lean_object* v_orderedRingInst_x3f_2540_; lean_object* v_fieldInst_x3f_2541_; lean_object* v_charInst_x3f_2542_; lean_object* v_zero_2543_; lean_object* v_ofNatZero_2544_; lean_object* v_one_x3f_2545_; lean_object* v_leFn_x3f_2546_; lean_object* v_ltFn_x3f_2547_; lean_object* v_addFn_2548_; lean_object* v_zsmulFn_2549_; lean_object* v_nsmulFn_2550_; lean_object* v_zsmulFn_x3f_2551_; lean_object* v_nsmulFn_x3f_2552_; lean_object* v_homomulFn_x3f_2553_; lean_object* v_subFn_2554_; lean_object* v_negFn_2555_; lean_object* v_vars_2556_; lean_object* v_varMap_2557_; lean_object* v_lowers_2558_; lean_object* v_uppers_2559_; lean_object* v_diseqs_2560_; lean_object* v_assignment_2561_; uint8_t v_caseSplits_2562_; lean_object* v_conflict_x3f_2563_; lean_object* v_diseqSplits_2564_; lean_object* v_elimEqs_2565_; lean_object* v_elimStack_2566_; lean_object* v_occurs_2567_; lean_object* v_ignored_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2582_; 
v_v_2525_ = lean_array_fget(v_structs_2512_, v_a_2508_);
v_id_2526_ = lean_ctor_get(v_v_2525_, 0);
v_ringId_x3f_2527_ = lean_ctor_get(v_v_2525_, 1);
v_type_2528_ = lean_ctor_get(v_v_2525_, 2);
v_u_2529_ = lean_ctor_get(v_v_2525_, 3);
v_intModuleInst_2530_ = lean_ctor_get(v_v_2525_, 4);
v_leInst_x3f_2531_ = lean_ctor_get(v_v_2525_, 5);
v_ltInst_x3f_2532_ = lean_ctor_get(v_v_2525_, 6);
v_lawfulOrderLTInst_x3f_2533_ = lean_ctor_get(v_v_2525_, 7);
v_isPreorderInst_x3f_2534_ = lean_ctor_get(v_v_2525_, 8);
v_orderedAddInst_x3f_2535_ = lean_ctor_get(v_v_2525_, 9);
v_isLinearInst_x3f_2536_ = lean_ctor_get(v_v_2525_, 10);
v_noNatDivInst_x3f_2537_ = lean_ctor_get(v_v_2525_, 11);
v_ringInst_x3f_2538_ = lean_ctor_get(v_v_2525_, 12);
v_commRingInst_x3f_2539_ = lean_ctor_get(v_v_2525_, 13);
v_orderedRingInst_x3f_2540_ = lean_ctor_get(v_v_2525_, 14);
v_fieldInst_x3f_2541_ = lean_ctor_get(v_v_2525_, 15);
v_charInst_x3f_2542_ = lean_ctor_get(v_v_2525_, 16);
v_zero_2543_ = lean_ctor_get(v_v_2525_, 17);
v_ofNatZero_2544_ = lean_ctor_get(v_v_2525_, 18);
v_one_x3f_2545_ = lean_ctor_get(v_v_2525_, 19);
v_leFn_x3f_2546_ = lean_ctor_get(v_v_2525_, 20);
v_ltFn_x3f_2547_ = lean_ctor_get(v_v_2525_, 21);
v_addFn_2548_ = lean_ctor_get(v_v_2525_, 22);
v_zsmulFn_2549_ = lean_ctor_get(v_v_2525_, 23);
v_nsmulFn_2550_ = lean_ctor_get(v_v_2525_, 24);
v_zsmulFn_x3f_2551_ = lean_ctor_get(v_v_2525_, 25);
v_nsmulFn_x3f_2552_ = lean_ctor_get(v_v_2525_, 26);
v_homomulFn_x3f_2553_ = lean_ctor_get(v_v_2525_, 27);
v_subFn_2554_ = lean_ctor_get(v_v_2525_, 28);
v_negFn_2555_ = lean_ctor_get(v_v_2525_, 29);
v_vars_2556_ = lean_ctor_get(v_v_2525_, 30);
v_varMap_2557_ = lean_ctor_get(v_v_2525_, 31);
v_lowers_2558_ = lean_ctor_get(v_v_2525_, 32);
v_uppers_2559_ = lean_ctor_get(v_v_2525_, 33);
v_diseqs_2560_ = lean_ctor_get(v_v_2525_, 34);
v_assignment_2561_ = lean_ctor_get(v_v_2525_, 35);
v_caseSplits_2562_ = lean_ctor_get_uint8(v_v_2525_, sizeof(void*)*42);
v_conflict_x3f_2563_ = lean_ctor_get(v_v_2525_, 36);
v_diseqSplits_2564_ = lean_ctor_get(v_v_2525_, 37);
v_elimEqs_2565_ = lean_ctor_get(v_v_2525_, 38);
v_elimStack_2566_ = lean_ctor_get(v_v_2525_, 39);
v_occurs_2567_ = lean_ctor_get(v_v_2525_, 40);
v_ignored_2568_ = lean_ctor_get(v_v_2525_, 41);
v_isSharedCheck_2582_ = !lean_is_exclusive(v_v_2525_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2570_ = v_v_2525_;
v_isShared_2571_ = v_isSharedCheck_2582_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_ignored_2568_);
lean_inc(v_occurs_2567_);
lean_inc(v_elimStack_2566_);
lean_inc(v_elimEqs_2565_);
lean_inc(v_diseqSplits_2564_);
lean_inc(v_conflict_x3f_2563_);
lean_inc(v_assignment_2561_);
lean_inc(v_diseqs_2560_);
lean_inc(v_uppers_2559_);
lean_inc(v_lowers_2558_);
lean_inc(v_varMap_2557_);
lean_inc(v_vars_2556_);
lean_inc(v_negFn_2555_);
lean_inc(v_subFn_2554_);
lean_inc(v_homomulFn_x3f_2553_);
lean_inc(v_nsmulFn_x3f_2552_);
lean_inc(v_zsmulFn_x3f_2551_);
lean_inc(v_nsmulFn_2550_);
lean_inc(v_zsmulFn_2549_);
lean_inc(v_addFn_2548_);
lean_inc(v_ltFn_x3f_2547_);
lean_inc(v_leFn_x3f_2546_);
lean_inc(v_one_x3f_2545_);
lean_inc(v_ofNatZero_2544_);
lean_inc(v_zero_2543_);
lean_inc(v_charInst_x3f_2542_);
lean_inc(v_fieldInst_x3f_2541_);
lean_inc(v_orderedRingInst_x3f_2540_);
lean_inc(v_commRingInst_x3f_2539_);
lean_inc(v_ringInst_x3f_2538_);
lean_inc(v_noNatDivInst_x3f_2537_);
lean_inc(v_isLinearInst_x3f_2536_);
lean_inc(v_orderedAddInst_x3f_2535_);
lean_inc(v_isPreorderInst_x3f_2534_);
lean_inc(v_lawfulOrderLTInst_x3f_2533_);
lean_inc(v_ltInst_x3f_2532_);
lean_inc(v_leInst_x3f_2531_);
lean_inc(v_intModuleInst_2530_);
lean_inc(v_u_2529_);
lean_inc(v_type_2528_);
lean_inc(v_ringId_x3f_2527_);
lean_inc(v_id_2526_);
lean_dec(v_v_2525_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2582_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v_xs_x27_2573_; lean_object* v___x_2574_; lean_object* v___x_2576_; 
v___x_2572_ = lean_box(0);
v_xs_x27_2573_ = lean_array_fset(v_structs_2512_, v_a_2508_, v___x_2572_);
v___x_2574_ = l_Lean_PersistentArray_set___redArg(v_uppers_2559_, v_y_2509_, v_fst_2510_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 33, v___x_2574_);
v___x_2576_ = v___x_2570_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_id_2526_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_ringId_x3f_2527_);
lean_ctor_set(v_reuseFailAlloc_2581_, 2, v_type_2528_);
lean_ctor_set(v_reuseFailAlloc_2581_, 3, v_u_2529_);
lean_ctor_set(v_reuseFailAlloc_2581_, 4, v_intModuleInst_2530_);
lean_ctor_set(v_reuseFailAlloc_2581_, 5, v_leInst_x3f_2531_);
lean_ctor_set(v_reuseFailAlloc_2581_, 6, v_ltInst_x3f_2532_);
lean_ctor_set(v_reuseFailAlloc_2581_, 7, v_lawfulOrderLTInst_x3f_2533_);
lean_ctor_set(v_reuseFailAlloc_2581_, 8, v_isPreorderInst_x3f_2534_);
lean_ctor_set(v_reuseFailAlloc_2581_, 9, v_orderedAddInst_x3f_2535_);
lean_ctor_set(v_reuseFailAlloc_2581_, 10, v_isLinearInst_x3f_2536_);
lean_ctor_set(v_reuseFailAlloc_2581_, 11, v_noNatDivInst_x3f_2537_);
lean_ctor_set(v_reuseFailAlloc_2581_, 12, v_ringInst_x3f_2538_);
lean_ctor_set(v_reuseFailAlloc_2581_, 13, v_commRingInst_x3f_2539_);
lean_ctor_set(v_reuseFailAlloc_2581_, 14, v_orderedRingInst_x3f_2540_);
lean_ctor_set(v_reuseFailAlloc_2581_, 15, v_fieldInst_x3f_2541_);
lean_ctor_set(v_reuseFailAlloc_2581_, 16, v_charInst_x3f_2542_);
lean_ctor_set(v_reuseFailAlloc_2581_, 17, v_zero_2543_);
lean_ctor_set(v_reuseFailAlloc_2581_, 18, v_ofNatZero_2544_);
lean_ctor_set(v_reuseFailAlloc_2581_, 19, v_one_x3f_2545_);
lean_ctor_set(v_reuseFailAlloc_2581_, 20, v_leFn_x3f_2546_);
lean_ctor_set(v_reuseFailAlloc_2581_, 21, v_ltFn_x3f_2547_);
lean_ctor_set(v_reuseFailAlloc_2581_, 22, v_addFn_2548_);
lean_ctor_set(v_reuseFailAlloc_2581_, 23, v_zsmulFn_2549_);
lean_ctor_set(v_reuseFailAlloc_2581_, 24, v_nsmulFn_2550_);
lean_ctor_set(v_reuseFailAlloc_2581_, 25, v_zsmulFn_x3f_2551_);
lean_ctor_set(v_reuseFailAlloc_2581_, 26, v_nsmulFn_x3f_2552_);
lean_ctor_set(v_reuseFailAlloc_2581_, 27, v_homomulFn_x3f_2553_);
lean_ctor_set(v_reuseFailAlloc_2581_, 28, v_subFn_2554_);
lean_ctor_set(v_reuseFailAlloc_2581_, 29, v_negFn_2555_);
lean_ctor_set(v_reuseFailAlloc_2581_, 30, v_vars_2556_);
lean_ctor_set(v_reuseFailAlloc_2581_, 31, v_varMap_2557_);
lean_ctor_set(v_reuseFailAlloc_2581_, 32, v_lowers_2558_);
lean_ctor_set(v_reuseFailAlloc_2581_, 33, v___x_2574_);
lean_ctor_set(v_reuseFailAlloc_2581_, 34, v_diseqs_2560_);
lean_ctor_set(v_reuseFailAlloc_2581_, 35, v_assignment_2561_);
lean_ctor_set(v_reuseFailAlloc_2581_, 36, v_conflict_x3f_2563_);
lean_ctor_set(v_reuseFailAlloc_2581_, 37, v_diseqSplits_2564_);
lean_ctor_set(v_reuseFailAlloc_2581_, 38, v_elimEqs_2565_);
lean_ctor_set(v_reuseFailAlloc_2581_, 39, v_elimStack_2566_);
lean_ctor_set(v_reuseFailAlloc_2581_, 40, v_occurs_2567_);
lean_ctor_set(v_reuseFailAlloc_2581_, 41, v_ignored_2568_);
lean_ctor_set_uint8(v_reuseFailAlloc_2581_, sizeof(void*)*42, v_caseSplits_2562_);
v___x_2576_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
lean_object* v___x_2577_; lean_object* v___x_2579_; 
v___x_2577_ = lean_array_fset(v_xs_x27_2573_, v_a_2508_, v___x_2576_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 0, v___x_2577_);
v___x_2579_ = v___x_2523_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_typeIdOf_2513_);
lean_ctor_set(v_reuseFailAlloc_2580_, 2, v_exprToStructId_2514_);
lean_ctor_set(v_reuseFailAlloc_2580_, 3, v_exprToStructIdEntries_2515_);
lean_ctor_set(v_reuseFailAlloc_2580_, 4, v_forbiddenNatModules_2516_);
lean_ctor_set(v_reuseFailAlloc_2580_, 5, v_natStructs_2517_);
lean_ctor_set(v_reuseFailAlloc_2580_, 6, v_natTypeIdOf_2518_);
lean_ctor_set(v_reuseFailAlloc_2580_, 7, v_exprToNatStructId_2519_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed(lean_object* v_a_2592_, lean_object* v_y_2593_, lean_object* v_fst_2594_, lean_object* v_s_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(v_a_2592_, v_y_2593_, v_fst_2594_, v_s_2595_);
lean_dec(v_y_2593_);
lean_dec(v_a_2592_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object* v_a_2597_, lean_object* v_x_2598_, lean_object* v_c_2599_, lean_object* v_y_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2648_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2648_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2648_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
uint8_t v___x_2618_; 
v___x_2618_ = lean_unbox(v_a_2614_);
lean_dec(v_a_2614_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; 
lean_del_object(v___x_2616_);
v___x_2619_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___y_2622_; lean_object* v_uppers_2630_; lean_object* v_size_2631_; lean_object* v___x_2632_; uint8_t v___x_2633_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2620_);
lean_dec_ref_known(v___x_2619_, 1);
v_uppers_2630_ = lean_ctor_get(v_a_2620_, 33);
lean_inc_ref(v_uppers_2630_);
lean_dec(v_a_2620_);
v_size_2631_ = lean_ctor_get(v_uppers_2630_, 2);
v___x_2632_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2633_ = lean_nat_dec_lt(v_y_2600_, v_size_2631_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; 
lean_dec_ref(v_uppers_2630_);
v___x_2634_ = l_outOfBounds___redArg(v___x_2632_);
v___y_2622_ = v___x_2634_;
goto v___jp_2621_;
}
else
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2632_, v_uppers_2630_, v_y_2600_);
lean_dec_ref(v_uppers_2630_);
v___y_2622_ = v___x_2635_;
goto v___jp_2621_;
}
v___jp_2621_:
{
lean_object* v___x_2623_; lean_object* v_fst_2624_; lean_object* v_snd_2625_; lean_object* v___f_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2623_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2598_, v___y_2622_);
lean_dec_ref(v___y_2622_);
v_fst_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_fst_2624_);
v_snd_2625_ = lean_ctor_get(v___x_2623_, 1);
lean_inc(v_snd_2625_);
lean_dec_ref(v___x_2623_);
lean_inc(v_a_2601_);
v___f_2626_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2626_, 0, v_a_2601_);
lean_closure_set(v___f_2626_, 1, v_y_2600_);
lean_closure_set(v___f_2626_, 2, v_fst_2624_);
v___x_2627_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2628_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2627_, v___f_2626_, v_a_2602_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v___x_2629_; 
lean_dec_ref_known(v___x_2628_, 1);
v___x_2629_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2597_, v_x_2598_, v_c_2599_, v_snd_2625_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_);
lean_dec(v_snd_2625_);
return v___x_2629_;
}
else
{
lean_dec(v_snd_2625_);
lean_dec_ref(v_c_2599_);
lean_dec(v_x_2598_);
lean_dec(v_a_2597_);
return v___x_2628_;
}
}
}
else
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
lean_dec(v_y_2600_);
lean_dec_ref(v_c_2599_);
lean_dec(v_x_2598_);
lean_dec(v_a_2597_);
v_a_2636_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2619_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2619_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
else
{
lean_object* v___x_2644_; lean_object* v___x_2646_; 
lean_dec(v_y_2600_);
lean_dec_ref(v_c_2599_);
lean_dec(v_x_2598_);
lean_dec(v_a_2597_);
v___x_2644_ = lean_box(0);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2644_);
v___x_2646_ = v___x_2616_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_dec(v_y_2600_);
lean_dec_ref(v_c_2599_);
lean_dec(v_x_2598_);
lean_dec(v_a_2597_);
v_a_2649_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2613_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2613_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object* v_a_2657_, lean_object* v_x_2658_, lean_object* v_c_2659_, lean_object* v_y_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_2657_, v_x_2658_, v_c_2659_, v_y_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
lean_dec(v_a_2671_);
lean_dec_ref(v_a_2670_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec(v_a_2661_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(lean_object* v___y_2674_, lean_object* v_a_2675_, lean_object* v_s_2676_){
_start:
{
lean_object* v_structs_2677_; lean_object* v_typeIdOf_2678_; lean_object* v_exprToStructId_2679_; lean_object* v_exprToStructIdEntries_2680_; lean_object* v_forbiddenNatModules_2681_; lean_object* v_natStructs_2682_; lean_object* v_natTypeIdOf_2683_; lean_object* v_exprToNatStructId_2684_; lean_object* v___x_2685_; uint8_t v___x_2686_; 
v_structs_2677_ = lean_ctor_get(v_s_2676_, 0);
v_typeIdOf_2678_ = lean_ctor_get(v_s_2676_, 1);
v_exprToStructId_2679_ = lean_ctor_get(v_s_2676_, 2);
v_exprToStructIdEntries_2680_ = lean_ctor_get(v_s_2676_, 3);
v_forbiddenNatModules_2681_ = lean_ctor_get(v_s_2676_, 4);
v_natStructs_2682_ = lean_ctor_get(v_s_2676_, 5);
v_natTypeIdOf_2683_ = lean_ctor_get(v_s_2676_, 6);
v_exprToNatStructId_2684_ = lean_ctor_get(v_s_2676_, 7);
v___x_2685_ = lean_array_get_size(v_structs_2677_);
v___x_2686_ = lean_nat_dec_lt(v___y_2674_, v___x_2685_);
if (v___x_2686_ == 0)
{
lean_dec_ref(v_a_2675_);
return v_s_2676_;
}
else
{
lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2748_; 
lean_inc_ref(v_exprToNatStructId_2684_);
lean_inc_ref(v_natTypeIdOf_2683_);
lean_inc_ref(v_natStructs_2682_);
lean_inc_ref(v_forbiddenNatModules_2681_);
lean_inc_ref(v_exprToStructIdEntries_2680_);
lean_inc_ref(v_exprToStructId_2679_);
lean_inc_ref(v_typeIdOf_2678_);
lean_inc_ref(v_structs_2677_);
v_isSharedCheck_2748_ = !lean_is_exclusive(v_s_2676_);
if (v_isSharedCheck_2748_ == 0)
{
lean_object* v_unused_2749_; lean_object* v_unused_2750_; lean_object* v_unused_2751_; lean_object* v_unused_2752_; lean_object* v_unused_2753_; lean_object* v_unused_2754_; lean_object* v_unused_2755_; lean_object* v_unused_2756_; 
v_unused_2749_ = lean_ctor_get(v_s_2676_, 7);
lean_dec(v_unused_2749_);
v_unused_2750_ = lean_ctor_get(v_s_2676_, 6);
lean_dec(v_unused_2750_);
v_unused_2751_ = lean_ctor_get(v_s_2676_, 5);
lean_dec(v_unused_2751_);
v_unused_2752_ = lean_ctor_get(v_s_2676_, 4);
lean_dec(v_unused_2752_);
v_unused_2753_ = lean_ctor_get(v_s_2676_, 3);
lean_dec(v_unused_2753_);
v_unused_2754_ = lean_ctor_get(v_s_2676_, 2);
lean_dec(v_unused_2754_);
v_unused_2755_ = lean_ctor_get(v_s_2676_, 1);
lean_dec(v_unused_2755_);
v_unused_2756_ = lean_ctor_get(v_s_2676_, 0);
lean_dec(v_unused_2756_);
v___x_2688_ = v_s_2676_;
v_isShared_2689_ = v_isSharedCheck_2748_;
goto v_resetjp_2687_;
}
else
{
lean_dec(v_s_2676_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2748_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v_v_2690_; lean_object* v_id_2691_; lean_object* v_ringId_x3f_2692_; lean_object* v_type_2693_; lean_object* v_u_2694_; lean_object* v_intModuleInst_2695_; lean_object* v_leInst_x3f_2696_; lean_object* v_ltInst_x3f_2697_; lean_object* v_lawfulOrderLTInst_x3f_2698_; lean_object* v_isPreorderInst_x3f_2699_; lean_object* v_orderedAddInst_x3f_2700_; lean_object* v_isLinearInst_x3f_2701_; lean_object* v_noNatDivInst_x3f_2702_; lean_object* v_ringInst_x3f_2703_; lean_object* v_commRingInst_x3f_2704_; lean_object* v_orderedRingInst_x3f_2705_; lean_object* v_fieldInst_x3f_2706_; lean_object* v_charInst_x3f_2707_; lean_object* v_zero_2708_; lean_object* v_ofNatZero_2709_; lean_object* v_one_x3f_2710_; lean_object* v_leFn_x3f_2711_; lean_object* v_ltFn_x3f_2712_; lean_object* v_addFn_2713_; lean_object* v_zsmulFn_2714_; lean_object* v_nsmulFn_2715_; lean_object* v_zsmulFn_x3f_2716_; lean_object* v_nsmulFn_x3f_2717_; lean_object* v_homomulFn_x3f_2718_; lean_object* v_subFn_2719_; lean_object* v_negFn_2720_; lean_object* v_vars_2721_; lean_object* v_varMap_2722_; lean_object* v_lowers_2723_; lean_object* v_uppers_2724_; lean_object* v_diseqs_2725_; lean_object* v_assignment_2726_; uint8_t v_caseSplits_2727_; lean_object* v_conflict_x3f_2728_; lean_object* v_diseqSplits_2729_; lean_object* v_elimEqs_2730_; lean_object* v_elimStack_2731_; lean_object* v_occurs_2732_; lean_object* v_ignored_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2747_; 
v_v_2690_ = lean_array_fget(v_structs_2677_, v___y_2674_);
v_id_2691_ = lean_ctor_get(v_v_2690_, 0);
v_ringId_x3f_2692_ = lean_ctor_get(v_v_2690_, 1);
v_type_2693_ = lean_ctor_get(v_v_2690_, 2);
v_u_2694_ = lean_ctor_get(v_v_2690_, 3);
v_intModuleInst_2695_ = lean_ctor_get(v_v_2690_, 4);
v_leInst_x3f_2696_ = lean_ctor_get(v_v_2690_, 5);
v_ltInst_x3f_2697_ = lean_ctor_get(v_v_2690_, 6);
v_lawfulOrderLTInst_x3f_2698_ = lean_ctor_get(v_v_2690_, 7);
v_isPreorderInst_x3f_2699_ = lean_ctor_get(v_v_2690_, 8);
v_orderedAddInst_x3f_2700_ = lean_ctor_get(v_v_2690_, 9);
v_isLinearInst_x3f_2701_ = lean_ctor_get(v_v_2690_, 10);
v_noNatDivInst_x3f_2702_ = lean_ctor_get(v_v_2690_, 11);
v_ringInst_x3f_2703_ = lean_ctor_get(v_v_2690_, 12);
v_commRingInst_x3f_2704_ = lean_ctor_get(v_v_2690_, 13);
v_orderedRingInst_x3f_2705_ = lean_ctor_get(v_v_2690_, 14);
v_fieldInst_x3f_2706_ = lean_ctor_get(v_v_2690_, 15);
v_charInst_x3f_2707_ = lean_ctor_get(v_v_2690_, 16);
v_zero_2708_ = lean_ctor_get(v_v_2690_, 17);
v_ofNatZero_2709_ = lean_ctor_get(v_v_2690_, 18);
v_one_x3f_2710_ = lean_ctor_get(v_v_2690_, 19);
v_leFn_x3f_2711_ = lean_ctor_get(v_v_2690_, 20);
v_ltFn_x3f_2712_ = lean_ctor_get(v_v_2690_, 21);
v_addFn_2713_ = lean_ctor_get(v_v_2690_, 22);
v_zsmulFn_2714_ = lean_ctor_get(v_v_2690_, 23);
v_nsmulFn_2715_ = lean_ctor_get(v_v_2690_, 24);
v_zsmulFn_x3f_2716_ = lean_ctor_get(v_v_2690_, 25);
v_nsmulFn_x3f_2717_ = lean_ctor_get(v_v_2690_, 26);
v_homomulFn_x3f_2718_ = lean_ctor_get(v_v_2690_, 27);
v_subFn_2719_ = lean_ctor_get(v_v_2690_, 28);
v_negFn_2720_ = lean_ctor_get(v_v_2690_, 29);
v_vars_2721_ = lean_ctor_get(v_v_2690_, 30);
v_varMap_2722_ = lean_ctor_get(v_v_2690_, 31);
v_lowers_2723_ = lean_ctor_get(v_v_2690_, 32);
v_uppers_2724_ = lean_ctor_get(v_v_2690_, 33);
v_diseqs_2725_ = lean_ctor_get(v_v_2690_, 34);
v_assignment_2726_ = lean_ctor_get(v_v_2690_, 35);
v_caseSplits_2727_ = lean_ctor_get_uint8(v_v_2690_, sizeof(void*)*42);
v_conflict_x3f_2728_ = lean_ctor_get(v_v_2690_, 36);
v_diseqSplits_2729_ = lean_ctor_get(v_v_2690_, 37);
v_elimEqs_2730_ = lean_ctor_get(v_v_2690_, 38);
v_elimStack_2731_ = lean_ctor_get(v_v_2690_, 39);
v_occurs_2732_ = lean_ctor_get(v_v_2690_, 40);
v_ignored_2733_ = lean_ctor_get(v_v_2690_, 41);
v_isSharedCheck_2747_ = !lean_is_exclusive(v_v_2690_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2735_ = v_v_2690_;
v_isShared_2736_ = v_isSharedCheck_2747_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_ignored_2733_);
lean_inc(v_occurs_2732_);
lean_inc(v_elimStack_2731_);
lean_inc(v_elimEqs_2730_);
lean_inc(v_diseqSplits_2729_);
lean_inc(v_conflict_x3f_2728_);
lean_inc(v_assignment_2726_);
lean_inc(v_diseqs_2725_);
lean_inc(v_uppers_2724_);
lean_inc(v_lowers_2723_);
lean_inc(v_varMap_2722_);
lean_inc(v_vars_2721_);
lean_inc(v_negFn_2720_);
lean_inc(v_subFn_2719_);
lean_inc(v_homomulFn_x3f_2718_);
lean_inc(v_nsmulFn_x3f_2717_);
lean_inc(v_zsmulFn_x3f_2716_);
lean_inc(v_nsmulFn_2715_);
lean_inc(v_zsmulFn_2714_);
lean_inc(v_addFn_2713_);
lean_inc(v_ltFn_x3f_2712_);
lean_inc(v_leFn_x3f_2711_);
lean_inc(v_one_x3f_2710_);
lean_inc(v_ofNatZero_2709_);
lean_inc(v_zero_2708_);
lean_inc(v_charInst_x3f_2707_);
lean_inc(v_fieldInst_x3f_2706_);
lean_inc(v_orderedRingInst_x3f_2705_);
lean_inc(v_commRingInst_x3f_2704_);
lean_inc(v_ringInst_x3f_2703_);
lean_inc(v_noNatDivInst_x3f_2702_);
lean_inc(v_isLinearInst_x3f_2701_);
lean_inc(v_orderedAddInst_x3f_2700_);
lean_inc(v_isPreorderInst_x3f_2699_);
lean_inc(v_lawfulOrderLTInst_x3f_2698_);
lean_inc(v_ltInst_x3f_2697_);
lean_inc(v_leInst_x3f_2696_);
lean_inc(v_intModuleInst_2695_);
lean_inc(v_u_2694_);
lean_inc(v_type_2693_);
lean_inc(v_ringId_x3f_2692_);
lean_inc(v_id_2691_);
lean_dec(v_v_2690_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2747_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2737_; lean_object* v_xs_x27_2738_; lean_object* v___x_2739_; lean_object* v___x_2741_; 
v___x_2737_ = lean_box(0);
v_xs_x27_2738_ = lean_array_fset(v_structs_2677_, v___y_2674_, v___x_2737_);
v___x_2739_ = l_Lean_PersistentArray_push___redArg(v_ignored_2733_, v_a_2675_);
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 41, v___x_2739_);
v___x_2741_ = v___x_2735_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_id_2691_);
lean_ctor_set(v_reuseFailAlloc_2746_, 1, v_ringId_x3f_2692_);
lean_ctor_set(v_reuseFailAlloc_2746_, 2, v_type_2693_);
lean_ctor_set(v_reuseFailAlloc_2746_, 3, v_u_2694_);
lean_ctor_set(v_reuseFailAlloc_2746_, 4, v_intModuleInst_2695_);
lean_ctor_set(v_reuseFailAlloc_2746_, 5, v_leInst_x3f_2696_);
lean_ctor_set(v_reuseFailAlloc_2746_, 6, v_ltInst_x3f_2697_);
lean_ctor_set(v_reuseFailAlloc_2746_, 7, v_lawfulOrderLTInst_x3f_2698_);
lean_ctor_set(v_reuseFailAlloc_2746_, 8, v_isPreorderInst_x3f_2699_);
lean_ctor_set(v_reuseFailAlloc_2746_, 9, v_orderedAddInst_x3f_2700_);
lean_ctor_set(v_reuseFailAlloc_2746_, 10, v_isLinearInst_x3f_2701_);
lean_ctor_set(v_reuseFailAlloc_2746_, 11, v_noNatDivInst_x3f_2702_);
lean_ctor_set(v_reuseFailAlloc_2746_, 12, v_ringInst_x3f_2703_);
lean_ctor_set(v_reuseFailAlloc_2746_, 13, v_commRingInst_x3f_2704_);
lean_ctor_set(v_reuseFailAlloc_2746_, 14, v_orderedRingInst_x3f_2705_);
lean_ctor_set(v_reuseFailAlloc_2746_, 15, v_fieldInst_x3f_2706_);
lean_ctor_set(v_reuseFailAlloc_2746_, 16, v_charInst_x3f_2707_);
lean_ctor_set(v_reuseFailAlloc_2746_, 17, v_zero_2708_);
lean_ctor_set(v_reuseFailAlloc_2746_, 18, v_ofNatZero_2709_);
lean_ctor_set(v_reuseFailAlloc_2746_, 19, v_one_x3f_2710_);
lean_ctor_set(v_reuseFailAlloc_2746_, 20, v_leFn_x3f_2711_);
lean_ctor_set(v_reuseFailAlloc_2746_, 21, v_ltFn_x3f_2712_);
lean_ctor_set(v_reuseFailAlloc_2746_, 22, v_addFn_2713_);
lean_ctor_set(v_reuseFailAlloc_2746_, 23, v_zsmulFn_2714_);
lean_ctor_set(v_reuseFailAlloc_2746_, 24, v_nsmulFn_2715_);
lean_ctor_set(v_reuseFailAlloc_2746_, 25, v_zsmulFn_x3f_2716_);
lean_ctor_set(v_reuseFailAlloc_2746_, 26, v_nsmulFn_x3f_2717_);
lean_ctor_set(v_reuseFailAlloc_2746_, 27, v_homomulFn_x3f_2718_);
lean_ctor_set(v_reuseFailAlloc_2746_, 28, v_subFn_2719_);
lean_ctor_set(v_reuseFailAlloc_2746_, 29, v_negFn_2720_);
lean_ctor_set(v_reuseFailAlloc_2746_, 30, v_vars_2721_);
lean_ctor_set(v_reuseFailAlloc_2746_, 31, v_varMap_2722_);
lean_ctor_set(v_reuseFailAlloc_2746_, 32, v_lowers_2723_);
lean_ctor_set(v_reuseFailAlloc_2746_, 33, v_uppers_2724_);
lean_ctor_set(v_reuseFailAlloc_2746_, 34, v_diseqs_2725_);
lean_ctor_set(v_reuseFailAlloc_2746_, 35, v_assignment_2726_);
lean_ctor_set(v_reuseFailAlloc_2746_, 36, v_conflict_x3f_2728_);
lean_ctor_set(v_reuseFailAlloc_2746_, 37, v_diseqSplits_2729_);
lean_ctor_set(v_reuseFailAlloc_2746_, 38, v_elimEqs_2730_);
lean_ctor_set(v_reuseFailAlloc_2746_, 39, v_elimStack_2731_);
lean_ctor_set(v_reuseFailAlloc_2746_, 40, v_occurs_2732_);
lean_ctor_set(v_reuseFailAlloc_2746_, 41, v___x_2739_);
lean_ctor_set_uint8(v_reuseFailAlloc_2746_, sizeof(void*)*42, v_caseSplits_2727_);
v___x_2741_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
lean_object* v___x_2742_; lean_object* v___x_2744_; 
v___x_2742_ = lean_array_fset(v_xs_x27_2738_, v___y_2674_, v___x_2741_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2742_);
v___x_2744_ = v___x_2688_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2742_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v_typeIdOf_2678_);
lean_ctor_set(v_reuseFailAlloc_2745_, 2, v_exprToStructId_2679_);
lean_ctor_set(v_reuseFailAlloc_2745_, 3, v_exprToStructIdEntries_2680_);
lean_ctor_set(v_reuseFailAlloc_2745_, 4, v_forbiddenNatModules_2681_);
lean_ctor_set(v_reuseFailAlloc_2745_, 5, v_natStructs_2682_);
lean_ctor_set(v_reuseFailAlloc_2745_, 6, v_natTypeIdOf_2683_);
lean_ctor_set(v_reuseFailAlloc_2745_, 7, v_exprToNatStructId_2684_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed(lean_object* v___y_2757_, lean_object* v_a_2758_, lean_object* v_s_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(v___y_2757_, v_a_2758_, v_s_2759_);
lean_dec(v___y_2757_);
return v_res_2760_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3(void){
_start:
{
lean_object* v_cls_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v_cls_2768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2769_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_2770_ = l_Lean_Name_append(v___x_2769_, v_cls_2768_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object* v_c_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v_options_2809_; uint8_t v_hasTrace_2810_; 
v_options_2809_ = lean_ctor_get(v_a_2781_, 2);
v_hasTrace_2810_ = lean_ctor_get_uint8(v_options_2809_, sizeof(void*)*1);
if (v_hasTrace_2810_ == 0)
{
v___y_2785_ = v_a_2772_;
v___y_2786_ = v_a_2773_;
v___y_2787_ = v_a_2774_;
v___y_2788_ = v_a_2775_;
v___y_2789_ = v_a_2776_;
v___y_2790_ = v_a_2777_;
v___y_2791_ = v_a_2778_;
v___y_2792_ = v_a_2779_;
v___y_2793_ = v_a_2780_;
v___y_2794_ = v_a_2781_;
v___y_2795_ = v_a_2782_;
goto v___jp_2784_;
}
else
{
lean_object* v_inheritedTraceOptions_2811_; lean_object* v_cls_2812_; lean_object* v___x_2813_; uint8_t v___x_2814_; 
v_inheritedTraceOptions_2811_ = lean_ctor_get(v_a_2781_, 13);
v_cls_2812_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2813_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3);
v___x_2814_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2811_, v_options_2809_, v___x_2813_);
if (v___x_2814_ == 0)
{
v___y_2785_ = v_a_2772_;
v___y_2786_ = v_a_2773_;
v___y_2787_ = v_a_2774_;
v___y_2788_ = v_a_2775_;
v___y_2789_ = v_a_2776_;
v___y_2790_ = v_a_2777_;
v___y_2791_ = v_a_2778_;
v___y_2792_ = v_a_2779_;
v___y_2793_ = v_a_2780_;
v___y_2794_ = v_a_2781_;
v___y_2795_ = v_a_2782_;
goto v___jp_2784_;
}
else
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2815_, 1);
v___x_2817_ = l_Lean_MessageData_ofExpr(v_a_2816_);
v___x_2818_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_2812_, v___x_2817_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_dec_ref_known(v___x_2818_, 1);
v___y_2785_ = v_a_2772_;
v___y_2786_ = v_a_2773_;
v___y_2787_ = v_a_2774_;
v___y_2788_ = v_a_2775_;
v___y_2789_ = v_a_2776_;
v___y_2790_ = v_a_2777_;
v___y_2791_ = v_a_2778_;
v___y_2792_ = v_a_2779_;
v___y_2793_ = v_a_2780_;
v___y_2794_ = v_a_2781_;
v___y_2795_ = v_a_2782_;
goto v___jp_2784_;
}
else
{
return v___x_2818_;
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
v_a_2819_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2815_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2815_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
}
v___jp_2784_:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2771_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v___f_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref_known(v___x_2796_, 1);
lean_inc(v___y_2785_);
v___f_2798_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2798_, 0, v___y_2785_);
lean_closure_set(v___f_2798_, 1, v_a_2797_);
v___x_2799_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2800_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2799_, v___f_2798_, v___y_2786_);
return v___x_2800_;
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
v_a_2801_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2796_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2796_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object* v_c_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_);
lean_dec(v_a_2838_);
lean_dec_ref(v_a_2837_);
lean_dec(v_a_2836_);
lean_dec_ref(v_a_2835_);
lean_dec(v_a_2834_);
lean_dec_ref(v_a_2833_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
lean_dec(v_a_2829_);
lean_dec(v_a_2828_);
lean_dec_ref(v_c_2827_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object* v_c_u2082_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_p_2854_; lean_object* v_fileName_2855_; lean_object* v_fileMap_2856_; lean_object* v_options_2857_; lean_object* v_currRecDepth_2858_; lean_object* v_maxRecDepth_2859_; lean_object* v_ref_2860_; lean_object* v_currNamespace_2861_; lean_object* v_openDecls_2862_; lean_object* v_initHeartbeats_2863_; lean_object* v_maxHeartbeats_2864_; lean_object* v_quotContext_2865_; lean_object* v_currMacroScope_2866_; uint8_t v_diag_2867_; lean_object* v_cancelTk_x3f_2868_; uint8_t v_suppressElabErrors_2869_; lean_object* v_inheritedTraceOptions_2870_; uint8_t v___y_2872_; lean_object* v___x_2924_; uint8_t v___x_2925_; uint8_t v___x_2926_; 
v_p_2854_ = lean_ctor_get(v_c_u2082_2841_, 0);
v_fileName_2855_ = lean_ctor_get(v_a_2851_, 0);
lean_inc_ref(v_fileName_2855_);
v_fileMap_2856_ = lean_ctor_get(v_a_2851_, 1);
lean_inc_ref(v_fileMap_2856_);
v_options_2857_ = lean_ctor_get(v_a_2851_, 2);
lean_inc_ref(v_options_2857_);
v_currRecDepth_2858_ = lean_ctor_get(v_a_2851_, 3);
lean_inc(v_currRecDepth_2858_);
v_maxRecDepth_2859_ = lean_ctor_get(v_a_2851_, 4);
lean_inc(v_maxRecDepth_2859_);
v_ref_2860_ = lean_ctor_get(v_a_2851_, 5);
lean_inc(v_ref_2860_);
v_currNamespace_2861_ = lean_ctor_get(v_a_2851_, 6);
lean_inc(v_currNamespace_2861_);
v_openDecls_2862_ = lean_ctor_get(v_a_2851_, 7);
lean_inc(v_openDecls_2862_);
v_initHeartbeats_2863_ = lean_ctor_get(v_a_2851_, 8);
lean_inc(v_initHeartbeats_2863_);
v_maxHeartbeats_2864_ = lean_ctor_get(v_a_2851_, 9);
lean_inc(v_maxHeartbeats_2864_);
v_quotContext_2865_ = lean_ctor_get(v_a_2851_, 10);
lean_inc(v_quotContext_2865_);
v_currMacroScope_2866_ = lean_ctor_get(v_a_2851_, 11);
lean_inc(v_currMacroScope_2866_);
v_diag_2867_ = lean_ctor_get_uint8(v_a_2851_, sizeof(void*)*14);
v_cancelTk_x3f_2868_ = lean_ctor_get(v_a_2851_, 12);
lean_inc(v_cancelTk_x3f_2868_);
v_suppressElabErrors_2869_ = lean_ctor_get_uint8(v_a_2851_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2870_ = lean_ctor_get(v_a_2851_, 13);
lean_inc_ref(v_inheritedTraceOptions_2870_);
lean_dec_ref(v_a_2851_);
v___x_2924_ = lean_unsigned_to_nat(0u);
v___x_2925_ = lean_nat_dec_eq(v_maxRecDepth_2859_, v___x_2924_);
v___x_2926_ = lean_bool_not(v___x_2925_);
if (v___x_2926_ == 0)
{
v___y_2872_ = v___x_2926_;
goto v___jp_2871_;
}
else
{
uint8_t v___x_2927_; 
v___x_2927_ = lean_nat_dec_eq(v_currRecDepth_2858_, v_maxRecDepth_2859_);
v___y_2872_ = v___x_2927_;
goto v___jp_2871_;
}
v___jp_2871_:
{
if (v___y_2872_ == 0)
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2873_ = lean_unsigned_to_nat(1u);
v___x_2874_ = lean_nat_add(v_currRecDepth_2858_, v___x_2873_);
lean_dec(v_currRecDepth_2858_);
v___x_2875_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2875_, 0, v_fileName_2855_);
lean_ctor_set(v___x_2875_, 1, v_fileMap_2856_);
lean_ctor_set(v___x_2875_, 2, v_options_2857_);
lean_ctor_set(v___x_2875_, 3, v___x_2874_);
lean_ctor_set(v___x_2875_, 4, v_maxRecDepth_2859_);
lean_ctor_set(v___x_2875_, 5, v_ref_2860_);
lean_ctor_set(v___x_2875_, 6, v_currNamespace_2861_);
lean_ctor_set(v___x_2875_, 7, v_openDecls_2862_);
lean_ctor_set(v___x_2875_, 8, v_initHeartbeats_2863_);
lean_ctor_set(v___x_2875_, 9, v_maxHeartbeats_2864_);
lean_ctor_set(v___x_2875_, 10, v_quotContext_2865_);
lean_ctor_set(v___x_2875_, 11, v_currMacroScope_2866_);
lean_ctor_set(v___x_2875_, 12, v_cancelTk_x3f_2868_);
lean_ctor_set(v___x_2875_, 13, v_inheritedTraceOptions_2870_);
lean_ctor_set_uint8(v___x_2875_, sizeof(void*)*14, v_diag_2867_);
lean_ctor_set_uint8(v___x_2875_, sizeof(void*)*14 + 1, v_suppressElabErrors_2869_);
v___x_2876_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2854_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v___x_2875_, v_a_2852_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2914_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2879_ = v___x_2876_;
v_isShared_2880_ = v_isSharedCheck_2914_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2876_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2914_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
if (lean_obj_tag(v_a_2877_) == 1)
{
lean_object* v_val_2881_; lean_object* v_snd_2882_; lean_object* v_snd_2883_; lean_object* v_fst_2884_; lean_object* v_fst_2885_; lean_object* v_p_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
lean_del_object(v___x_2879_);
v_val_2881_ = lean_ctor_get(v_a_2877_, 0);
lean_inc(v_val_2881_);
lean_dec_ref_known(v_a_2877_, 1);
v_snd_2882_ = lean_ctor_get(v_val_2881_, 1);
lean_inc(v_snd_2882_);
v_snd_2883_ = lean_ctor_get(v_snd_2882_, 1);
lean_inc(v_snd_2883_);
v_fst_2884_ = lean_ctor_get(v_val_2881_, 0);
lean_inc(v_fst_2884_);
lean_dec(v_val_2881_);
v_fst_2885_ = lean_ctor_get(v_snd_2882_, 0);
lean_inc(v_fst_2885_);
lean_dec(v_snd_2882_);
v_p_2886_ = lean_ctor_get(v_snd_2883_, 0);
v___x_2887_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2886_, v_fst_2885_);
lean_inc_ref(v_c_u2082_2841_);
v___x_2888_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v___x_2887_, v_fst_2885_, v_snd_2883_, v_fst_2884_, v_c_u2082_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v___x_2875_, v_a_2852_);
lean_dec(v_fst_2885_);
lean_dec(v___x_2887_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_a_2889_);
lean_dec_ref_known(v___x_2888_, 1);
if (lean_obj_tag(v_a_2889_) == 1)
{
lean_object* v_val_2890_; 
lean_dec_ref(v_c_u2082_2841_);
v_val_2890_ = lean_ctor_get(v_a_2889_, 0);
lean_inc(v_val_2890_);
lean_dec_ref_known(v_a_2889_, 1);
v_c_u2082_2841_ = v_val_2890_;
v_a_2851_ = v___x_2875_;
goto _start;
}
else
{
lean_object* v___x_2892_; 
lean_dec(v_a_2889_);
v___x_2892_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_u2082_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v___x_2875_, v_a_2852_);
lean_dec_ref_known(v___x_2875_, 14);
lean_dec_ref(v_c_u2082_2841_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2900_; 
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2900_ == 0)
{
lean_object* v_unused_2901_; 
v_unused_2901_ = lean_ctor_get(v___x_2892_, 0);
lean_dec(v_unused_2901_);
v___x_2894_ = v___x_2892_;
v_isShared_2895_ = v_isSharedCheck_2900_;
goto v_resetjp_2893_;
}
else
{
lean_dec(v___x_2892_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2900_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; lean_object* v___x_2898_; 
v___x_2896_ = lean_box(0);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 0, v___x_2896_);
v___x_2898_ = v___x_2894_;
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
else
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
v_a_2902_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2892_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2892_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2875_, 14);
lean_dec_ref(v_c_u2082_2841_);
return v___x_2888_;
}
}
else
{
lean_object* v___x_2910_; lean_object* v___x_2912_; 
lean_dec(v_a_2877_);
lean_dec_ref_known(v___x_2875_, 14);
v___x_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2910_, 0, v_c_u2082_2841_);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 0, v___x_2910_);
v___x_2912_ = v___x_2879_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2910_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec_ref_known(v___x_2875_, 14);
lean_dec_ref(v_c_u2082_2841_);
v_a_2915_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2876_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2876_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
else
{
lean_object* v___x_2923_; 
lean_dec_ref(v_inheritedTraceOptions_2870_);
lean_dec(v_cancelTk_x3f_2868_);
lean_dec(v_currMacroScope_2866_);
lean_dec(v_quotContext_2865_);
lean_dec(v_maxHeartbeats_2864_);
lean_dec(v_initHeartbeats_2863_);
lean_dec(v_openDecls_2862_);
lean_dec(v_currNamespace_2861_);
lean_dec(v_maxRecDepth_2859_);
lean_dec(v_currRecDepth_2858_);
lean_dec_ref(v_options_2857_);
lean_dec_ref(v_fileMap_2856_);
lean_dec_ref(v_fileName_2855_);
lean_dec_ref(v_c_u2082_2841_);
v___x_2923_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_2860_);
return v___x_2923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object* v_c_u2082_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_u2082_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_);
lean_dec(v_a_2939_);
lean_dec(v_a_2937_);
lean_dec_ref(v_a_2936_);
lean_dec(v_a_2935_);
lean_dec_ref(v_a_2934_);
lean_dec(v_a_2933_);
lean_dec_ref(v_a_2932_);
lean_dec(v_a_2931_);
lean_dec(v_a_2930_);
lean_dec(v_a_2929_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object* v_val_2942_, lean_object* v_x_2943_, size_t v_x_2944_, size_t v_x_2945_){
_start:
{
if (lean_obj_tag(v_x_2943_) == 0)
{
lean_object* v_cs_2946_; size_t v_j_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; uint8_t v___x_2950_; 
v_cs_2946_ = lean_ctor_get(v_x_2943_, 0);
v_j_2947_ = lean_usize_shift_right(v_x_2944_, v_x_2945_);
v___x_2948_ = lean_usize_to_nat(v_j_2947_);
v___x_2949_ = lean_array_get_size(v_cs_2946_);
v___x_2950_ = lean_nat_dec_lt(v___x_2948_, v___x_2949_);
if (v___x_2950_ == 0)
{
lean_dec(v___x_2948_);
lean_dec_ref(v_val_2942_);
return v_x_2943_;
}
else
{
lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2968_; 
lean_inc_ref(v_cs_2946_);
v_isSharedCheck_2968_ = !lean_is_exclusive(v_x_2943_);
if (v_isSharedCheck_2968_ == 0)
{
lean_object* v_unused_2969_; 
v_unused_2969_ = lean_ctor_get(v_x_2943_, 0);
lean_dec(v_unused_2969_);
v___x_2952_ = v_x_2943_;
v_isShared_2953_ = v_isSharedCheck_2968_;
goto v_resetjp_2951_;
}
else
{
lean_dec(v_x_2943_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2968_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
size_t v___x_2954_; size_t v___x_2955_; size_t v___x_2956_; size_t v_i_2957_; size_t v___x_2958_; size_t v_shift_2959_; lean_object* v_v_2960_; lean_object* v___x_2961_; lean_object* v_xs_x27_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2966_; 
v___x_2954_ = ((size_t)1ULL);
v___x_2955_ = lean_usize_shift_left(v___x_2954_, v_x_2945_);
v___x_2956_ = lean_usize_sub(v___x_2955_, v___x_2954_);
v_i_2957_ = lean_usize_land(v_x_2944_, v___x_2956_);
v___x_2958_ = ((size_t)5ULL);
v_shift_2959_ = lean_usize_sub(v_x_2945_, v___x_2958_);
v_v_2960_ = lean_array_fget(v_cs_2946_, v___x_2948_);
v___x_2961_ = lean_box(0);
v_xs_x27_2962_ = lean_array_fset(v_cs_2946_, v___x_2948_, v___x_2961_);
v___x_2963_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2942_, v_v_2960_, v_i_2957_, v_shift_2959_);
v___x_2964_ = lean_array_fset(v_xs_x27_2962_, v___x_2948_, v___x_2963_);
lean_dec(v___x_2948_);
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 0, v___x_2964_);
v___x_2966_ = v___x_2952_;
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
lean_object* v_vs_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; uint8_t v___x_2973_; 
v_vs_2970_ = lean_ctor_get(v_x_2943_, 0);
v___x_2971_ = lean_usize_to_nat(v_x_2944_);
v___x_2972_ = lean_array_get_size(v_vs_2970_);
v___x_2973_ = lean_nat_dec_lt(v___x_2971_, v___x_2972_);
if (v___x_2973_ == 0)
{
lean_dec(v___x_2971_);
lean_dec_ref(v_val_2942_);
return v_x_2943_;
}
else
{
lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2985_; 
lean_inc_ref(v_vs_2970_);
v_isSharedCheck_2985_ = !lean_is_exclusive(v_x_2943_);
if (v_isSharedCheck_2985_ == 0)
{
lean_object* v_unused_2986_; 
v_unused_2986_ = lean_ctor_get(v_x_2943_, 0);
lean_dec(v_unused_2986_);
v___x_2975_ = v_x_2943_;
v_isShared_2976_ = v_isSharedCheck_2985_;
goto v_resetjp_2974_;
}
else
{
lean_dec(v_x_2943_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2985_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v_v_2977_; lean_object* v___x_2978_; lean_object* v_xs_x27_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2983_; 
v_v_2977_ = lean_array_fget(v_vs_2970_, v___x_2971_);
v___x_2978_ = lean_box(0);
v_xs_x27_2979_ = lean_array_fset(v_vs_2970_, v___x_2971_, v___x_2978_);
v___x_2980_ = l_Lean_PersistentArray_push___redArg(v_v_2977_, v_val_2942_);
v___x_2981_ = lean_array_fset(v_xs_x27_2979_, v___x_2971_, v___x_2980_);
lean_dec(v___x_2971_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 0, v___x_2981_);
v___x_2983_ = v___x_2975_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2981_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_val_2987_, lean_object* v_x_2988_, lean_object* v_x_2989_, lean_object* v_x_2990_){
_start:
{
size_t v_x_53647__boxed_2991_; size_t v_x_53648__boxed_2992_; lean_object* v_res_2993_; 
v_x_53647__boxed_2991_ = lean_unbox_usize(v_x_2989_);
lean_dec(v_x_2989_);
v_x_53648__boxed_2992_ = lean_unbox_usize(v_x_2990_);
lean_dec(v_x_2990_);
v_res_2993_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2987_, v_x_2988_, v_x_53647__boxed_2991_, v_x_53648__boxed_2992_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object* v_val_2994_, lean_object* v_t_2995_, lean_object* v_i_2996_){
_start:
{
lean_object* v_root_2997_; lean_object* v_tail_2998_; lean_object* v_size_2999_; size_t v_shift_3000_; lean_object* v_tailOff_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3025_; 
v_root_2997_ = lean_ctor_get(v_t_2995_, 0);
v_tail_2998_ = lean_ctor_get(v_t_2995_, 1);
v_size_2999_ = lean_ctor_get(v_t_2995_, 2);
v_shift_3000_ = lean_ctor_get_usize(v_t_2995_, 4);
v_tailOff_3001_ = lean_ctor_get(v_t_2995_, 3);
v_isSharedCheck_3025_ = !lean_is_exclusive(v_t_2995_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3003_ = v_t_2995_;
v_isShared_3004_ = v_isSharedCheck_3025_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_tailOff_3001_);
lean_inc(v_size_2999_);
lean_inc(v_tail_2998_);
lean_inc(v_root_2997_);
lean_dec(v_t_2995_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3025_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
uint8_t v___x_3005_; 
v___x_3005_ = lean_nat_dec_le(v_tailOff_3001_, v_i_2996_);
if (v___x_3005_ == 0)
{
size_t v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3009_; 
v___x_3006_ = lean_usize_of_nat(v_i_2996_);
v___x_3007_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2994_, v_root_2997_, v___x_3006_, v_shift_3000_);
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 0, v___x_3007_);
v___x_3009_ = v___x_3003_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3007_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v_tail_2998_);
lean_ctor_set(v_reuseFailAlloc_3010_, 2, v_size_2999_);
lean_ctor_set(v_reuseFailAlloc_3010_, 3, v_tailOff_3001_);
lean_ctor_set_usize(v_reuseFailAlloc_3010_, 4, v_shift_3000_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
else
{
lean_object* v___x_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; 
v___x_3011_ = lean_nat_sub(v_i_2996_, v_tailOff_3001_);
v___x_3012_ = lean_array_get_size(v_tail_2998_);
v___x_3013_ = lean_nat_dec_lt(v___x_3011_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3015_; 
lean_dec(v___x_3011_);
lean_dec_ref(v_val_2994_);
if (v_isShared_3004_ == 0)
{
v___x_3015_ = v___x_3003_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_root_2997_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v_tail_2998_);
lean_ctor_set(v_reuseFailAlloc_3016_, 2, v_size_2999_);
lean_ctor_set(v_reuseFailAlloc_3016_, 3, v_tailOff_3001_);
lean_ctor_set_usize(v_reuseFailAlloc_3016_, 4, v_shift_3000_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
else
{
lean_object* v_v_3017_; lean_object* v___x_3018_; lean_object* v_xs_x27_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3023_; 
v_v_3017_ = lean_array_fget(v_tail_2998_, v___x_3011_);
v___x_3018_ = lean_box(0);
v_xs_x27_3019_ = lean_array_fset(v_tail_2998_, v___x_3011_, v___x_3018_);
v___x_3020_ = l_Lean_PersistentArray_push___redArg(v_v_3017_, v_val_2994_);
v___x_3021_ = lean_array_fset(v_xs_x27_3019_, v___x_3011_, v___x_3020_);
lean_dec(v___x_3011_);
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 1, v___x_3021_);
v___x_3023_ = v___x_3003_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_root_2997_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v___x_3021_);
lean_ctor_set(v_reuseFailAlloc_3024_, 2, v_size_2999_);
lean_ctor_set(v_reuseFailAlloc_3024_, 3, v_tailOff_3001_);
lean_ctor_set_usize(v_reuseFailAlloc_3024_, 4, v_shift_3000_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object* v_val_3026_, lean_object* v_t_3027_, lean_object* v_i_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3026_, v_t_3027_, v_i_3028_);
lean_dec(v_i_3028_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(lean_object* v___y_3030_, lean_object* v_val_3031_, lean_object* v_v_3032_, lean_object* v_s_3033_){
_start:
{
lean_object* v_structs_3034_; lean_object* v_typeIdOf_3035_; lean_object* v_exprToStructId_3036_; lean_object* v_exprToStructIdEntries_3037_; lean_object* v_forbiddenNatModules_3038_; lean_object* v_natStructs_3039_; lean_object* v_natTypeIdOf_3040_; lean_object* v_exprToNatStructId_3041_; lean_object* v___x_3042_; uint8_t v___x_3043_; 
v_structs_3034_ = lean_ctor_get(v_s_3033_, 0);
v_typeIdOf_3035_ = lean_ctor_get(v_s_3033_, 1);
v_exprToStructId_3036_ = lean_ctor_get(v_s_3033_, 2);
v_exprToStructIdEntries_3037_ = lean_ctor_get(v_s_3033_, 3);
v_forbiddenNatModules_3038_ = lean_ctor_get(v_s_3033_, 4);
v_natStructs_3039_ = lean_ctor_get(v_s_3033_, 5);
v_natTypeIdOf_3040_ = lean_ctor_get(v_s_3033_, 6);
v_exprToNatStructId_3041_ = lean_ctor_get(v_s_3033_, 7);
v___x_3042_ = lean_array_get_size(v_structs_3034_);
v___x_3043_ = lean_nat_dec_lt(v___y_3030_, v___x_3042_);
if (v___x_3043_ == 0)
{
lean_dec_ref(v_val_3031_);
return v_s_3033_;
}
else
{
lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3105_; 
lean_inc_ref(v_exprToNatStructId_3041_);
lean_inc_ref(v_natTypeIdOf_3040_);
lean_inc_ref(v_natStructs_3039_);
lean_inc_ref(v_forbiddenNatModules_3038_);
lean_inc_ref(v_exprToStructIdEntries_3037_);
lean_inc_ref(v_exprToStructId_3036_);
lean_inc_ref(v_typeIdOf_3035_);
lean_inc_ref(v_structs_3034_);
v_isSharedCheck_3105_ = !lean_is_exclusive(v_s_3033_);
if (v_isSharedCheck_3105_ == 0)
{
lean_object* v_unused_3106_; lean_object* v_unused_3107_; lean_object* v_unused_3108_; lean_object* v_unused_3109_; lean_object* v_unused_3110_; lean_object* v_unused_3111_; lean_object* v_unused_3112_; lean_object* v_unused_3113_; 
v_unused_3106_ = lean_ctor_get(v_s_3033_, 7);
lean_dec(v_unused_3106_);
v_unused_3107_ = lean_ctor_get(v_s_3033_, 6);
lean_dec(v_unused_3107_);
v_unused_3108_ = lean_ctor_get(v_s_3033_, 5);
lean_dec(v_unused_3108_);
v_unused_3109_ = lean_ctor_get(v_s_3033_, 4);
lean_dec(v_unused_3109_);
v_unused_3110_ = lean_ctor_get(v_s_3033_, 3);
lean_dec(v_unused_3110_);
v_unused_3111_ = lean_ctor_get(v_s_3033_, 2);
lean_dec(v_unused_3111_);
v_unused_3112_ = lean_ctor_get(v_s_3033_, 1);
lean_dec(v_unused_3112_);
v_unused_3113_ = lean_ctor_get(v_s_3033_, 0);
lean_dec(v_unused_3113_);
v___x_3045_ = v_s_3033_;
v_isShared_3046_ = v_isSharedCheck_3105_;
goto v_resetjp_3044_;
}
else
{
lean_dec(v_s_3033_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3105_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v_v_3047_; lean_object* v_id_3048_; lean_object* v_ringId_x3f_3049_; lean_object* v_type_3050_; lean_object* v_u_3051_; lean_object* v_intModuleInst_3052_; lean_object* v_leInst_x3f_3053_; lean_object* v_ltInst_x3f_3054_; lean_object* v_lawfulOrderLTInst_x3f_3055_; lean_object* v_isPreorderInst_x3f_3056_; lean_object* v_orderedAddInst_x3f_3057_; lean_object* v_isLinearInst_x3f_3058_; lean_object* v_noNatDivInst_x3f_3059_; lean_object* v_ringInst_x3f_3060_; lean_object* v_commRingInst_x3f_3061_; lean_object* v_orderedRingInst_x3f_3062_; lean_object* v_fieldInst_x3f_3063_; lean_object* v_charInst_x3f_3064_; lean_object* v_zero_3065_; lean_object* v_ofNatZero_3066_; lean_object* v_one_x3f_3067_; lean_object* v_leFn_x3f_3068_; lean_object* v_ltFn_x3f_3069_; lean_object* v_addFn_3070_; lean_object* v_zsmulFn_3071_; lean_object* v_nsmulFn_3072_; lean_object* v_zsmulFn_x3f_3073_; lean_object* v_nsmulFn_x3f_3074_; lean_object* v_homomulFn_x3f_3075_; lean_object* v_subFn_3076_; lean_object* v_negFn_3077_; lean_object* v_vars_3078_; lean_object* v_varMap_3079_; lean_object* v_lowers_3080_; lean_object* v_uppers_3081_; lean_object* v_diseqs_3082_; lean_object* v_assignment_3083_; uint8_t v_caseSplits_3084_; lean_object* v_conflict_x3f_3085_; lean_object* v_diseqSplits_3086_; lean_object* v_elimEqs_3087_; lean_object* v_elimStack_3088_; lean_object* v_occurs_3089_; lean_object* v_ignored_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3104_; 
v_v_3047_ = lean_array_fget(v_structs_3034_, v___y_3030_);
v_id_3048_ = lean_ctor_get(v_v_3047_, 0);
v_ringId_x3f_3049_ = lean_ctor_get(v_v_3047_, 1);
v_type_3050_ = lean_ctor_get(v_v_3047_, 2);
v_u_3051_ = lean_ctor_get(v_v_3047_, 3);
v_intModuleInst_3052_ = lean_ctor_get(v_v_3047_, 4);
v_leInst_x3f_3053_ = lean_ctor_get(v_v_3047_, 5);
v_ltInst_x3f_3054_ = lean_ctor_get(v_v_3047_, 6);
v_lawfulOrderLTInst_x3f_3055_ = lean_ctor_get(v_v_3047_, 7);
v_isPreorderInst_x3f_3056_ = lean_ctor_get(v_v_3047_, 8);
v_orderedAddInst_x3f_3057_ = lean_ctor_get(v_v_3047_, 9);
v_isLinearInst_x3f_3058_ = lean_ctor_get(v_v_3047_, 10);
v_noNatDivInst_x3f_3059_ = lean_ctor_get(v_v_3047_, 11);
v_ringInst_x3f_3060_ = lean_ctor_get(v_v_3047_, 12);
v_commRingInst_x3f_3061_ = lean_ctor_get(v_v_3047_, 13);
v_orderedRingInst_x3f_3062_ = lean_ctor_get(v_v_3047_, 14);
v_fieldInst_x3f_3063_ = lean_ctor_get(v_v_3047_, 15);
v_charInst_x3f_3064_ = lean_ctor_get(v_v_3047_, 16);
v_zero_3065_ = lean_ctor_get(v_v_3047_, 17);
v_ofNatZero_3066_ = lean_ctor_get(v_v_3047_, 18);
v_one_x3f_3067_ = lean_ctor_get(v_v_3047_, 19);
v_leFn_x3f_3068_ = lean_ctor_get(v_v_3047_, 20);
v_ltFn_x3f_3069_ = lean_ctor_get(v_v_3047_, 21);
v_addFn_3070_ = lean_ctor_get(v_v_3047_, 22);
v_zsmulFn_3071_ = lean_ctor_get(v_v_3047_, 23);
v_nsmulFn_3072_ = lean_ctor_get(v_v_3047_, 24);
v_zsmulFn_x3f_3073_ = lean_ctor_get(v_v_3047_, 25);
v_nsmulFn_x3f_3074_ = lean_ctor_get(v_v_3047_, 26);
v_homomulFn_x3f_3075_ = lean_ctor_get(v_v_3047_, 27);
v_subFn_3076_ = lean_ctor_get(v_v_3047_, 28);
v_negFn_3077_ = lean_ctor_get(v_v_3047_, 29);
v_vars_3078_ = lean_ctor_get(v_v_3047_, 30);
v_varMap_3079_ = lean_ctor_get(v_v_3047_, 31);
v_lowers_3080_ = lean_ctor_get(v_v_3047_, 32);
v_uppers_3081_ = lean_ctor_get(v_v_3047_, 33);
v_diseqs_3082_ = lean_ctor_get(v_v_3047_, 34);
v_assignment_3083_ = lean_ctor_get(v_v_3047_, 35);
v_caseSplits_3084_ = lean_ctor_get_uint8(v_v_3047_, sizeof(void*)*42);
v_conflict_x3f_3085_ = lean_ctor_get(v_v_3047_, 36);
v_diseqSplits_3086_ = lean_ctor_get(v_v_3047_, 37);
v_elimEqs_3087_ = lean_ctor_get(v_v_3047_, 38);
v_elimStack_3088_ = lean_ctor_get(v_v_3047_, 39);
v_occurs_3089_ = lean_ctor_get(v_v_3047_, 40);
v_ignored_3090_ = lean_ctor_get(v_v_3047_, 41);
v_isSharedCheck_3104_ = !lean_is_exclusive(v_v_3047_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3092_ = v_v_3047_;
v_isShared_3093_ = v_isSharedCheck_3104_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_ignored_3090_);
lean_inc(v_occurs_3089_);
lean_inc(v_elimStack_3088_);
lean_inc(v_elimEqs_3087_);
lean_inc(v_diseqSplits_3086_);
lean_inc(v_conflict_x3f_3085_);
lean_inc(v_assignment_3083_);
lean_inc(v_diseqs_3082_);
lean_inc(v_uppers_3081_);
lean_inc(v_lowers_3080_);
lean_inc(v_varMap_3079_);
lean_inc(v_vars_3078_);
lean_inc(v_negFn_3077_);
lean_inc(v_subFn_3076_);
lean_inc(v_homomulFn_x3f_3075_);
lean_inc(v_nsmulFn_x3f_3074_);
lean_inc(v_zsmulFn_x3f_3073_);
lean_inc(v_nsmulFn_3072_);
lean_inc(v_zsmulFn_3071_);
lean_inc(v_addFn_3070_);
lean_inc(v_ltFn_x3f_3069_);
lean_inc(v_leFn_x3f_3068_);
lean_inc(v_one_x3f_3067_);
lean_inc(v_ofNatZero_3066_);
lean_inc(v_zero_3065_);
lean_inc(v_charInst_x3f_3064_);
lean_inc(v_fieldInst_x3f_3063_);
lean_inc(v_orderedRingInst_x3f_3062_);
lean_inc(v_commRingInst_x3f_3061_);
lean_inc(v_ringInst_x3f_3060_);
lean_inc(v_noNatDivInst_x3f_3059_);
lean_inc(v_isLinearInst_x3f_3058_);
lean_inc(v_orderedAddInst_x3f_3057_);
lean_inc(v_isPreorderInst_x3f_3056_);
lean_inc(v_lawfulOrderLTInst_x3f_3055_);
lean_inc(v_ltInst_x3f_3054_);
lean_inc(v_leInst_x3f_3053_);
lean_inc(v_intModuleInst_3052_);
lean_inc(v_u_3051_);
lean_inc(v_type_3050_);
lean_inc(v_ringId_x3f_3049_);
lean_inc(v_id_3048_);
lean_dec(v_v_3047_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3104_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; lean_object* v_xs_x27_3095_; lean_object* v___x_3096_; lean_object* v___x_3098_; 
v___x_3094_ = lean_box(0);
v_xs_x27_3095_ = lean_array_fset(v_structs_3034_, v___y_3030_, v___x_3094_);
v___x_3096_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3031_, v_diseqs_3082_, v_v_3032_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 34, v___x_3096_);
v___x_3098_ = v___x_3092_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_id_3048_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v_ringId_x3f_3049_);
lean_ctor_set(v_reuseFailAlloc_3103_, 2, v_type_3050_);
lean_ctor_set(v_reuseFailAlloc_3103_, 3, v_u_3051_);
lean_ctor_set(v_reuseFailAlloc_3103_, 4, v_intModuleInst_3052_);
lean_ctor_set(v_reuseFailAlloc_3103_, 5, v_leInst_x3f_3053_);
lean_ctor_set(v_reuseFailAlloc_3103_, 6, v_ltInst_x3f_3054_);
lean_ctor_set(v_reuseFailAlloc_3103_, 7, v_lawfulOrderLTInst_x3f_3055_);
lean_ctor_set(v_reuseFailAlloc_3103_, 8, v_isPreorderInst_x3f_3056_);
lean_ctor_set(v_reuseFailAlloc_3103_, 9, v_orderedAddInst_x3f_3057_);
lean_ctor_set(v_reuseFailAlloc_3103_, 10, v_isLinearInst_x3f_3058_);
lean_ctor_set(v_reuseFailAlloc_3103_, 11, v_noNatDivInst_x3f_3059_);
lean_ctor_set(v_reuseFailAlloc_3103_, 12, v_ringInst_x3f_3060_);
lean_ctor_set(v_reuseFailAlloc_3103_, 13, v_commRingInst_x3f_3061_);
lean_ctor_set(v_reuseFailAlloc_3103_, 14, v_orderedRingInst_x3f_3062_);
lean_ctor_set(v_reuseFailAlloc_3103_, 15, v_fieldInst_x3f_3063_);
lean_ctor_set(v_reuseFailAlloc_3103_, 16, v_charInst_x3f_3064_);
lean_ctor_set(v_reuseFailAlloc_3103_, 17, v_zero_3065_);
lean_ctor_set(v_reuseFailAlloc_3103_, 18, v_ofNatZero_3066_);
lean_ctor_set(v_reuseFailAlloc_3103_, 19, v_one_x3f_3067_);
lean_ctor_set(v_reuseFailAlloc_3103_, 20, v_leFn_x3f_3068_);
lean_ctor_set(v_reuseFailAlloc_3103_, 21, v_ltFn_x3f_3069_);
lean_ctor_set(v_reuseFailAlloc_3103_, 22, v_addFn_3070_);
lean_ctor_set(v_reuseFailAlloc_3103_, 23, v_zsmulFn_3071_);
lean_ctor_set(v_reuseFailAlloc_3103_, 24, v_nsmulFn_3072_);
lean_ctor_set(v_reuseFailAlloc_3103_, 25, v_zsmulFn_x3f_3073_);
lean_ctor_set(v_reuseFailAlloc_3103_, 26, v_nsmulFn_x3f_3074_);
lean_ctor_set(v_reuseFailAlloc_3103_, 27, v_homomulFn_x3f_3075_);
lean_ctor_set(v_reuseFailAlloc_3103_, 28, v_subFn_3076_);
lean_ctor_set(v_reuseFailAlloc_3103_, 29, v_negFn_3077_);
lean_ctor_set(v_reuseFailAlloc_3103_, 30, v_vars_3078_);
lean_ctor_set(v_reuseFailAlloc_3103_, 31, v_varMap_3079_);
lean_ctor_set(v_reuseFailAlloc_3103_, 32, v_lowers_3080_);
lean_ctor_set(v_reuseFailAlloc_3103_, 33, v_uppers_3081_);
lean_ctor_set(v_reuseFailAlloc_3103_, 34, v___x_3096_);
lean_ctor_set(v_reuseFailAlloc_3103_, 35, v_assignment_3083_);
lean_ctor_set(v_reuseFailAlloc_3103_, 36, v_conflict_x3f_3085_);
lean_ctor_set(v_reuseFailAlloc_3103_, 37, v_diseqSplits_3086_);
lean_ctor_set(v_reuseFailAlloc_3103_, 38, v_elimEqs_3087_);
lean_ctor_set(v_reuseFailAlloc_3103_, 39, v_elimStack_3088_);
lean_ctor_set(v_reuseFailAlloc_3103_, 40, v_occurs_3089_);
lean_ctor_set(v_reuseFailAlloc_3103_, 41, v_ignored_3090_);
lean_ctor_set_uint8(v_reuseFailAlloc_3103_, sizeof(void*)*42, v_caseSplits_3084_);
v___x_3098_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
lean_object* v___x_3099_; lean_object* v___x_3101_; 
v___x_3099_ = lean_array_fset(v_xs_x27_3095_, v___y_3030_, v___x_3098_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3099_);
v___x_3101_ = v___x_3045_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3099_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v_typeIdOf_3035_);
lean_ctor_set(v_reuseFailAlloc_3102_, 2, v_exprToStructId_3036_);
lean_ctor_set(v_reuseFailAlloc_3102_, 3, v_exprToStructIdEntries_3037_);
lean_ctor_set(v_reuseFailAlloc_3102_, 4, v_forbiddenNatModules_3038_);
lean_ctor_set(v_reuseFailAlloc_3102_, 5, v_natStructs_3039_);
lean_ctor_set(v_reuseFailAlloc_3102_, 6, v_natTypeIdOf_3040_);
lean_ctor_set(v_reuseFailAlloc_3102_, 7, v_exprToNatStructId_3041_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed(lean_object* v___y_3114_, lean_object* v_val_3115_, lean_object* v_v_3116_, lean_object* v_s_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(v___y_3114_, v_val_3115_, v_v_3116_, v_s_3117_);
lean_dec(v_v_3116_);
lean_dec(v___y_3114_);
return v_res_3118_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2(void){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3126_ = l_Lean_Name_append(v___x_3125_, v___x_3124_);
return v___x_3126_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3133_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3135_ = l_Lean_Name_append(v___x_3134_, v___x_3133_);
return v___x_3135_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7(void){
_start:
{
lean_object* v_cls_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v_cls_3140_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3141_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3142_ = l_Lean_Name_append(v___x_3141_, v_cls_3140_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object* v_c_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_){
_start:
{
lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v_options_3214_; lean_object* v_inheritedTraceOptions_3215_; uint8_t v_hasTrace_3216_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; 
v_options_3214_ = lean_ctor_get(v_a_3153_, 2);
v_inheritedTraceOptions_3215_ = lean_ctor_get(v_a_3153_, 13);
v_hasTrace_3216_ = lean_ctor_get_uint8(v_options_3214_, sizeof(void*)*1);
if (v_hasTrace_3216_ == 0)
{
v___y_3218_ = v_a_3144_;
v___y_3219_ = v_a_3145_;
v___y_3220_ = v_a_3146_;
v___y_3221_ = v_a_3147_;
v___y_3222_ = v_a_3148_;
v___y_3223_ = v_a_3149_;
v___y_3224_ = v_a_3150_;
v___y_3225_ = v_a_3151_;
v___y_3226_ = v_a_3152_;
v___y_3227_ = v_a_3153_;
v___y_3228_ = v_a_3154_;
goto v___jp_3217_;
}
else
{
lean_object* v_cls_3287_; lean_object* v___x_3288_; uint8_t v___x_3289_; 
v_cls_3287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3288_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_3289_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3215_, v_options_3214_, v___x_3288_);
if (v___x_3289_ == 0)
{
v___y_3218_ = v_a_3144_;
v___y_3219_ = v_a_3145_;
v___y_3220_ = v_a_3146_;
v___y_3221_ = v_a_3147_;
v___y_3222_ = v_a_3148_;
v___y_3223_ = v_a_3149_;
v___y_3224_ = v_a_3150_;
v___y_3225_ = v_a_3151_;
v___y_3226_ = v_a_3152_;
v___y_3227_ = v_a_3153_;
v___y_3228_ = v_a_3154_;
goto v___jp_3217_;
}
else
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v_a_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
lean_inc(v_a_3291_);
lean_dec_ref_known(v___x_3290_, 1);
v___x_3292_ = l_Lean_MessageData_ofExpr(v_a_3291_);
v___x_3293_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_3287_, v___x_3292_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_dec_ref_known(v___x_3293_, 1);
v___y_3218_ = v_a_3144_;
v___y_3219_ = v_a_3145_;
v___y_3220_ = v_a_3146_;
v___y_3221_ = v_a_3147_;
v___y_3222_ = v_a_3148_;
v___y_3223_ = v_a_3149_;
v___y_3224_ = v_a_3150_;
v___y_3225_ = v_a_3151_;
v___y_3226_ = v_a_3152_;
v___y_3227_ = v_a_3153_;
v___y_3228_ = v_a_3154_;
goto v___jp_3217_;
}
else
{
lean_dec_ref(v_c_3143_);
return v___x_3293_;
}
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
lean_dec_ref(v_c_3143_);
v_a_3294_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3290_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3290_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
}
v___jp_3156_:
{
lean_object* v___x_3173_; 
v___x_3173_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_3160_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v___f_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
lean_dec_ref_known(v___x_3173_, 1);
lean_inc(v___y_3162_);
v___f_3174_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3174_, 0, v___y_3162_);
lean_closure_set(v___f_3174_, 1, v___y_3158_);
lean_closure_set(v___f_3174_, 2, v___y_3157_);
v___x_3175_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3176_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3175_, v___f_3174_, v___y_3163_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v___x_3177_; 
lean_dec_ref_known(v___x_3176_, 1);
v___x_3177_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3190_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3180_ = v___x_3177_;
v_isShared_3181_ = v_isSharedCheck_3190_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3190_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
uint8_t v___x_3182_; uint8_t v___x_3183_; uint8_t v___x_3184_; 
v___x_3182_ = 0;
v___x_3183_ = lean_unbox(v_a_3178_);
lean_dec(v_a_3178_);
v___x_3184_ = l_Lean_instBEqLBool_beq(v___x_3183_, v___x_3182_);
if (v___x_3184_ == 0)
{
lean_object* v___x_3185_; lean_object* v___x_3187_; 
lean_dec(v___y_3159_);
v___x_3185_ = lean_box(0);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v___x_3185_);
v___x_3187_ = v___x_3180_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
else
{
lean_object* v___x_3189_; 
lean_del_object(v___x_3180_);
v___x_3189_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_3159_, v___y_3162_, v___y_3163_);
return v___x_3189_;
}
}
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
lean_dec(v___y_3159_);
v_a_3191_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_3177_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3177_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
else
{
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3159_);
return v___x_3176_;
}
}
else
{
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
return v___x_3173_;
}
}
v___jp_3199_:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___y_3200_);
v___x_3213_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(v___x_3212_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3213_;
}
v___jp_3217_:
{
lean_object* v___x_3229_; 
lean_inc_ref(v___y_3227_);
v___x_3229_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_3143_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3278_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3232_ = v___x_3229_;
v_isShared_3233_ = v_isSharedCheck_3278_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3229_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3278_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
if (lean_obj_tag(v_a_3230_) == 1)
{
lean_object* v_val_3234_; lean_object* v_p_3235_; 
lean_del_object(v___x_3232_);
v_val_3234_ = lean_ctor_get(v_a_3230_, 0);
lean_inc(v_val_3234_);
lean_dec_ref_known(v_a_3230_, 1);
v_p_3235_ = lean_ctor_get(v_val_3234_, 0);
if (lean_obj_tag(v_p_3235_) == 0)
{
lean_object* v_options_3236_; uint8_t v_hasTrace_3237_; 
v_options_3236_ = lean_ctor_get(v___y_3227_, 2);
v_hasTrace_3237_ = lean_ctor_get_uint8(v_options_3236_, sizeof(void*)*1);
if (v_hasTrace_3237_ == 0)
{
v___y_3200_ = v_val_3234_;
v___y_3201_ = v___y_3218_;
v___y_3202_ = v___y_3219_;
v___y_3203_ = v___y_3220_;
v___y_3204_ = v___y_3221_;
v___y_3205_ = v___y_3222_;
v___y_3206_ = v___y_3223_;
v___y_3207_ = v___y_3224_;
v___y_3208_ = v___y_3225_;
v___y_3209_ = v___y_3226_;
v___y_3210_ = v___y_3227_;
v___y_3211_ = v___y_3228_;
goto v___jp_3199_;
}
else
{
lean_object* v_inheritedTraceOptions_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; uint8_t v___x_3241_; 
v_inheritedTraceOptions_3238_ = lean_ctor_get(v___y_3227_, 13);
v___x_3239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3240_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2);
v___x_3241_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3238_, v_options_3236_, v___x_3240_);
if (v___x_3241_ == 0)
{
v___y_3200_ = v_val_3234_;
v___y_3201_ = v___y_3218_;
v___y_3202_ = v___y_3219_;
v___y_3203_ = v___y_3220_;
v___y_3204_ = v___y_3221_;
v___y_3205_ = v___y_3222_;
v___y_3206_ = v___y_3223_;
v___y_3207_ = v___y_3224_;
v___y_3208_ = v___y_3225_;
v___y_3209_ = v___y_3226_;
v___y_3210_ = v___y_3227_;
v___y_3211_ = v___y_3228_;
goto v___jp_3199_;
}
else
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3234_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc(v_a_3243_);
lean_dec_ref_known(v___x_3242_, 1);
v___x_3244_ = l_Lean_MessageData_ofExpr(v_a_3243_);
v___x_3245_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3239_, v___x_3244_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_dec_ref_known(v___x_3245_, 1);
v___y_3200_ = v_val_3234_;
v___y_3201_ = v___y_3218_;
v___y_3202_ = v___y_3219_;
v___y_3203_ = v___y_3220_;
v___y_3204_ = v___y_3221_;
v___y_3205_ = v___y_3222_;
v___y_3206_ = v___y_3223_;
v___y_3207_ = v___y_3224_;
v___y_3208_ = v___y_3225_;
v___y_3209_ = v___y_3226_;
v___y_3210_ = v___y_3227_;
v___y_3211_ = v___y_3228_;
goto v___jp_3199_;
}
else
{
lean_dec(v_val_3234_);
return v___x_3245_;
}
}
else
{
lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
lean_dec(v_val_3234_);
v_a_3246_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3248_ = v___x_3242_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3242_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3246_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
}
}
else
{
lean_object* v_options_3254_; uint8_t v_hasTrace_3255_; 
lean_inc_ref(v_p_3235_);
v_options_3254_ = lean_ctor_get(v___y_3227_, 2);
v_hasTrace_3255_ = lean_ctor_get_uint8(v_options_3254_, sizeof(void*)*1);
if (v_hasTrace_3255_ == 0)
{
lean_object* v_v_3256_; 
v_v_3256_ = lean_ctor_get(v_p_3235_, 1);
lean_inc_n(v_v_3256_, 2);
lean_inc(v_val_3234_);
v___y_3157_ = v_v_3256_;
v___y_3158_ = v_val_3234_;
v___y_3159_ = v_v_3256_;
v___y_3160_ = v_p_3235_;
v___y_3161_ = v_val_3234_;
v___y_3162_ = v___y_3218_;
v___y_3163_ = v___y_3219_;
v___y_3164_ = v___y_3220_;
v___y_3165_ = v___y_3221_;
v___y_3166_ = v___y_3222_;
v___y_3167_ = v___y_3223_;
v___y_3168_ = v___y_3224_;
v___y_3169_ = v___y_3225_;
v___y_3170_ = v___y_3226_;
v___y_3171_ = v___y_3227_;
v___y_3172_ = v___y_3228_;
goto v___jp_3156_;
}
else
{
lean_object* v_v_3257_; lean_object* v_inheritedTraceOptions_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; uint8_t v___x_3261_; 
v_v_3257_ = lean_ctor_get(v_p_3235_, 1);
lean_inc(v_v_3257_);
v_inheritedTraceOptions_3258_ = lean_ctor_get(v___y_3227_, 13);
v___x_3259_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3260_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_3261_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3258_, v_options_3254_, v___x_3260_);
if (v___x_3261_ == 0)
{
lean_inc(v_val_3234_);
lean_inc(v_v_3257_);
v___y_3157_ = v_v_3257_;
v___y_3158_ = v_val_3234_;
v___y_3159_ = v_v_3257_;
v___y_3160_ = v_p_3235_;
v___y_3161_ = v_val_3234_;
v___y_3162_ = v___y_3218_;
v___y_3163_ = v___y_3219_;
v___y_3164_ = v___y_3220_;
v___y_3165_ = v___y_3221_;
v___y_3166_ = v___y_3222_;
v___y_3167_ = v___y_3223_;
v___y_3168_ = v___y_3224_;
v___y_3169_ = v___y_3225_;
v___y_3170_ = v___y_3226_;
v___y_3171_ = v___y_3227_;
v___y_3172_ = v___y_3228_;
goto v___jp_3156_;
}
else
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3234_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_a_3263_);
lean_dec_ref_known(v___x_3262_, 1);
v___x_3264_ = l_Lean_MessageData_ofExpr(v_a_3263_);
v___x_3265_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3259_, v___x_3264_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_dec_ref_known(v___x_3265_, 1);
lean_inc(v_val_3234_);
lean_inc(v_v_3257_);
v___y_3157_ = v_v_3257_;
v___y_3158_ = v_val_3234_;
v___y_3159_ = v_v_3257_;
v___y_3160_ = v_p_3235_;
v___y_3161_ = v_val_3234_;
v___y_3162_ = v___y_3218_;
v___y_3163_ = v___y_3219_;
v___y_3164_ = v___y_3220_;
v___y_3165_ = v___y_3221_;
v___y_3166_ = v___y_3222_;
v___y_3167_ = v___y_3223_;
v___y_3168_ = v___y_3224_;
v___y_3169_ = v___y_3225_;
v___y_3170_ = v___y_3226_;
v___y_3171_ = v___y_3227_;
v___y_3172_ = v___y_3228_;
goto v___jp_3156_;
}
else
{
lean_dec(v_v_3257_);
lean_dec_ref_known(v_p_3235_, 3);
lean_dec(v_val_3234_);
return v___x_3265_;
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_dec(v_v_3257_);
lean_dec_ref_known(v_p_3235_, 3);
lean_dec(v_val_3234_);
v_a_3266_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3262_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3262_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3276_; 
lean_dec(v_a_3230_);
v___x_3274_ = lean_box(0);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 0, v___x_3274_);
v___x_3276_ = v___x_3232_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
v_a_3279_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3229_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3229_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___boxed(lean_object* v_c_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_c_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
lean_dec(v_a_3313_);
lean_dec_ref(v_a_3312_);
lean_dec(v_a_3311_);
lean_dec_ref(v_a_3310_);
lean_dec(v_a_3309_);
lean_dec_ref(v_a_3308_);
lean_dec(v_a_3307_);
lean_dec_ref(v_a_3306_);
lean_dec(v_a_3305_);
lean_dec(v_a_3304_);
lean_dec(v_a_3303_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_3316_, lean_object* v_as_3317_, size_t v_sz_3318_, size_t v_i_3319_, lean_object* v_b_3320_){
_start:
{
uint8_t v___x_3321_; 
v___x_3321_ = lean_usize_dec_lt(v_i_3319_, v_sz_3318_);
if (v___x_3321_ == 0)
{
return v_b_3320_;
}
else
{
lean_object* v_snd_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3363_; 
v_snd_3322_ = lean_ctor_get(v_b_3320_, 1);
v_isSharedCheck_3363_ = !lean_is_exclusive(v_b_3320_);
if (v_isSharedCheck_3363_ == 0)
{
lean_object* v_unused_3364_; 
v_unused_3364_ = lean_ctor_get(v_b_3320_, 0);
lean_dec(v_unused_3364_);
v___x_3324_ = v_b_3320_;
v_isShared_3325_ = v_isSharedCheck_3363_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_snd_3322_);
lean_dec(v_b_3320_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3363_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v_fst_3326_; lean_object* v_snd_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3362_; 
v_fst_3326_ = lean_ctor_get(v_snd_3322_, 0);
v_snd_3327_ = lean_ctor_get(v_snd_3322_, 1);
v_isSharedCheck_3362_ = !lean_is_exclusive(v_snd_3322_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3329_ = v_snd_3322_;
v_isShared_3330_ = v_isSharedCheck_3362_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_snd_3327_);
lean_inc(v_fst_3326_);
lean_dec(v_snd_3322_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3362_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v_a_3331_; lean_object* v_p_3332_; lean_object* v___x_3333_; lean_object* v_a_3335_; lean_object* v_b_3342_; lean_object* v___x_3343_; uint8_t v___x_3344_; 
v_a_3331_ = lean_array_uget(v_as_3317_, v_i_3319_);
v_p_3332_ = lean_ctor_get(v_a_3331_, 0);
v___x_3333_ = lean_box(0);
v_b_3342_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3332_, v_x_3316_);
v___x_3343_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3344_ = lean_int_dec_eq(v_b_3342_, v___x_3343_);
if (v___x_3344_ == 0)
{
lean_object* v___x_3346_; 
lean_inc(v_a_3331_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 1, v_a_3331_);
lean_ctor_set(v___x_3324_, 0, v_b_3342_);
v___x_3346_ = v___x_3324_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_b_3342_);
lean_ctor_set(v_reuseFailAlloc_3357_, 1, v_a_3331_);
v___x_3346_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3354_; 
v_isSharedCheck_3354_ = !lean_is_exclusive(v_a_3331_);
if (v_isSharedCheck_3354_ == 0)
{
lean_object* v_unused_3355_; lean_object* v_unused_3356_; 
v_unused_3355_ = lean_ctor_get(v_a_3331_, 1);
lean_dec(v_unused_3355_);
v_unused_3356_ = lean_ctor_get(v_a_3331_, 0);
lean_dec(v_unused_3356_);
v___x_3348_ = v_a_3331_;
v_isShared_3349_ = v_isSharedCheck_3354_;
goto v_resetjp_3347_;
}
else
{
lean_dec(v_a_3331_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3354_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v_todo_3350_; lean_object* v___x_3352_; 
v_todo_3350_ = lean_array_push(v_snd_3327_, v___x_3346_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 1, v_todo_3350_);
lean_ctor_set(v___x_3348_, 0, v_fst_3326_);
v___x_3352_ = v___x_3348_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_fst_3326_);
lean_ctor_set(v_reuseFailAlloc_3353_, 1, v_todo_3350_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
v_a_3335_ = v___x_3352_;
goto v___jp_3334_;
}
}
}
}
else
{
lean_object* v_cs_x27_3358_; lean_object* v___x_3360_; 
lean_dec(v_b_3342_);
v_cs_x27_3358_ = l_Lean_PersistentArray_push___redArg(v_fst_3326_, v_a_3331_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 1, v_snd_3327_);
lean_ctor_set(v___x_3324_, 0, v_cs_x27_3358_);
v___x_3360_ = v___x_3324_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_cs_x27_3358_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_snd_3327_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
v_a_3335_ = v___x_3360_;
goto v___jp_3334_;
}
}
v___jp_3334_:
{
lean_object* v___x_3337_; 
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 1, v_a_3335_);
lean_ctor_set(v___x_3329_, 0, v___x_3333_);
v___x_3337_ = v___x_3329_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3333_);
lean_ctor_set(v_reuseFailAlloc_3341_, 1, v_a_3335_);
v___x_3337_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
size_t v___x_3338_; size_t v___x_3339_; 
v___x_3338_ = ((size_t)1ULL);
v___x_3339_ = lean_usize_add(v_i_3319_, v___x_3338_);
v_i_3319_ = v___x_3339_;
v_b_3320_ = v___x_3337_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_3365_, lean_object* v_as_3366_, lean_object* v_sz_3367_, lean_object* v_i_3368_, lean_object* v_b_3369_){
_start:
{
size_t v_sz_boxed_3370_; size_t v_i_boxed_3371_; lean_object* v_res_3372_; 
v_sz_boxed_3370_ = lean_unbox_usize(v_sz_3367_);
lean_dec(v_sz_3367_);
v_i_boxed_3371_ = lean_unbox_usize(v_i_3368_);
lean_dec(v_i_3368_);
v_res_3372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3365_, v_as_3366_, v_sz_boxed_3370_, v_i_boxed_3371_, v_b_3369_);
lean_dec_ref(v_as_3366_);
lean_dec(v_x_3365_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(lean_object* v_x_3373_, lean_object* v_as_3374_, size_t v_sz_3375_, size_t v_i_3376_, lean_object* v_b_3377_){
_start:
{
uint8_t v___x_3378_; 
v___x_3378_ = lean_usize_dec_lt(v_i_3376_, v_sz_3375_);
if (v___x_3378_ == 0)
{
return v_b_3377_;
}
else
{
lean_object* v_snd_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3420_; 
v_snd_3379_ = lean_ctor_get(v_b_3377_, 1);
v_isSharedCheck_3420_ = !lean_is_exclusive(v_b_3377_);
if (v_isSharedCheck_3420_ == 0)
{
lean_object* v_unused_3421_; 
v_unused_3421_ = lean_ctor_get(v_b_3377_, 0);
lean_dec(v_unused_3421_);
v___x_3381_ = v_b_3377_;
v_isShared_3382_ = v_isSharedCheck_3420_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_snd_3379_);
lean_dec(v_b_3377_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3420_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v_fst_3383_; lean_object* v_snd_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3419_; 
v_fst_3383_ = lean_ctor_get(v_snd_3379_, 0);
v_snd_3384_ = lean_ctor_get(v_snd_3379_, 1);
v_isSharedCheck_3419_ = !lean_is_exclusive(v_snd_3379_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3386_ = v_snd_3379_;
v_isShared_3387_ = v_isSharedCheck_3419_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_snd_3384_);
lean_inc(v_fst_3383_);
lean_dec(v_snd_3379_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3419_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v_a_3388_; lean_object* v_p_3389_; lean_object* v___x_3390_; lean_object* v_a_3392_; lean_object* v_b_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v_a_3388_ = lean_array_uget(v_as_3374_, v_i_3376_);
v_p_3389_ = lean_ctor_get(v_a_3388_, 0);
v___x_3390_ = lean_box(0);
v_b_3399_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3389_, v_x_3373_);
v___x_3400_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3401_ = lean_int_dec_eq(v_b_3399_, v___x_3400_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3403_; 
lean_inc(v_a_3388_);
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 1, v_a_3388_);
lean_ctor_set(v___x_3381_, 0, v_b_3399_);
v___x_3403_ = v___x_3381_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_b_3399_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_a_3388_);
v___x_3403_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3411_; 
v_isSharedCheck_3411_ = !lean_is_exclusive(v_a_3388_);
if (v_isSharedCheck_3411_ == 0)
{
lean_object* v_unused_3412_; lean_object* v_unused_3413_; 
v_unused_3412_ = lean_ctor_get(v_a_3388_, 1);
lean_dec(v_unused_3412_);
v_unused_3413_ = lean_ctor_get(v_a_3388_, 0);
lean_dec(v_unused_3413_);
v___x_3405_ = v_a_3388_;
v_isShared_3406_ = v_isSharedCheck_3411_;
goto v_resetjp_3404_;
}
else
{
lean_dec(v_a_3388_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3411_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v_todo_3407_; lean_object* v___x_3409_; 
v_todo_3407_ = lean_array_push(v_snd_3384_, v___x_3403_);
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 1, v_todo_3407_);
lean_ctor_set(v___x_3405_, 0, v_fst_3383_);
v___x_3409_ = v___x_3405_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_fst_3383_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v_todo_3407_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
v_a_3392_ = v___x_3409_;
goto v___jp_3391_;
}
}
}
}
else
{
lean_object* v_cs_x27_3415_; lean_object* v___x_3417_; 
lean_dec(v_b_3399_);
v_cs_x27_3415_ = l_Lean_PersistentArray_push___redArg(v_fst_3383_, v_a_3388_);
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 1, v_snd_3384_);
lean_ctor_set(v___x_3381_, 0, v_cs_x27_3415_);
v___x_3417_ = v___x_3381_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_cs_x27_3415_);
lean_ctor_set(v_reuseFailAlloc_3418_, 1, v_snd_3384_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
v_a_3392_ = v___x_3417_;
goto v___jp_3391_;
}
}
v___jp_3391_:
{
lean_object* v___x_3394_; 
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 1, v_a_3392_);
lean_ctor_set(v___x_3386_, 0, v___x_3390_);
v___x_3394_ = v___x_3386_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3390_);
lean_ctor_set(v_reuseFailAlloc_3398_, 1, v_a_3392_);
v___x_3394_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
size_t v___x_3395_; size_t v___x_3396_; lean_object* v___x_3397_; 
v___x_3395_ = ((size_t)1ULL);
v___x_3396_ = lean_usize_add(v_i_3376_, v___x_3395_);
v___x_3397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3373_, v_as_3374_, v_sz_3375_, v___x_3396_, v___x_3394_);
return v___x_3397_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_3422_, lean_object* v_as_3423_, lean_object* v_sz_3424_, lean_object* v_i_3425_, lean_object* v_b_3426_){
_start:
{
size_t v_sz_boxed_3427_; size_t v_i_boxed_3428_; lean_object* v_res_3429_; 
v_sz_boxed_3427_ = lean_unbox_usize(v_sz_3424_);
lean_dec(v_sz_3424_);
v_i_boxed_3428_ = lean_unbox_usize(v_i_3425_);
lean_dec(v_i_3425_);
v_res_3429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3422_, v_as_3423_, v_sz_boxed_3427_, v_i_boxed_3428_, v_b_3426_);
lean_dec_ref(v_as_3423_);
lean_dec(v_x_3422_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_3430_, lean_object* v_as_3431_, size_t v_sz_3432_, size_t v_i_3433_, lean_object* v_b_3434_){
_start:
{
uint8_t v___x_3435_; 
v___x_3435_ = lean_usize_dec_lt(v_i_3433_, v_sz_3432_);
if (v___x_3435_ == 0)
{
return v_b_3434_;
}
else
{
lean_object* v_snd_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3477_; 
v_snd_3436_ = lean_ctor_get(v_b_3434_, 1);
v_isSharedCheck_3477_ = !lean_is_exclusive(v_b_3434_);
if (v_isSharedCheck_3477_ == 0)
{
lean_object* v_unused_3478_; 
v_unused_3478_ = lean_ctor_get(v_b_3434_, 0);
lean_dec(v_unused_3478_);
v___x_3438_ = v_b_3434_;
v_isShared_3439_ = v_isSharedCheck_3477_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_snd_3436_);
lean_dec(v_b_3434_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3477_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v_fst_3440_; lean_object* v_snd_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3476_; 
v_fst_3440_ = lean_ctor_get(v_snd_3436_, 0);
v_snd_3441_ = lean_ctor_get(v_snd_3436_, 1);
v_isSharedCheck_3476_ = !lean_is_exclusive(v_snd_3436_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3443_ = v_snd_3436_;
v_isShared_3444_ = v_isSharedCheck_3476_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_snd_3441_);
lean_inc(v_fst_3440_);
lean_dec(v_snd_3436_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3476_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v_a_3445_; lean_object* v_p_3446_; lean_object* v___x_3447_; lean_object* v_a_3449_; lean_object* v_b_3456_; lean_object* v___x_3457_; uint8_t v___x_3458_; 
v_a_3445_ = lean_array_uget(v_as_3431_, v_i_3433_);
v_p_3446_ = lean_ctor_get(v_a_3445_, 0);
v___x_3447_ = lean_box(0);
v_b_3456_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3446_, v_x_3430_);
v___x_3457_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3458_ = lean_int_dec_eq(v_b_3456_, v___x_3457_);
if (v___x_3458_ == 0)
{
lean_object* v___x_3460_; 
lean_inc(v_a_3445_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v_a_3445_);
lean_ctor_set(v___x_3438_, 0, v_b_3456_);
v___x_3460_ = v___x_3438_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_b_3456_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_a_3445_);
v___x_3460_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3468_; 
v_isSharedCheck_3468_ = !lean_is_exclusive(v_a_3445_);
if (v_isSharedCheck_3468_ == 0)
{
lean_object* v_unused_3469_; lean_object* v_unused_3470_; 
v_unused_3469_ = lean_ctor_get(v_a_3445_, 1);
lean_dec(v_unused_3469_);
v_unused_3470_ = lean_ctor_get(v_a_3445_, 0);
lean_dec(v_unused_3470_);
v___x_3462_ = v_a_3445_;
v_isShared_3463_ = v_isSharedCheck_3468_;
goto v_resetjp_3461_;
}
else
{
lean_dec(v_a_3445_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3468_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v_todo_3464_; lean_object* v___x_3466_; 
v_todo_3464_ = lean_array_push(v_snd_3441_, v___x_3460_);
if (v_isShared_3463_ == 0)
{
lean_ctor_set(v___x_3462_, 1, v_todo_3464_);
lean_ctor_set(v___x_3462_, 0, v_fst_3440_);
v___x_3466_ = v___x_3462_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_fst_3440_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_todo_3464_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
v_a_3449_ = v___x_3466_;
goto v___jp_3448_;
}
}
}
}
else
{
lean_object* v_cs_x27_3472_; lean_object* v___x_3474_; 
lean_dec(v_b_3456_);
v_cs_x27_3472_ = l_Lean_PersistentArray_push___redArg(v_fst_3440_, v_a_3445_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v_snd_3441_);
lean_ctor_set(v___x_3438_, 0, v_cs_x27_3472_);
v___x_3474_ = v___x_3438_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_cs_x27_3472_);
lean_ctor_set(v_reuseFailAlloc_3475_, 1, v_snd_3441_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
v_a_3449_ = v___x_3474_;
goto v___jp_3448_;
}
}
v___jp_3448_:
{
lean_object* v___x_3451_; 
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 1, v_a_3449_);
lean_ctor_set(v___x_3443_, 0, v___x_3447_);
v___x_3451_ = v___x_3443_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3447_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_a_3449_);
v___x_3451_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
size_t v___x_3452_; size_t v___x_3453_; 
v___x_3452_ = ((size_t)1ULL);
v___x_3453_ = lean_usize_add(v_i_3433_, v___x_3452_);
v_i_3433_ = v___x_3453_;
v_b_3434_ = v___x_3451_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3479_, lean_object* v_as_3480_, lean_object* v_sz_3481_, lean_object* v_i_3482_, lean_object* v_b_3483_){
_start:
{
size_t v_sz_boxed_3484_; size_t v_i_boxed_3485_; lean_object* v_res_3486_; 
v_sz_boxed_3484_ = lean_unbox_usize(v_sz_3481_);
lean_dec(v_sz_3481_);
v_i_boxed_3485_ = lean_unbox_usize(v_i_3482_);
lean_dec(v_i_3482_);
v_res_3486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3479_, v_as_3480_, v_sz_boxed_3484_, v_i_boxed_3485_, v_b_3483_);
lean_dec_ref(v_as_3480_);
lean_dec(v_x_3479_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_3487_, lean_object* v_as_3488_, size_t v_sz_3489_, size_t v_i_3490_, lean_object* v_b_3491_){
_start:
{
uint8_t v___x_3492_; 
v___x_3492_ = lean_usize_dec_lt(v_i_3490_, v_sz_3489_);
if (v___x_3492_ == 0)
{
return v_b_3491_;
}
else
{
lean_object* v_snd_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3534_; 
v_snd_3493_ = lean_ctor_get(v_b_3491_, 1);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_b_3491_);
if (v_isSharedCheck_3534_ == 0)
{
lean_object* v_unused_3535_; 
v_unused_3535_ = lean_ctor_get(v_b_3491_, 0);
lean_dec(v_unused_3535_);
v___x_3495_ = v_b_3491_;
v_isShared_3496_ = v_isSharedCheck_3534_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_snd_3493_);
lean_dec(v_b_3491_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3534_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v_fst_3497_; lean_object* v_snd_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3533_; 
v_fst_3497_ = lean_ctor_get(v_snd_3493_, 0);
v_snd_3498_ = lean_ctor_get(v_snd_3493_, 1);
v_isSharedCheck_3533_ = !lean_is_exclusive(v_snd_3493_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3500_ = v_snd_3493_;
v_isShared_3501_ = v_isSharedCheck_3533_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_snd_3498_);
lean_inc(v_fst_3497_);
lean_dec(v_snd_3493_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3533_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v_a_3502_; lean_object* v_p_3503_; lean_object* v___x_3504_; lean_object* v_a_3506_; lean_object* v_b_3513_; lean_object* v___x_3514_; uint8_t v___x_3515_; 
v_a_3502_ = lean_array_uget(v_as_3488_, v_i_3490_);
v_p_3503_ = lean_ctor_get(v_a_3502_, 0);
v___x_3504_ = lean_box(0);
v_b_3513_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3503_, v_x_3487_);
v___x_3514_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3515_ = lean_int_dec_eq(v_b_3513_, v___x_3514_);
if (v___x_3515_ == 0)
{
lean_object* v___x_3517_; 
lean_inc(v_a_3502_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 1, v_a_3502_);
lean_ctor_set(v___x_3495_, 0, v_b_3513_);
v___x_3517_ = v___x_3495_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_b_3513_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v_a_3502_);
v___x_3517_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3525_; 
v_isSharedCheck_3525_ = !lean_is_exclusive(v_a_3502_);
if (v_isSharedCheck_3525_ == 0)
{
lean_object* v_unused_3526_; lean_object* v_unused_3527_; 
v_unused_3526_ = lean_ctor_get(v_a_3502_, 1);
lean_dec(v_unused_3526_);
v_unused_3527_ = lean_ctor_get(v_a_3502_, 0);
lean_dec(v_unused_3527_);
v___x_3519_ = v_a_3502_;
v_isShared_3520_ = v_isSharedCheck_3525_;
goto v_resetjp_3518_;
}
else
{
lean_dec(v_a_3502_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3525_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v_todo_3521_; lean_object* v___x_3523_; 
v_todo_3521_ = lean_array_push(v_snd_3498_, v___x_3517_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 1, v_todo_3521_);
lean_ctor_set(v___x_3519_, 0, v_fst_3497_);
v___x_3523_ = v___x_3519_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_fst_3497_);
lean_ctor_set(v_reuseFailAlloc_3524_, 1, v_todo_3521_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
v_a_3506_ = v___x_3523_;
goto v___jp_3505_;
}
}
}
}
else
{
lean_object* v_cs_x27_3529_; lean_object* v___x_3531_; 
lean_dec(v_b_3513_);
v_cs_x27_3529_ = l_Lean_PersistentArray_push___redArg(v_fst_3497_, v_a_3502_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 1, v_snd_3498_);
lean_ctor_set(v___x_3495_, 0, v_cs_x27_3529_);
v___x_3531_ = v___x_3495_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_cs_x27_3529_);
lean_ctor_set(v_reuseFailAlloc_3532_, 1, v_snd_3498_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
v_a_3506_ = v___x_3531_;
goto v___jp_3505_;
}
}
v___jp_3505_:
{
lean_object* v___x_3508_; 
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 1, v_a_3506_);
lean_ctor_set(v___x_3500_, 0, v___x_3504_);
v___x_3508_ = v___x_3500_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v___x_3504_);
lean_ctor_set(v_reuseFailAlloc_3512_, 1, v_a_3506_);
v___x_3508_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
size_t v___x_3509_; size_t v___x_3510_; lean_object* v___x_3511_; 
v___x_3509_ = ((size_t)1ULL);
v___x_3510_ = lean_usize_add(v_i_3490_, v___x_3509_);
v___x_3511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3487_, v_as_3488_, v_sz_3489_, v___x_3510_, v___x_3508_);
return v___x_3511_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_3536_, lean_object* v_as_3537_, lean_object* v_sz_3538_, lean_object* v_i_3539_, lean_object* v_b_3540_){
_start:
{
size_t v_sz_boxed_3541_; size_t v_i_boxed_3542_; lean_object* v_res_3543_; 
v_sz_boxed_3541_ = lean_unbox_usize(v_sz_3538_);
lean_dec(v_sz_3538_);
v_i_boxed_3542_ = lean_unbox_usize(v_i_3539_);
lean_dec(v_i_3539_);
v_res_3543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3536_, v_as_3537_, v_sz_boxed_3541_, v_i_boxed_3542_, v_b_3540_);
lean_dec_ref(v_as_3537_);
lean_dec(v_x_3536_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(lean_object* v_init_3544_, lean_object* v_x_3545_, lean_object* v_n_3546_, lean_object* v_b_3547_){
_start:
{
if (lean_obj_tag(v_n_3546_) == 0)
{
lean_object* v_cs_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; size_t v_sz_3551_; size_t v___x_3552_; lean_object* v___x_3553_; lean_object* v_fst_3554_; 
v_cs_3548_ = lean_ctor_get(v_n_3546_, 0);
v___x_3549_ = lean_box(0);
v___x_3550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
lean_ctor_set(v___x_3550_, 1, v_b_3547_);
v_sz_3551_ = lean_array_size(v_cs_3548_);
v___x_3552_ = ((size_t)0ULL);
v___x_3553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3544_, v_x_3545_, v_cs_3548_, v_sz_3551_, v___x_3552_, v___x_3550_);
v_fst_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_fst_3554_);
if (lean_obj_tag(v_fst_3554_) == 0)
{
lean_object* v_snd_3555_; lean_object* v___x_3556_; 
v_snd_3555_ = lean_ctor_get(v___x_3553_, 1);
lean_inc(v_snd_3555_);
lean_dec_ref(v___x_3553_);
v___x_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3556_, 0, v_snd_3555_);
return v___x_3556_;
}
else
{
lean_object* v_val_3557_; 
lean_dec_ref(v___x_3553_);
v_val_3557_ = lean_ctor_get(v_fst_3554_, 0);
lean_inc(v_val_3557_);
lean_dec_ref_known(v_fst_3554_, 1);
return v_val_3557_;
}
}
else
{
lean_object* v_vs_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; size_t v_sz_3561_; size_t v___x_3562_; lean_object* v___x_3563_; lean_object* v_fst_3564_; 
v_vs_3558_ = lean_ctor_get(v_n_3546_, 0);
v___x_3559_ = lean_box(0);
v___x_3560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3559_);
lean_ctor_set(v___x_3560_, 1, v_b_3547_);
v_sz_3561_ = lean_array_size(v_vs_3558_);
v___x_3562_ = ((size_t)0ULL);
v___x_3563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3545_, v_vs_3558_, v_sz_3561_, v___x_3562_, v___x_3560_);
v_fst_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_fst_3564_);
if (lean_obj_tag(v_fst_3564_) == 0)
{
lean_object* v_snd_3565_; lean_object* v___x_3566_; 
v_snd_3565_ = lean_ctor_get(v___x_3563_, 1);
lean_inc(v_snd_3565_);
lean_dec_ref(v___x_3563_);
v___x_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3566_, 0, v_snd_3565_);
return v___x_3566_;
}
else
{
lean_object* v_val_3567_; 
lean_dec_ref(v___x_3563_);
v_val_3567_ = lean_ctor_get(v_fst_3564_, 0);
lean_inc(v_val_3567_);
lean_dec_ref_known(v_fst_3564_, 1);
return v_val_3567_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3568_, lean_object* v_x_3569_, lean_object* v_as_3570_, size_t v_sz_3571_, size_t v_i_3572_, lean_object* v_b_3573_){
_start:
{
uint8_t v___x_3574_; 
v___x_3574_ = lean_usize_dec_lt(v_i_3572_, v_sz_3571_);
if (v___x_3574_ == 0)
{
return v_b_3573_;
}
else
{
lean_object* v_snd_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3593_; 
v_snd_3575_ = lean_ctor_get(v_b_3573_, 1);
v_isSharedCheck_3593_ = !lean_is_exclusive(v_b_3573_);
if (v_isSharedCheck_3593_ == 0)
{
lean_object* v_unused_3594_; 
v_unused_3594_ = lean_ctor_get(v_b_3573_, 0);
lean_dec(v_unused_3594_);
v___x_3577_ = v_b_3573_;
v_isShared_3578_ = v_isSharedCheck_3593_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_snd_3575_);
lean_dec(v_b_3573_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3593_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v_a_3579_; lean_object* v___x_3580_; 
v_a_3579_ = lean_array_uget_borrowed(v_as_3570_, v_i_3572_);
lean_inc(v_snd_3575_);
v___x_3580_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3568_, v_x_3569_, v_a_3579_, v_snd_3575_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v___x_3581_; lean_object* v___x_3583_; 
v___x_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3580_);
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 0, v___x_3581_);
v___x_3583_ = v___x_3577_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3581_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v_snd_3575_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3586_; lean_object* v___x_3588_; 
lean_dec(v_snd_3575_);
v_a_3585_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_a_3585_);
lean_dec_ref_known(v___x_3580_, 1);
v___x_3586_ = lean_box(0);
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 1, v_a_3585_);
lean_ctor_set(v___x_3577_, 0, v___x_3586_);
v___x_3588_ = v___x_3577_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3586_);
lean_ctor_set(v_reuseFailAlloc_3592_, 1, v_a_3585_);
v___x_3588_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
size_t v___x_3589_; size_t v___x_3590_; 
v___x_3589_ = ((size_t)1ULL);
v___x_3590_ = lean_usize_add(v_i_3572_, v___x_3589_);
v_i_3572_ = v___x_3590_;
v_b_3573_ = v___x_3588_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3595_, lean_object* v_x_3596_, lean_object* v_as_3597_, lean_object* v_sz_3598_, lean_object* v_i_3599_, lean_object* v_b_3600_){
_start:
{
size_t v_sz_boxed_3601_; size_t v_i_boxed_3602_; lean_object* v_res_3603_; 
v_sz_boxed_3601_ = lean_unbox_usize(v_sz_3598_);
lean_dec(v_sz_3598_);
v_i_boxed_3602_ = lean_unbox_usize(v_i_3599_);
lean_dec(v_i_3599_);
v_res_3603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3595_, v_x_3596_, v_as_3597_, v_sz_boxed_3601_, v_i_boxed_3602_, v_b_3600_);
lean_dec_ref(v_as_3597_);
lean_dec(v_x_3596_);
lean_dec_ref(v_init_3595_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3604_, lean_object* v_x_3605_, lean_object* v_n_3606_, lean_object* v_b_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3604_, v_x_3605_, v_n_3606_, v_b_3607_);
lean_dec_ref(v_n_3606_);
lean_dec(v_x_3605_);
lean_dec_ref(v_init_3604_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object* v_x_3609_, lean_object* v_t_3610_, lean_object* v_init_3611_){
_start:
{
lean_object* v_root_3612_; lean_object* v_tail_3613_; lean_object* v___x_3614_; 
v_root_3612_ = lean_ctor_get(v_t_3610_, 0);
v_tail_3613_ = lean_ctor_get(v_t_3610_, 1);
lean_inc_ref(v_init_3611_);
v___x_3614_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3611_, v_x_3609_, v_root_3612_, v_init_3611_);
lean_dec_ref(v_init_3611_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v_a_3615_; 
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_a_3615_);
lean_dec_ref_known(v___x_3614_, 1);
return v_a_3615_;
}
else
{
lean_object* v_a_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; size_t v_sz_3619_; size_t v___x_3620_; lean_object* v___x_3621_; lean_object* v_fst_3622_; 
v_a_3616_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_a_3616_);
lean_dec_ref_known(v___x_3614_, 1);
v___x_3617_ = lean_box(0);
v___x_3618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
lean_ctor_set(v___x_3618_, 1, v_a_3616_);
v_sz_3619_ = lean_array_size(v_tail_3613_);
v___x_3620_ = ((size_t)0ULL);
v___x_3621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3609_, v_tail_3613_, v_sz_3619_, v___x_3620_, v___x_3618_);
v_fst_3622_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_fst_3622_);
if (lean_obj_tag(v_fst_3622_) == 0)
{
lean_object* v_snd_3623_; 
v_snd_3623_ = lean_ctor_get(v___x_3621_, 1);
lean_inc(v_snd_3623_);
lean_dec_ref(v___x_3621_);
return v_snd_3623_;
}
else
{
lean_object* v_val_3624_; 
lean_dec_ref(v___x_3621_);
v_val_3624_ = lean_ctor_get(v_fst_3622_, 0);
lean_inc(v_val_3624_);
lean_dec_ref_known(v_fst_3622_, 1);
return v_val_3624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object* v_x_3625_, lean_object* v_t_3626_, lean_object* v_init_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3625_, v_t_3626_, v_init_3627_);
lean_dec_ref(v_t_3626_);
lean_dec(v_x_3625_);
return v_res_3628_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3629_ = lean_unsigned_to_nat(32u);
v___x_3630_ = lean_mk_empty_array_with_capacity(v___x_3629_);
v___x_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3630_);
return v___x_3631_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1(void){
_start:
{
size_t v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v_cs_x27_3637_; 
v___x_3632_ = ((size_t)5ULL);
v___x_3633_ = lean_unsigned_to_nat(0u);
v___x_3634_ = lean_unsigned_to_nat(32u);
v___x_3635_ = lean_mk_empty_array_with_capacity(v___x_3634_);
v___x_3636_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0);
v_cs_x27_3637_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_3637_, 0, v___x_3636_);
lean_ctor_set(v_cs_x27_3637_, 1, v___x_3635_);
lean_ctor_set(v_cs_x27_3637_, 2, v___x_3633_);
lean_ctor_set(v_cs_x27_3637_, 3, v___x_3633_);
lean_ctor_set_usize(v_cs_x27_3637_, 4, v___x_3632_);
return v_cs_x27_3637_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_3640_; lean_object* v_cs_x27_3641_; lean_object* v___x_3642_; 
v_todo_3640_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2));
v_cs_x27_3641_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1);
v___x_3642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3642_, 0, v_cs_x27_3641_);
lean_ctor_set(v___x_3642_, 1, v_todo_3640_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object* v_x_3643_, lean_object* v_cs_3644_){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v_fst_3647_; lean_object* v_snd_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
v___x_3645_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3);
v___x_3646_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3643_, v_cs_3644_, v___x_3645_);
v_fst_3647_ = lean_ctor_get(v___x_3646_, 0);
v_snd_3648_ = lean_ctor_get(v___x_3646_, 1);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3650_ = v___x_3646_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_snd_3648_);
lean_inc(v_fst_3647_);
lean_dec(v___x_3646_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
if (v_isShared_3651_ == 0)
{
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_fst_3647_);
lean_ctor_set(v_reuseFailAlloc_3654_, 1, v_snd_3648_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object* v_x_3656_, lean_object* v_cs_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3656_, v_cs_3657_);
lean_dec_ref(v_cs_3657_);
lean_dec(v_x_3656_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object* v_x_3659_, lean_object* v_cs_3660_){
_start:
{
lean_object* v___x_3661_; 
v___x_3661_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3659_, v_cs_3660_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object* v_x_3662_, lean_object* v_cs_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(v_x_3662_, v_cs_3663_);
lean_dec_ref(v_cs_3663_);
lean_dec(v_x_3662_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(lean_object* v_a_3665_, lean_object* v_y_3666_, lean_object* v_fst_3667_, lean_object* v_s_3668_){
_start:
{
lean_object* v_structs_3669_; lean_object* v_typeIdOf_3670_; lean_object* v_exprToStructId_3671_; lean_object* v_exprToStructIdEntries_3672_; lean_object* v_forbiddenNatModules_3673_; lean_object* v_natStructs_3674_; lean_object* v_natTypeIdOf_3675_; lean_object* v_exprToNatStructId_3676_; lean_object* v___x_3677_; uint8_t v___x_3678_; 
v_structs_3669_ = lean_ctor_get(v_s_3668_, 0);
v_typeIdOf_3670_ = lean_ctor_get(v_s_3668_, 1);
v_exprToStructId_3671_ = lean_ctor_get(v_s_3668_, 2);
v_exprToStructIdEntries_3672_ = lean_ctor_get(v_s_3668_, 3);
v_forbiddenNatModules_3673_ = lean_ctor_get(v_s_3668_, 4);
v_natStructs_3674_ = lean_ctor_get(v_s_3668_, 5);
v_natTypeIdOf_3675_ = lean_ctor_get(v_s_3668_, 6);
v_exprToNatStructId_3676_ = lean_ctor_get(v_s_3668_, 7);
v___x_3677_ = lean_array_get_size(v_structs_3669_);
v___x_3678_ = lean_nat_dec_lt(v_a_3665_, v___x_3677_);
if (v___x_3678_ == 0)
{
lean_dec_ref(v_fst_3667_);
return v_s_3668_;
}
else
{
lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3740_; 
lean_inc_ref(v_exprToNatStructId_3676_);
lean_inc_ref(v_natTypeIdOf_3675_);
lean_inc_ref(v_natStructs_3674_);
lean_inc_ref(v_forbiddenNatModules_3673_);
lean_inc_ref(v_exprToStructIdEntries_3672_);
lean_inc_ref(v_exprToStructId_3671_);
lean_inc_ref(v_typeIdOf_3670_);
lean_inc_ref(v_structs_3669_);
v_isSharedCheck_3740_ = !lean_is_exclusive(v_s_3668_);
if (v_isSharedCheck_3740_ == 0)
{
lean_object* v_unused_3741_; lean_object* v_unused_3742_; lean_object* v_unused_3743_; lean_object* v_unused_3744_; lean_object* v_unused_3745_; lean_object* v_unused_3746_; lean_object* v_unused_3747_; lean_object* v_unused_3748_; 
v_unused_3741_ = lean_ctor_get(v_s_3668_, 7);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v_s_3668_, 6);
lean_dec(v_unused_3742_);
v_unused_3743_ = lean_ctor_get(v_s_3668_, 5);
lean_dec(v_unused_3743_);
v_unused_3744_ = lean_ctor_get(v_s_3668_, 4);
lean_dec(v_unused_3744_);
v_unused_3745_ = lean_ctor_get(v_s_3668_, 3);
lean_dec(v_unused_3745_);
v_unused_3746_ = lean_ctor_get(v_s_3668_, 2);
lean_dec(v_unused_3746_);
v_unused_3747_ = lean_ctor_get(v_s_3668_, 1);
lean_dec(v_unused_3747_);
v_unused_3748_ = lean_ctor_get(v_s_3668_, 0);
lean_dec(v_unused_3748_);
v___x_3680_ = v_s_3668_;
v_isShared_3681_ = v_isSharedCheck_3740_;
goto v_resetjp_3679_;
}
else
{
lean_dec(v_s_3668_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3740_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v_v_3682_; lean_object* v_id_3683_; lean_object* v_ringId_x3f_3684_; lean_object* v_type_3685_; lean_object* v_u_3686_; lean_object* v_intModuleInst_3687_; lean_object* v_leInst_x3f_3688_; lean_object* v_ltInst_x3f_3689_; lean_object* v_lawfulOrderLTInst_x3f_3690_; lean_object* v_isPreorderInst_x3f_3691_; lean_object* v_orderedAddInst_x3f_3692_; lean_object* v_isLinearInst_x3f_3693_; lean_object* v_noNatDivInst_x3f_3694_; lean_object* v_ringInst_x3f_3695_; lean_object* v_commRingInst_x3f_3696_; lean_object* v_orderedRingInst_x3f_3697_; lean_object* v_fieldInst_x3f_3698_; lean_object* v_charInst_x3f_3699_; lean_object* v_zero_3700_; lean_object* v_ofNatZero_3701_; lean_object* v_one_x3f_3702_; lean_object* v_leFn_x3f_3703_; lean_object* v_ltFn_x3f_3704_; lean_object* v_addFn_3705_; lean_object* v_zsmulFn_3706_; lean_object* v_nsmulFn_3707_; lean_object* v_zsmulFn_x3f_3708_; lean_object* v_nsmulFn_x3f_3709_; lean_object* v_homomulFn_x3f_3710_; lean_object* v_subFn_3711_; lean_object* v_negFn_3712_; lean_object* v_vars_3713_; lean_object* v_varMap_3714_; lean_object* v_lowers_3715_; lean_object* v_uppers_3716_; lean_object* v_diseqs_3717_; lean_object* v_assignment_3718_; uint8_t v_caseSplits_3719_; lean_object* v_conflict_x3f_3720_; lean_object* v_diseqSplits_3721_; lean_object* v_elimEqs_3722_; lean_object* v_elimStack_3723_; lean_object* v_occurs_3724_; lean_object* v_ignored_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3739_; 
v_v_3682_ = lean_array_fget(v_structs_3669_, v_a_3665_);
v_id_3683_ = lean_ctor_get(v_v_3682_, 0);
v_ringId_x3f_3684_ = lean_ctor_get(v_v_3682_, 1);
v_type_3685_ = lean_ctor_get(v_v_3682_, 2);
v_u_3686_ = lean_ctor_get(v_v_3682_, 3);
v_intModuleInst_3687_ = lean_ctor_get(v_v_3682_, 4);
v_leInst_x3f_3688_ = lean_ctor_get(v_v_3682_, 5);
v_ltInst_x3f_3689_ = lean_ctor_get(v_v_3682_, 6);
v_lawfulOrderLTInst_x3f_3690_ = lean_ctor_get(v_v_3682_, 7);
v_isPreorderInst_x3f_3691_ = lean_ctor_get(v_v_3682_, 8);
v_orderedAddInst_x3f_3692_ = lean_ctor_get(v_v_3682_, 9);
v_isLinearInst_x3f_3693_ = lean_ctor_get(v_v_3682_, 10);
v_noNatDivInst_x3f_3694_ = lean_ctor_get(v_v_3682_, 11);
v_ringInst_x3f_3695_ = lean_ctor_get(v_v_3682_, 12);
v_commRingInst_x3f_3696_ = lean_ctor_get(v_v_3682_, 13);
v_orderedRingInst_x3f_3697_ = lean_ctor_get(v_v_3682_, 14);
v_fieldInst_x3f_3698_ = lean_ctor_get(v_v_3682_, 15);
v_charInst_x3f_3699_ = lean_ctor_get(v_v_3682_, 16);
v_zero_3700_ = lean_ctor_get(v_v_3682_, 17);
v_ofNatZero_3701_ = lean_ctor_get(v_v_3682_, 18);
v_one_x3f_3702_ = lean_ctor_get(v_v_3682_, 19);
v_leFn_x3f_3703_ = lean_ctor_get(v_v_3682_, 20);
v_ltFn_x3f_3704_ = lean_ctor_get(v_v_3682_, 21);
v_addFn_3705_ = lean_ctor_get(v_v_3682_, 22);
v_zsmulFn_3706_ = lean_ctor_get(v_v_3682_, 23);
v_nsmulFn_3707_ = lean_ctor_get(v_v_3682_, 24);
v_zsmulFn_x3f_3708_ = lean_ctor_get(v_v_3682_, 25);
v_nsmulFn_x3f_3709_ = lean_ctor_get(v_v_3682_, 26);
v_homomulFn_x3f_3710_ = lean_ctor_get(v_v_3682_, 27);
v_subFn_3711_ = lean_ctor_get(v_v_3682_, 28);
v_negFn_3712_ = lean_ctor_get(v_v_3682_, 29);
v_vars_3713_ = lean_ctor_get(v_v_3682_, 30);
v_varMap_3714_ = lean_ctor_get(v_v_3682_, 31);
v_lowers_3715_ = lean_ctor_get(v_v_3682_, 32);
v_uppers_3716_ = lean_ctor_get(v_v_3682_, 33);
v_diseqs_3717_ = lean_ctor_get(v_v_3682_, 34);
v_assignment_3718_ = lean_ctor_get(v_v_3682_, 35);
v_caseSplits_3719_ = lean_ctor_get_uint8(v_v_3682_, sizeof(void*)*42);
v_conflict_x3f_3720_ = lean_ctor_get(v_v_3682_, 36);
v_diseqSplits_3721_ = lean_ctor_get(v_v_3682_, 37);
v_elimEqs_3722_ = lean_ctor_get(v_v_3682_, 38);
v_elimStack_3723_ = lean_ctor_get(v_v_3682_, 39);
v_occurs_3724_ = lean_ctor_get(v_v_3682_, 40);
v_ignored_3725_ = lean_ctor_get(v_v_3682_, 41);
v_isSharedCheck_3739_ = !lean_is_exclusive(v_v_3682_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3727_ = v_v_3682_;
v_isShared_3728_ = v_isSharedCheck_3739_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_ignored_3725_);
lean_inc(v_occurs_3724_);
lean_inc(v_elimStack_3723_);
lean_inc(v_elimEqs_3722_);
lean_inc(v_diseqSplits_3721_);
lean_inc(v_conflict_x3f_3720_);
lean_inc(v_assignment_3718_);
lean_inc(v_diseqs_3717_);
lean_inc(v_uppers_3716_);
lean_inc(v_lowers_3715_);
lean_inc(v_varMap_3714_);
lean_inc(v_vars_3713_);
lean_inc(v_negFn_3712_);
lean_inc(v_subFn_3711_);
lean_inc(v_homomulFn_x3f_3710_);
lean_inc(v_nsmulFn_x3f_3709_);
lean_inc(v_zsmulFn_x3f_3708_);
lean_inc(v_nsmulFn_3707_);
lean_inc(v_zsmulFn_3706_);
lean_inc(v_addFn_3705_);
lean_inc(v_ltFn_x3f_3704_);
lean_inc(v_leFn_x3f_3703_);
lean_inc(v_one_x3f_3702_);
lean_inc(v_ofNatZero_3701_);
lean_inc(v_zero_3700_);
lean_inc(v_charInst_x3f_3699_);
lean_inc(v_fieldInst_x3f_3698_);
lean_inc(v_orderedRingInst_x3f_3697_);
lean_inc(v_commRingInst_x3f_3696_);
lean_inc(v_ringInst_x3f_3695_);
lean_inc(v_noNatDivInst_x3f_3694_);
lean_inc(v_isLinearInst_x3f_3693_);
lean_inc(v_orderedAddInst_x3f_3692_);
lean_inc(v_isPreorderInst_x3f_3691_);
lean_inc(v_lawfulOrderLTInst_x3f_3690_);
lean_inc(v_ltInst_x3f_3689_);
lean_inc(v_leInst_x3f_3688_);
lean_inc(v_intModuleInst_3687_);
lean_inc(v_u_3686_);
lean_inc(v_type_3685_);
lean_inc(v_ringId_x3f_3684_);
lean_inc(v_id_3683_);
lean_dec(v_v_3682_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3739_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3729_; lean_object* v_xs_x27_3730_; lean_object* v___x_3731_; lean_object* v___x_3733_; 
v___x_3729_ = lean_box(0);
v_xs_x27_3730_ = lean_array_fset(v_structs_3669_, v_a_3665_, v___x_3729_);
v___x_3731_ = l_Lean_PersistentArray_set___redArg(v_diseqs_3717_, v_y_3666_, v_fst_3667_);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 34, v___x_3731_);
v___x_3733_ = v___x_3727_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_id_3683_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_ringId_x3f_3684_);
lean_ctor_set(v_reuseFailAlloc_3738_, 2, v_type_3685_);
lean_ctor_set(v_reuseFailAlloc_3738_, 3, v_u_3686_);
lean_ctor_set(v_reuseFailAlloc_3738_, 4, v_intModuleInst_3687_);
lean_ctor_set(v_reuseFailAlloc_3738_, 5, v_leInst_x3f_3688_);
lean_ctor_set(v_reuseFailAlloc_3738_, 6, v_ltInst_x3f_3689_);
lean_ctor_set(v_reuseFailAlloc_3738_, 7, v_lawfulOrderLTInst_x3f_3690_);
lean_ctor_set(v_reuseFailAlloc_3738_, 8, v_isPreorderInst_x3f_3691_);
lean_ctor_set(v_reuseFailAlloc_3738_, 9, v_orderedAddInst_x3f_3692_);
lean_ctor_set(v_reuseFailAlloc_3738_, 10, v_isLinearInst_x3f_3693_);
lean_ctor_set(v_reuseFailAlloc_3738_, 11, v_noNatDivInst_x3f_3694_);
lean_ctor_set(v_reuseFailAlloc_3738_, 12, v_ringInst_x3f_3695_);
lean_ctor_set(v_reuseFailAlloc_3738_, 13, v_commRingInst_x3f_3696_);
lean_ctor_set(v_reuseFailAlloc_3738_, 14, v_orderedRingInst_x3f_3697_);
lean_ctor_set(v_reuseFailAlloc_3738_, 15, v_fieldInst_x3f_3698_);
lean_ctor_set(v_reuseFailAlloc_3738_, 16, v_charInst_x3f_3699_);
lean_ctor_set(v_reuseFailAlloc_3738_, 17, v_zero_3700_);
lean_ctor_set(v_reuseFailAlloc_3738_, 18, v_ofNatZero_3701_);
lean_ctor_set(v_reuseFailAlloc_3738_, 19, v_one_x3f_3702_);
lean_ctor_set(v_reuseFailAlloc_3738_, 20, v_leFn_x3f_3703_);
lean_ctor_set(v_reuseFailAlloc_3738_, 21, v_ltFn_x3f_3704_);
lean_ctor_set(v_reuseFailAlloc_3738_, 22, v_addFn_3705_);
lean_ctor_set(v_reuseFailAlloc_3738_, 23, v_zsmulFn_3706_);
lean_ctor_set(v_reuseFailAlloc_3738_, 24, v_nsmulFn_3707_);
lean_ctor_set(v_reuseFailAlloc_3738_, 25, v_zsmulFn_x3f_3708_);
lean_ctor_set(v_reuseFailAlloc_3738_, 26, v_nsmulFn_x3f_3709_);
lean_ctor_set(v_reuseFailAlloc_3738_, 27, v_homomulFn_x3f_3710_);
lean_ctor_set(v_reuseFailAlloc_3738_, 28, v_subFn_3711_);
lean_ctor_set(v_reuseFailAlloc_3738_, 29, v_negFn_3712_);
lean_ctor_set(v_reuseFailAlloc_3738_, 30, v_vars_3713_);
lean_ctor_set(v_reuseFailAlloc_3738_, 31, v_varMap_3714_);
lean_ctor_set(v_reuseFailAlloc_3738_, 32, v_lowers_3715_);
lean_ctor_set(v_reuseFailAlloc_3738_, 33, v_uppers_3716_);
lean_ctor_set(v_reuseFailAlloc_3738_, 34, v___x_3731_);
lean_ctor_set(v_reuseFailAlloc_3738_, 35, v_assignment_3718_);
lean_ctor_set(v_reuseFailAlloc_3738_, 36, v_conflict_x3f_3720_);
lean_ctor_set(v_reuseFailAlloc_3738_, 37, v_diseqSplits_3721_);
lean_ctor_set(v_reuseFailAlloc_3738_, 38, v_elimEqs_3722_);
lean_ctor_set(v_reuseFailAlloc_3738_, 39, v_elimStack_3723_);
lean_ctor_set(v_reuseFailAlloc_3738_, 40, v_occurs_3724_);
lean_ctor_set(v_reuseFailAlloc_3738_, 41, v_ignored_3725_);
lean_ctor_set_uint8(v_reuseFailAlloc_3738_, sizeof(void*)*42, v_caseSplits_3719_);
v___x_3733_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
lean_object* v___x_3734_; lean_object* v___x_3736_; 
v___x_3734_ = lean_array_fset(v_xs_x27_3730_, v_a_3665_, v___x_3733_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 0, v___x_3734_);
v___x_3736_ = v___x_3680_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3734_);
lean_ctor_set(v_reuseFailAlloc_3737_, 1, v_typeIdOf_3670_);
lean_ctor_set(v_reuseFailAlloc_3737_, 2, v_exprToStructId_3671_);
lean_ctor_set(v_reuseFailAlloc_3737_, 3, v_exprToStructIdEntries_3672_);
lean_ctor_set(v_reuseFailAlloc_3737_, 4, v_forbiddenNatModules_3673_);
lean_ctor_set(v_reuseFailAlloc_3737_, 5, v_natStructs_3674_);
lean_ctor_set(v_reuseFailAlloc_3737_, 6, v_natTypeIdOf_3675_);
lean_ctor_set(v_reuseFailAlloc_3737_, 7, v_exprToNatStructId_3676_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed(lean_object* v_a_3749_, lean_object* v_y_3750_, lean_object* v_fst_3751_, lean_object* v_s_3752_){
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(v_a_3749_, v_y_3750_, v_fst_3751_, v_s_3752_);
lean_dec(v_y_3750_);
lean_dec(v_a_3749_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object* v_a_3754_, lean_object* v_x_3755_, lean_object* v_c_3756_, lean_object* v_as_3757_, size_t v_sz_3758_, size_t v_i_3759_, lean_object* v_b_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v_a_3774_; uint8_t v___x_3778_; 
v___x_3778_ = lean_usize_dec_lt(v_i_3759_, v_sz_3758_);
if (v___x_3778_ == 0)
{
lean_object* v___x_3779_; 
lean_dec_ref(v_c_3756_);
v___x_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3779_, 0, v_b_3760_);
return v___x_3779_;
}
else
{
lean_object* v_a_3780_; lean_object* v_fst_3781_; lean_object* v_snd_3782_; lean_object* v___x_3783_; 
lean_dec_ref(v_b_3760_);
v_a_3780_ = lean_array_uget_borrowed(v_as_3757_, v_i_3759_);
v_fst_3781_ = lean_ctor_get(v_a_3780_, 0);
v_snd_3782_ = lean_ctor_get(v_a_3780_, 1);
lean_inc(v_snd_3782_);
lean_inc(v_fst_3781_);
lean_inc_ref(v_c_3756_);
v___x_3783_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_3754_, v_x_3755_, v_c_3756_, v_fst_3781_, v_snd_3782_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; lean_object* v___x_3785_; 
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_a_3784_);
lean_dec_ref_known(v___x_3783_, 1);
v___x_3785_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
if (lean_obj_tag(v_a_3784_) == 1)
{
lean_object* v_val_3786_; lean_object* v___x_3787_; 
v_val_3786_ = lean_ctor_get(v_a_3784_, 0);
lean_inc(v_val_3786_);
lean_dec_ref_known(v_a_3784_, 1);
v___x_3787_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_val_3786_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v___x_3788_; 
lean_dec_ref_known(v___x_3787_, 1);
v___x_3788_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3798_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3791_ = v___x_3788_;
v_isShared_3792_ = v_isSharedCheck_3798_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3788_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3798_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
uint8_t v___x_3793_; 
v___x_3793_ = lean_unbox(v_a_3789_);
lean_dec(v_a_3789_);
if (v___x_3793_ == 0)
{
lean_del_object(v___x_3791_);
v_a_3774_ = v___x_3785_;
goto v___jp_3773_;
}
else
{
lean_object* v___x_3794_; lean_object* v___x_3796_; 
lean_dec_ref(v_c_3756_);
v___x_3794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v___x_3794_);
v___x_3796_ = v___x_3791_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3794_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
lean_dec_ref(v_c_3756_);
v_a_3799_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3788_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3788_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
else
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3814_; 
lean_dec_ref(v_c_3756_);
v_a_3807_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3809_ = v___x_3787_;
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3787_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3810_ == 0)
{
v___x_3812_ = v___x_3809_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
else
{
lean_object* v___x_3815_; 
lean_dec(v_a_3784_);
v___x_3815_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_snd_3782_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_dec_ref_known(v___x_3815_, 1);
v_a_3774_ = v___x_3785_;
goto v___jp_3773_;
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
lean_dec_ref(v_c_3756_);
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3815_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3815_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_dec_ref(v_c_3756_);
v_a_3824_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3783_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3783_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
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
v___jp_3773_:
{
size_t v___x_3775_; size_t v___x_3776_; 
v___x_3775_ = ((size_t)1ULL);
v___x_3776_ = lean_usize_add(v_i_3759_, v___x_3775_);
lean_inc_ref(v_a_3774_);
v_i_3759_ = v___x_3776_;
v_b_3760_ = v_a_3774_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object** _args){
lean_object* v_a_3832_ = _args[0];
lean_object* v_x_3833_ = _args[1];
lean_object* v_c_3834_ = _args[2];
lean_object* v_as_3835_ = _args[3];
lean_object* v_sz_3836_ = _args[4];
lean_object* v_i_3837_ = _args[5];
lean_object* v_b_3838_ = _args[6];
lean_object* v___y_3839_ = _args[7];
lean_object* v___y_3840_ = _args[8];
lean_object* v___y_3841_ = _args[9];
lean_object* v___y_3842_ = _args[10];
lean_object* v___y_3843_ = _args[11];
lean_object* v___y_3844_ = _args[12];
lean_object* v___y_3845_ = _args[13];
lean_object* v___y_3846_ = _args[14];
lean_object* v___y_3847_ = _args[15];
lean_object* v___y_3848_ = _args[16];
lean_object* v___y_3849_ = _args[17];
lean_object* v___y_3850_ = _args[18];
_start:
{
size_t v_sz_boxed_3851_; size_t v_i_boxed_3852_; lean_object* v_res_3853_; 
v_sz_boxed_3851_ = lean_unbox_usize(v_sz_3836_);
lean_dec(v_sz_3836_);
v_i_boxed_3852_ = lean_unbox_usize(v_i_3837_);
lean_dec(v_i_3837_);
v_res_3853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3832_, v_x_3833_, v_c_3834_, v_as_3835_, v_sz_boxed_3851_, v_i_boxed_3852_, v_b_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v_as_3835_);
lean_dec(v_x_3833_);
lean_dec(v_a_3832_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object* v_a_3854_, lean_object* v_x_3855_, lean_object* v_c_3856_, lean_object* v_y_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_){
_start:
{
lean_object* v___x_3870_; 
v___x_3870_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3930_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3873_ = v___x_3870_;
v_isShared_3874_ = v_isSharedCheck_3930_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_a_3871_);
lean_dec(v___x_3870_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3930_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
uint8_t v___x_3875_; 
v___x_3875_ = lean_unbox(v_a_3871_);
lean_dec(v_a_3871_);
if (v___x_3875_ == 0)
{
lean_object* v___x_3876_; 
lean_del_object(v___x_3873_);
v___x_3876_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v___y_3879_; lean_object* v_diseqs_3912_; lean_object* v_size_3913_; lean_object* v___x_3914_; uint8_t v___x_3915_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref_known(v___x_3876_, 1);
v_diseqs_3912_ = lean_ctor_get(v_a_3877_, 34);
lean_inc_ref(v_diseqs_3912_);
lean_dec(v_a_3877_);
v_size_3913_ = lean_ctor_get(v_diseqs_3912_, 2);
v___x_3914_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_3915_ = lean_nat_dec_lt(v_y_3857_, v_size_3913_);
if (v___x_3915_ == 0)
{
lean_object* v___x_3916_; 
lean_dec_ref(v_diseqs_3912_);
v___x_3916_ = l_outOfBounds___redArg(v___x_3914_);
v___y_3879_ = v___x_3916_;
goto v___jp_3878_;
}
else
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3914_, v_diseqs_3912_, v_y_3857_);
lean_dec_ref(v_diseqs_3912_);
v___y_3879_ = v___x_3917_;
goto v___jp_3878_;
}
v___jp_3878_:
{
lean_object* v___x_3880_; lean_object* v_fst_3881_; lean_object* v_snd_3882_; lean_object* v___f_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3880_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3855_, v___y_3879_);
lean_dec_ref(v___y_3879_);
v_fst_3881_ = lean_ctor_get(v___x_3880_, 0);
lean_inc(v_fst_3881_);
v_snd_3882_ = lean_ctor_get(v___x_3880_, 1);
lean_inc(v_snd_3882_);
lean_dec_ref(v___x_3880_);
lean_inc(v_a_3858_);
v___f_3883_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3883_, 0, v_a_3858_);
lean_closure_set(v___f_3883_, 1, v_y_3857_);
lean_closure_set(v___f_3883_, 2, v_fst_3881_);
v___x_3884_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3885_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3884_, v___f_3883_, v_a_3859_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v___x_3886_; lean_object* v___x_3887_; size_t v_sz_3888_; size_t v___x_3889_; lean_object* v___x_3890_; 
lean_dec_ref_known(v___x_3885_, 1);
v___x_3886_ = lean_box(0);
v___x_3887_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_3888_ = lean_array_size(v_snd_3882_);
v___x_3889_ = ((size_t)0ULL);
v___x_3890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3854_, v_x_3855_, v_c_3856_, v_snd_3882_, v_sz_3888_, v___x_3889_, v___x_3887_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_);
lean_dec(v_snd_3882_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3903_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3893_ = v___x_3890_;
v_isShared_3894_ = v_isSharedCheck_3903_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3890_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3903_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v_fst_3895_; 
v_fst_3895_ = lean_ctor_get(v_a_3891_, 0);
lean_inc(v_fst_3895_);
lean_dec(v_a_3891_);
if (lean_obj_tag(v_fst_3895_) == 0)
{
lean_object* v___x_3897_; 
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 0, v___x_3886_);
v___x_3897_ = v___x_3893_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3886_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
else
{
lean_object* v_val_3899_; lean_object* v___x_3901_; 
v_val_3899_ = lean_ctor_get(v_fst_3895_, 0);
lean_inc(v_val_3899_);
lean_dec_ref_known(v_fst_3895_, 1);
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 0, v_val_3899_);
v___x_3901_ = v___x_3893_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_val_3899_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
else
{
lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3911_; 
v_a_3904_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3906_ = v___x_3890_;
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3890_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3909_; 
if (v_isShared_3907_ == 0)
{
v___x_3909_ = v___x_3906_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3904_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
else
{
lean_dec(v_snd_3882_);
lean_dec_ref(v_c_3856_);
return v___x_3885_;
}
}
}
else
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
lean_dec(v_y_3857_);
lean_dec_ref(v_c_3856_);
v_a_3918_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3876_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3876_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
else
{
lean_object* v___x_3926_; lean_object* v___x_3928_; 
lean_dec(v_y_3857_);
lean_dec_ref(v_c_3856_);
v___x_3926_ = lean_box(0);
if (v_isShared_3874_ == 0)
{
lean_ctor_set(v___x_3873_, 0, v___x_3926_);
v___x_3928_ = v___x_3873_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3926_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3938_; 
lean_dec(v_y_3857_);
lean_dec_ref(v_c_3856_);
v_a_3931_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3933_ = v___x_3870_;
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3870_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3936_; 
if (v_isShared_3934_ == 0)
{
v___x_3936_ = v___x_3933_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3931_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object* v_a_3939_, lean_object* v_x_3940_, lean_object* v_c_3941_, lean_object* v_y_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v_a_3939_, v_x_3940_, v_c_3941_, v_y_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_);
lean_dec(v_a_3953_);
lean_dec_ref(v_a_3952_);
lean_dec(v_a_3951_);
lean_dec_ref(v_a_3950_);
lean_dec(v_a_3949_);
lean_dec_ref(v_a_3948_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
lean_dec(v_a_3945_);
lean_dec(v_a_3944_);
lean_dec(v_a_3943_);
lean_dec(v_x_3940_);
lean_dec(v_a_3939_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object* v_a_3956_, lean_object* v_x_3957_, lean_object* v_c_3958_, lean_object* v_y_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_){
_start:
{
lean_object* v___x_3972_; 
lean_inc(v_y_3959_);
lean_inc_ref(v_c_3958_);
lean_inc(v_x_3957_);
lean_inc(v_a_3956_);
v___x_3972_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_3956_, v_x_3957_, v_c_3958_, v_y_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v___x_3973_; 
lean_dec_ref_known(v___x_3972_, 1);
lean_inc(v_y_3959_);
lean_inc_ref(v_c_3958_);
lean_inc(v_x_3957_);
lean_inc(v_a_3956_);
v___x_3973_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_3956_, v_x_3957_, v_c_3958_, v_y_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
lean_dec_ref_known(v___x_3973_, 1);
v___x_3974_ = lean_nat_to_int(v_a_3956_);
v___x_3975_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v___x_3974_, v_x_3957_, v_c_3958_, v_y_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
lean_dec(v_x_3957_);
lean_dec(v___x_3974_);
return v___x_3975_;
}
else
{
lean_dec(v_y_3959_);
lean_dec_ref(v_c_3958_);
lean_dec(v_x_3957_);
lean_dec(v_a_3956_);
return v___x_3973_;
}
}
else
{
lean_dec(v_y_3959_);
lean_dec_ref(v_c_3958_);
lean_dec(v_x_3957_);
lean_dec(v_a_3956_);
return v___x_3972_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object* v_a_3976_, lean_object* v_x_3977_, lean_object* v_c_3978_, lean_object* v_y_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_3976_, v_x_3977_, v_c_3978_, v_y_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_);
lean_dec(v_a_3990_);
lean_dec_ref(v_a_3989_);
lean_dec(v_a_3988_);
lean_dec_ref(v_a_3987_);
lean_dec(v_a_3986_);
lean_dec_ref(v_a_3985_);
lean_dec(v_a_3984_);
lean_dec_ref(v_a_3983_);
lean_dec(v_a_3982_);
lean_dec(v_a_3981_);
lean_dec(v_a_3980_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(lean_object* v_a_3993_, lean_object* v_x_3994_, lean_object* v_s_3995_){
_start:
{
lean_object* v_structs_3996_; lean_object* v_typeIdOf_3997_; lean_object* v_exprToStructId_3998_; lean_object* v_exprToStructIdEntries_3999_; lean_object* v_forbiddenNatModules_4000_; lean_object* v_natStructs_4001_; lean_object* v_natTypeIdOf_4002_; lean_object* v_exprToNatStructId_4003_; lean_object* v___x_4004_; uint8_t v___x_4005_; 
v_structs_3996_ = lean_ctor_get(v_s_3995_, 0);
v_typeIdOf_3997_ = lean_ctor_get(v_s_3995_, 1);
v_exprToStructId_3998_ = lean_ctor_get(v_s_3995_, 2);
v_exprToStructIdEntries_3999_ = lean_ctor_get(v_s_3995_, 3);
v_forbiddenNatModules_4000_ = lean_ctor_get(v_s_3995_, 4);
v_natStructs_4001_ = lean_ctor_get(v_s_3995_, 5);
v_natTypeIdOf_4002_ = lean_ctor_get(v_s_3995_, 6);
v_exprToNatStructId_4003_ = lean_ctor_get(v_s_3995_, 7);
v___x_4004_ = lean_array_get_size(v_structs_3996_);
v___x_4005_ = lean_nat_dec_lt(v_a_3993_, v___x_4004_);
if (v___x_4005_ == 0)
{
return v_s_3995_;
}
else
{
lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4068_; 
lean_inc_ref(v_exprToNatStructId_4003_);
lean_inc_ref(v_natTypeIdOf_4002_);
lean_inc_ref(v_natStructs_4001_);
lean_inc_ref(v_forbiddenNatModules_4000_);
lean_inc_ref(v_exprToStructIdEntries_3999_);
lean_inc_ref(v_exprToStructId_3998_);
lean_inc_ref(v_typeIdOf_3997_);
lean_inc_ref(v_structs_3996_);
v_isSharedCheck_4068_ = !lean_is_exclusive(v_s_3995_);
if (v_isSharedCheck_4068_ == 0)
{
lean_object* v_unused_4069_; lean_object* v_unused_4070_; lean_object* v_unused_4071_; lean_object* v_unused_4072_; lean_object* v_unused_4073_; lean_object* v_unused_4074_; lean_object* v_unused_4075_; lean_object* v_unused_4076_; 
v_unused_4069_ = lean_ctor_get(v_s_3995_, 7);
lean_dec(v_unused_4069_);
v_unused_4070_ = lean_ctor_get(v_s_3995_, 6);
lean_dec(v_unused_4070_);
v_unused_4071_ = lean_ctor_get(v_s_3995_, 5);
lean_dec(v_unused_4071_);
v_unused_4072_ = lean_ctor_get(v_s_3995_, 4);
lean_dec(v_unused_4072_);
v_unused_4073_ = lean_ctor_get(v_s_3995_, 3);
lean_dec(v_unused_4073_);
v_unused_4074_ = lean_ctor_get(v_s_3995_, 2);
lean_dec(v_unused_4074_);
v_unused_4075_ = lean_ctor_get(v_s_3995_, 1);
lean_dec(v_unused_4075_);
v_unused_4076_ = lean_ctor_get(v_s_3995_, 0);
lean_dec(v_unused_4076_);
v___x_4007_ = v_s_3995_;
v_isShared_4008_ = v_isSharedCheck_4068_;
goto v_resetjp_4006_;
}
else
{
lean_dec(v_s_3995_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4068_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v_v_4009_; lean_object* v_id_4010_; lean_object* v_ringId_x3f_4011_; lean_object* v_type_4012_; lean_object* v_u_4013_; lean_object* v_intModuleInst_4014_; lean_object* v_leInst_x3f_4015_; lean_object* v_ltInst_x3f_4016_; lean_object* v_lawfulOrderLTInst_x3f_4017_; lean_object* v_isPreorderInst_x3f_4018_; lean_object* v_orderedAddInst_x3f_4019_; lean_object* v_isLinearInst_x3f_4020_; lean_object* v_noNatDivInst_x3f_4021_; lean_object* v_ringInst_x3f_4022_; lean_object* v_commRingInst_x3f_4023_; lean_object* v_orderedRingInst_x3f_4024_; lean_object* v_fieldInst_x3f_4025_; lean_object* v_charInst_x3f_4026_; lean_object* v_zero_4027_; lean_object* v_ofNatZero_4028_; lean_object* v_one_x3f_4029_; lean_object* v_leFn_x3f_4030_; lean_object* v_ltFn_x3f_4031_; lean_object* v_addFn_4032_; lean_object* v_zsmulFn_4033_; lean_object* v_nsmulFn_4034_; lean_object* v_zsmulFn_x3f_4035_; lean_object* v_nsmulFn_x3f_4036_; lean_object* v_homomulFn_x3f_4037_; lean_object* v_subFn_4038_; lean_object* v_negFn_4039_; lean_object* v_vars_4040_; lean_object* v_varMap_4041_; lean_object* v_lowers_4042_; lean_object* v_uppers_4043_; lean_object* v_diseqs_4044_; lean_object* v_assignment_4045_; uint8_t v_caseSplits_4046_; lean_object* v_conflict_x3f_4047_; lean_object* v_diseqSplits_4048_; lean_object* v_elimEqs_4049_; lean_object* v_elimStack_4050_; lean_object* v_occurs_4051_; lean_object* v_ignored_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4067_; 
v_v_4009_ = lean_array_fget(v_structs_3996_, v_a_3993_);
v_id_4010_ = lean_ctor_get(v_v_4009_, 0);
v_ringId_x3f_4011_ = lean_ctor_get(v_v_4009_, 1);
v_type_4012_ = lean_ctor_get(v_v_4009_, 2);
v_u_4013_ = lean_ctor_get(v_v_4009_, 3);
v_intModuleInst_4014_ = lean_ctor_get(v_v_4009_, 4);
v_leInst_x3f_4015_ = lean_ctor_get(v_v_4009_, 5);
v_ltInst_x3f_4016_ = lean_ctor_get(v_v_4009_, 6);
v_lawfulOrderLTInst_x3f_4017_ = lean_ctor_get(v_v_4009_, 7);
v_isPreorderInst_x3f_4018_ = lean_ctor_get(v_v_4009_, 8);
v_orderedAddInst_x3f_4019_ = lean_ctor_get(v_v_4009_, 9);
v_isLinearInst_x3f_4020_ = lean_ctor_get(v_v_4009_, 10);
v_noNatDivInst_x3f_4021_ = lean_ctor_get(v_v_4009_, 11);
v_ringInst_x3f_4022_ = lean_ctor_get(v_v_4009_, 12);
v_commRingInst_x3f_4023_ = lean_ctor_get(v_v_4009_, 13);
v_orderedRingInst_x3f_4024_ = lean_ctor_get(v_v_4009_, 14);
v_fieldInst_x3f_4025_ = lean_ctor_get(v_v_4009_, 15);
v_charInst_x3f_4026_ = lean_ctor_get(v_v_4009_, 16);
v_zero_4027_ = lean_ctor_get(v_v_4009_, 17);
v_ofNatZero_4028_ = lean_ctor_get(v_v_4009_, 18);
v_one_x3f_4029_ = lean_ctor_get(v_v_4009_, 19);
v_leFn_x3f_4030_ = lean_ctor_get(v_v_4009_, 20);
v_ltFn_x3f_4031_ = lean_ctor_get(v_v_4009_, 21);
v_addFn_4032_ = lean_ctor_get(v_v_4009_, 22);
v_zsmulFn_4033_ = lean_ctor_get(v_v_4009_, 23);
v_nsmulFn_4034_ = lean_ctor_get(v_v_4009_, 24);
v_zsmulFn_x3f_4035_ = lean_ctor_get(v_v_4009_, 25);
v_nsmulFn_x3f_4036_ = lean_ctor_get(v_v_4009_, 26);
v_homomulFn_x3f_4037_ = lean_ctor_get(v_v_4009_, 27);
v_subFn_4038_ = lean_ctor_get(v_v_4009_, 28);
v_negFn_4039_ = lean_ctor_get(v_v_4009_, 29);
v_vars_4040_ = lean_ctor_get(v_v_4009_, 30);
v_varMap_4041_ = lean_ctor_get(v_v_4009_, 31);
v_lowers_4042_ = lean_ctor_get(v_v_4009_, 32);
v_uppers_4043_ = lean_ctor_get(v_v_4009_, 33);
v_diseqs_4044_ = lean_ctor_get(v_v_4009_, 34);
v_assignment_4045_ = lean_ctor_get(v_v_4009_, 35);
v_caseSplits_4046_ = lean_ctor_get_uint8(v_v_4009_, sizeof(void*)*42);
v_conflict_x3f_4047_ = lean_ctor_get(v_v_4009_, 36);
v_diseqSplits_4048_ = lean_ctor_get(v_v_4009_, 37);
v_elimEqs_4049_ = lean_ctor_get(v_v_4009_, 38);
v_elimStack_4050_ = lean_ctor_get(v_v_4009_, 39);
v_occurs_4051_ = lean_ctor_get(v_v_4009_, 40);
v_ignored_4052_ = lean_ctor_get(v_v_4009_, 41);
v_isSharedCheck_4067_ = !lean_is_exclusive(v_v_4009_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4054_ = v_v_4009_;
v_isShared_4055_ = v_isSharedCheck_4067_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_ignored_4052_);
lean_inc(v_occurs_4051_);
lean_inc(v_elimStack_4050_);
lean_inc(v_elimEqs_4049_);
lean_inc(v_diseqSplits_4048_);
lean_inc(v_conflict_x3f_4047_);
lean_inc(v_assignment_4045_);
lean_inc(v_diseqs_4044_);
lean_inc(v_uppers_4043_);
lean_inc(v_lowers_4042_);
lean_inc(v_varMap_4041_);
lean_inc(v_vars_4040_);
lean_inc(v_negFn_4039_);
lean_inc(v_subFn_4038_);
lean_inc(v_homomulFn_x3f_4037_);
lean_inc(v_nsmulFn_x3f_4036_);
lean_inc(v_zsmulFn_x3f_4035_);
lean_inc(v_nsmulFn_4034_);
lean_inc(v_zsmulFn_4033_);
lean_inc(v_addFn_4032_);
lean_inc(v_ltFn_x3f_4031_);
lean_inc(v_leFn_x3f_4030_);
lean_inc(v_one_x3f_4029_);
lean_inc(v_ofNatZero_4028_);
lean_inc(v_zero_4027_);
lean_inc(v_charInst_x3f_4026_);
lean_inc(v_fieldInst_x3f_4025_);
lean_inc(v_orderedRingInst_x3f_4024_);
lean_inc(v_commRingInst_x3f_4023_);
lean_inc(v_ringInst_x3f_4022_);
lean_inc(v_noNatDivInst_x3f_4021_);
lean_inc(v_isLinearInst_x3f_4020_);
lean_inc(v_orderedAddInst_x3f_4019_);
lean_inc(v_isPreorderInst_x3f_4018_);
lean_inc(v_lawfulOrderLTInst_x3f_4017_);
lean_inc(v_ltInst_x3f_4016_);
lean_inc(v_leInst_x3f_4015_);
lean_inc(v_intModuleInst_4014_);
lean_inc(v_u_4013_);
lean_inc(v_type_4012_);
lean_inc(v_ringId_x3f_4011_);
lean_inc(v_id_4010_);
lean_dec(v_v_4009_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4067_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4056_; lean_object* v_xs_x27_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4061_; 
v___x_4056_ = lean_box(0);
v_xs_x27_4057_ = lean_array_fset(v_structs_3996_, v_a_3993_, v___x_4056_);
v___x_4058_ = lean_box(1);
v___x_4059_ = l_Lean_PersistentArray_set___redArg(v_occurs_4051_, v_x_3994_, v___x_4058_);
if (v_isShared_4055_ == 0)
{
lean_ctor_set(v___x_4054_, 40, v___x_4059_);
v___x_4061_ = v___x_4054_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_id_4010_);
lean_ctor_set(v_reuseFailAlloc_4066_, 1, v_ringId_x3f_4011_);
lean_ctor_set(v_reuseFailAlloc_4066_, 2, v_type_4012_);
lean_ctor_set(v_reuseFailAlloc_4066_, 3, v_u_4013_);
lean_ctor_set(v_reuseFailAlloc_4066_, 4, v_intModuleInst_4014_);
lean_ctor_set(v_reuseFailAlloc_4066_, 5, v_leInst_x3f_4015_);
lean_ctor_set(v_reuseFailAlloc_4066_, 6, v_ltInst_x3f_4016_);
lean_ctor_set(v_reuseFailAlloc_4066_, 7, v_lawfulOrderLTInst_x3f_4017_);
lean_ctor_set(v_reuseFailAlloc_4066_, 8, v_isPreorderInst_x3f_4018_);
lean_ctor_set(v_reuseFailAlloc_4066_, 9, v_orderedAddInst_x3f_4019_);
lean_ctor_set(v_reuseFailAlloc_4066_, 10, v_isLinearInst_x3f_4020_);
lean_ctor_set(v_reuseFailAlloc_4066_, 11, v_noNatDivInst_x3f_4021_);
lean_ctor_set(v_reuseFailAlloc_4066_, 12, v_ringInst_x3f_4022_);
lean_ctor_set(v_reuseFailAlloc_4066_, 13, v_commRingInst_x3f_4023_);
lean_ctor_set(v_reuseFailAlloc_4066_, 14, v_orderedRingInst_x3f_4024_);
lean_ctor_set(v_reuseFailAlloc_4066_, 15, v_fieldInst_x3f_4025_);
lean_ctor_set(v_reuseFailAlloc_4066_, 16, v_charInst_x3f_4026_);
lean_ctor_set(v_reuseFailAlloc_4066_, 17, v_zero_4027_);
lean_ctor_set(v_reuseFailAlloc_4066_, 18, v_ofNatZero_4028_);
lean_ctor_set(v_reuseFailAlloc_4066_, 19, v_one_x3f_4029_);
lean_ctor_set(v_reuseFailAlloc_4066_, 20, v_leFn_x3f_4030_);
lean_ctor_set(v_reuseFailAlloc_4066_, 21, v_ltFn_x3f_4031_);
lean_ctor_set(v_reuseFailAlloc_4066_, 22, v_addFn_4032_);
lean_ctor_set(v_reuseFailAlloc_4066_, 23, v_zsmulFn_4033_);
lean_ctor_set(v_reuseFailAlloc_4066_, 24, v_nsmulFn_4034_);
lean_ctor_set(v_reuseFailAlloc_4066_, 25, v_zsmulFn_x3f_4035_);
lean_ctor_set(v_reuseFailAlloc_4066_, 26, v_nsmulFn_x3f_4036_);
lean_ctor_set(v_reuseFailAlloc_4066_, 27, v_homomulFn_x3f_4037_);
lean_ctor_set(v_reuseFailAlloc_4066_, 28, v_subFn_4038_);
lean_ctor_set(v_reuseFailAlloc_4066_, 29, v_negFn_4039_);
lean_ctor_set(v_reuseFailAlloc_4066_, 30, v_vars_4040_);
lean_ctor_set(v_reuseFailAlloc_4066_, 31, v_varMap_4041_);
lean_ctor_set(v_reuseFailAlloc_4066_, 32, v_lowers_4042_);
lean_ctor_set(v_reuseFailAlloc_4066_, 33, v_uppers_4043_);
lean_ctor_set(v_reuseFailAlloc_4066_, 34, v_diseqs_4044_);
lean_ctor_set(v_reuseFailAlloc_4066_, 35, v_assignment_4045_);
lean_ctor_set(v_reuseFailAlloc_4066_, 36, v_conflict_x3f_4047_);
lean_ctor_set(v_reuseFailAlloc_4066_, 37, v_diseqSplits_4048_);
lean_ctor_set(v_reuseFailAlloc_4066_, 38, v_elimEqs_4049_);
lean_ctor_set(v_reuseFailAlloc_4066_, 39, v_elimStack_4050_);
lean_ctor_set(v_reuseFailAlloc_4066_, 40, v___x_4059_);
lean_ctor_set(v_reuseFailAlloc_4066_, 41, v_ignored_4052_);
lean_ctor_set_uint8(v_reuseFailAlloc_4066_, sizeof(void*)*42, v_caseSplits_4046_);
v___x_4061_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
lean_object* v___x_4062_; lean_object* v___x_4064_; 
v___x_4062_ = lean_array_fset(v_xs_x27_4057_, v_a_3993_, v___x_4061_);
if (v_isShared_4008_ == 0)
{
lean_ctor_set(v___x_4007_, 0, v___x_4062_);
v___x_4064_ = v___x_4007_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___x_4062_);
lean_ctor_set(v_reuseFailAlloc_4065_, 1, v_typeIdOf_3997_);
lean_ctor_set(v_reuseFailAlloc_4065_, 2, v_exprToStructId_3998_);
lean_ctor_set(v_reuseFailAlloc_4065_, 3, v_exprToStructIdEntries_3999_);
lean_ctor_set(v_reuseFailAlloc_4065_, 4, v_forbiddenNatModules_4000_);
lean_ctor_set(v_reuseFailAlloc_4065_, 5, v_natStructs_4001_);
lean_ctor_set(v_reuseFailAlloc_4065_, 6, v_natTypeIdOf_4002_);
lean_ctor_set(v_reuseFailAlloc_4065_, 7, v_exprToNatStructId_4003_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed(lean_object* v_a_4077_, lean_object* v_x_4078_, lean_object* v_s_4079_){
_start:
{
lean_object* v_res_4080_; 
v_res_4080_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(v_a_4077_, v_x_4078_, v_s_4079_);
lean_dec(v_x_4078_);
lean_dec(v_a_4077_);
return v_res_4080_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object* v_a_4081_, lean_object* v_x_4082_, lean_object* v_c_4083_, lean_object* v_init_4084_, lean_object* v_x_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
if (lean_obj_tag(v_x_4085_) == 0)
{
lean_object* v_k_4098_; lean_object* v_l_4099_; lean_object* v_r_4100_; lean_object* v___x_4101_; 
v_k_4098_ = lean_ctor_get(v_x_4085_, 1);
lean_inc(v_k_4098_);
v_l_4099_ = lean_ctor_get(v_x_4085_, 3);
lean_inc(v_l_4099_);
v_r_4100_ = lean_ctor_get(v_x_4085_, 4);
lean_inc(v_r_4100_);
lean_dec_ref_known(v_x_4085_, 5);
lean_inc_ref(v_c_4083_);
lean_inc(v_x_4082_);
lean_inc(v_a_4081_);
v___x_4101_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4081_, v_x_4082_, v_c_4083_, v_init_4084_, v_l_4099_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v___x_4102_; 
lean_dec_ref_known(v___x_4101_, 1);
lean_inc_ref(v_c_4083_);
lean_inc(v_x_4082_);
lean_inc(v_a_4081_);
v___x_4102_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4081_, v_x_4082_, v_c_4083_, v_k_4098_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v___x_4103_; 
lean_dec_ref_known(v___x_4102_, 1);
v___x_4103_ = lean_box(0);
v_init_4084_ = v___x_4103_;
v_x_4085_ = v_r_4100_;
goto _start;
}
else
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4112_; 
lean_dec(v_r_4100_);
lean_dec_ref(v_c_4083_);
lean_dec(v_x_4082_);
lean_dec(v_a_4081_);
v_a_4105_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4107_ = v___x_4102_;
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v___x_4102_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4110_; 
if (v_isShared_4108_ == 0)
{
v___x_4110_ = v___x_4107_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4105_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
else
{
lean_dec(v_r_4100_);
lean_dec(v_k_4098_);
lean_dec_ref(v_c_4083_);
lean_dec(v_x_4082_);
lean_dec(v_a_4081_);
return v___x_4101_;
}
}
else
{
lean_object* v___x_4113_; lean_object* v___x_4114_; 
lean_dec_ref(v_c_4083_);
lean_dec(v_x_4082_);
lean_dec(v_a_4081_);
v___x_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4113_, 0, v_init_4084_);
v___x_4114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4113_);
return v___x_4114_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object** _args){
lean_object* v_a_4115_ = _args[0];
lean_object* v_x_4116_ = _args[1];
lean_object* v_c_4117_ = _args[2];
lean_object* v_init_4118_ = _args[3];
lean_object* v_x_4119_ = _args[4];
lean_object* v___y_4120_ = _args[5];
lean_object* v___y_4121_ = _args[6];
lean_object* v___y_4122_ = _args[7];
lean_object* v___y_4123_ = _args[8];
lean_object* v___y_4124_ = _args[9];
lean_object* v___y_4125_ = _args[10];
lean_object* v___y_4126_ = _args[11];
lean_object* v___y_4127_ = _args[12];
lean_object* v___y_4128_ = _args[13];
lean_object* v___y_4129_ = _args[14];
lean_object* v___y_4130_ = _args[15];
lean_object* v___y_4131_ = _args[16];
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4115_, v_x_4116_, v_c_4117_, v_init_4118_, v_x_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec(v___y_4120_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object* v_a_4133_, lean_object* v_x_4134_, lean_object* v_c_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_){
_start:
{
lean_object* v___x_4148_; 
v___x_4148_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; lean_object* v_occurs_4150_; lean_object* v_size_4151_; lean_object* v___f_4152_; lean_object* v___y_4154_; lean_object* v___x_4176_; uint8_t v___x_4177_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_a_4149_);
lean_dec_ref_known(v___x_4148_, 1);
v_occurs_4150_ = lean_ctor_get(v_a_4149_, 40);
lean_inc_ref(v_occurs_4150_);
lean_dec(v_a_4149_);
v_size_4151_ = lean_ctor_get(v_occurs_4150_, 2);
lean_inc(v_x_4134_);
lean_inc(v_a_4136_);
v___f_4152_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4152_, 0, v_a_4136_);
lean_closure_set(v___f_4152_, 1, v_x_4134_);
v___x_4176_ = lean_box(1);
v___x_4177_ = lean_nat_dec_lt(v_x_4134_, v_size_4151_);
if (v___x_4177_ == 0)
{
lean_object* v___x_4178_; 
lean_dec_ref(v_occurs_4150_);
v___x_4178_ = l_outOfBounds___redArg(v___x_4176_);
v___y_4154_ = v___x_4178_;
goto v___jp_4153_;
}
else
{
lean_object* v___x_4179_; 
v___x_4179_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4176_, v_occurs_4150_, v_x_4134_);
lean_dec_ref(v_occurs_4150_);
v___y_4154_ = v___x_4179_;
goto v___jp_4153_;
}
v___jp_4153_:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4155_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4156_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4155_, v___f_4152_, v_a_4137_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v___x_4157_; 
lean_dec_ref_known(v___x_4156_, 1);
lean_inc_ref(v_c_4135_);
lean_inc_n(v_x_4134_, 2);
lean_inc(v_a_4133_);
v___x_4157_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4133_, v_x_4134_, v_c_4135_, v_x_4134_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v___x_4158_; lean_object* v___x_4159_; 
lean_dec_ref_known(v___x_4157_, 1);
v___x_4158_ = lean_box(0);
v___x_4159_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4133_, v_x_4134_, v_c_4135_, v___x_4158_, v___y_4154_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4166_; 
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4166_ == 0)
{
lean_object* v_unused_4167_; 
v_unused_4167_ = lean_ctor_get(v___x_4159_, 0);
lean_dec(v_unused_4167_);
v___x_4161_ = v___x_4159_;
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
else
{
lean_dec(v___x_4159_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4164_; 
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 0, v___x_4158_);
v___x_4164_ = v___x_4161_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4158_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
v_a_4168_ = lean_ctor_get(v___x_4159_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4159_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4159_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
else
{
lean_dec(v___y_4154_);
lean_dec_ref(v_c_4135_);
lean_dec(v_x_4134_);
lean_dec(v_a_4133_);
return v___x_4157_;
}
}
else
{
lean_dec(v___y_4154_);
lean_dec_ref(v_c_4135_);
lean_dec(v_x_4134_);
lean_dec(v_a_4133_);
return v___x_4156_;
}
}
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4187_; 
lean_dec_ref(v_c_4135_);
lean_dec(v_x_4134_);
lean_dec(v_a_4133_);
v_a_4180_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4182_ = v___x_4148_;
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4148_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4185_; 
if (v_isShared_4183_ == 0)
{
v___x_4185_ = v___x_4182_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_a_4180_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___boxed(lean_object* v_a_4188_, lean_object* v_x_4189_, lean_object* v_c_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_){
_start:
{
lean_object* v_res_4203_; 
v_res_4203_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v_a_4188_, v_x_4189_, v_c_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_);
lean_dec(v_a_4201_);
lean_dec_ref(v_a_4200_);
lean_dec(v_a_4199_);
lean_dec_ref(v_a_4198_);
lean_dec(v_a_4197_);
lean_dec_ref(v_a_4196_);
lean_dec(v_a_4195_);
lean_dec_ref(v_a_4194_);
lean_dec(v_a_4193_);
lean_dec(v_a_4192_);
lean_dec(v_a_4191_);
return v_res_4203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(lean_object* v_c_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_){
_start:
{
lean_object* v_p_4221_; 
v_p_4221_ = lean_ctor_get(v_c_4204_, 0);
if (lean_obj_tag(v_p_4221_) == 1)
{
lean_object* v_k_4222_; lean_object* v_v_4223_; lean_object* v_p_4224_; lean_object* v_y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___x_4275_; lean_object* v___x_4276_; uint8_t v___x_4277_; 
v_k_4222_ = lean_ctor_get(v_p_4221_, 0);
v_v_4223_ = lean_ctor_get(v_p_4221_, 1);
v_p_4224_ = lean_ctor_get(v_p_4221_, 2);
v___x_4275_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_4276_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4277_ = lean_int_dec_eq(v_k_4222_, v___x_4276_);
if (v___x_4277_ == 0)
{
uint8_t v___x_4278_; 
v___x_4278_ = lean_int_dec_eq(v_k_4222_, v___x_4275_);
if (v___x_4278_ == 0)
{
goto v___jp_4217_;
}
else
{
if (lean_obj_tag(v_p_4224_) == 1)
{
lean_object* v_k_4279_; lean_object* v_v_4280_; lean_object* v_p_4281_; uint8_t v___x_4282_; 
v_k_4279_ = lean_ctor_get(v_p_4224_, 0);
v_v_4280_ = lean_ctor_get(v_p_4224_, 1);
v_p_4281_ = lean_ctor_get(v_p_4224_, 2);
v___x_4282_ = lean_int_dec_eq(v_k_4279_, v___x_4276_);
if (v___x_4282_ == 0)
{
goto v___jp_4217_;
}
else
{
if (lean_obj_tag(v_p_4281_) == 0)
{
v_y_4226_ = v_v_4280_;
v___y_4227_ = v_a_4205_;
v___y_4228_ = v_a_4206_;
v___y_4229_ = v_a_4207_;
v___y_4230_ = v_a_4208_;
v___y_4231_ = v_a_4209_;
v___y_4232_ = v_a_4210_;
v___y_4233_ = v_a_4211_;
v___y_4234_ = v_a_4212_;
v___y_4235_ = v_a_4213_;
v___y_4236_ = v_a_4214_;
v___y_4237_ = v_a_4215_;
goto v___jp_4225_;
}
else
{
goto v___jp_4217_;
}
}
}
else
{
goto v___jp_4217_;
}
}
}
else
{
if (lean_obj_tag(v_p_4224_) == 1)
{
lean_object* v_k_4283_; lean_object* v_v_4284_; lean_object* v_p_4285_; uint8_t v___x_4286_; 
v_k_4283_ = lean_ctor_get(v_p_4224_, 0);
v_v_4284_ = lean_ctor_get(v_p_4224_, 1);
v_p_4285_ = lean_ctor_get(v_p_4224_, 2);
v___x_4286_ = lean_int_dec_eq(v_k_4283_, v___x_4275_);
if (v___x_4286_ == 0)
{
goto v___jp_4217_;
}
else
{
if (lean_obj_tag(v_p_4285_) == 0)
{
v_y_4226_ = v_v_4284_;
v___y_4227_ = v_a_4205_;
v___y_4228_ = v_a_4206_;
v___y_4229_ = v_a_4207_;
v___y_4230_ = v_a_4208_;
v___y_4231_ = v_a_4209_;
v___y_4232_ = v_a_4210_;
v___y_4233_ = v_a_4211_;
v___y_4234_ = v_a_4212_;
v___y_4235_ = v_a_4213_;
v___y_4236_ = v_a_4214_;
v___y_4237_ = v_a_4215_;
goto v___jp_4225_;
}
else
{
goto v___jp_4217_;
}
}
}
else
{
goto v___jp_4217_;
}
}
v___jp_4225_:
{
lean_object* v___x_4238_; 
v___x_4238_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_v_4223_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
if (lean_obj_tag(v___x_4238_) == 0)
{
lean_object* v_a_4239_; lean_object* v___x_4240_; 
v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
lean_inc(v_a_4239_);
lean_dec_ref_known(v___x_4238_, 1);
v___x_4240_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_a_4241_; lean_object* v___x_4242_; 
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
lean_inc(v_a_4241_);
lean_dec_ref_known(v___x_4240_, 1);
v___x_4242_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_4239_, v_a_4241_, v___y_4228_);
lean_dec(v_a_4241_);
lean_dec(v_a_4239_);
if (lean_obj_tag(v___x_4242_) == 0)
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4258_; 
v_a_4243_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4245_ = v___x_4242_;
v_isShared_4246_ = v_isSharedCheck_4258_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4242_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4258_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
uint8_t v___x_4247_; 
v___x_4247_ = lean_unbox(v_a_4243_);
lean_dec(v_a_4243_);
if (v___x_4247_ == 0)
{
uint8_t v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4251_; 
v___x_4248_ = 1;
v___x_4249_ = lean_box(v___x_4248_);
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 0, v___x_4249_);
v___x_4251_ = v___x_4245_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4249_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
else
{
uint8_t v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4256_; 
v___x_4253_ = 0;
v___x_4254_ = lean_box(v___x_4253_);
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 0, v___x_4254_);
v___x_4256_ = v___x_4245_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v___x_4254_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
}
else
{
return v___x_4242_;
}
}
else
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4266_; 
lean_dec(v_a_4239_);
v_a_4259_ = lean_ctor_get(v___x_4240_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4261_ = v___x_4240_;
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v___x_4240_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
if (v_isShared_4262_ == 0)
{
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
else
{
lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4274_; 
v_a_4267_ = lean_ctor_get(v___x_4238_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4238_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4269_ = v___x_4238_;
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_dec(v___x_4238_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4272_; 
if (v_isShared_4270_ == 0)
{
v___x_4272_ = v___x_4269_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_a_4267_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
}
}
else
{
goto v___jp_4217_;
}
v___jp_4217_:
{
uint8_t v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4218_ = 0;
v___x_4219_ = lean_box(v___x_4218_);
v___x_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4219_);
return v___x_4220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq___boxed(lean_object* v_c_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v_c_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
lean_dec(v_a_4298_);
lean_dec_ref(v_a_4297_);
lean_dec(v_a_4296_);
lean_dec_ref(v_a_4295_);
lean_dec(v_a_4294_);
lean_dec_ref(v_a_4293_);
lean_dec(v_a_4292_);
lean_dec_ref(v_a_4291_);
lean_dec(v_a_4290_);
lean_dec(v_a_4289_);
lean_dec(v_a_4288_);
lean_dec_ref(v_c_4287_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(lean_object* v_c_4301_){
_start:
{
lean_object* v_p_4303_; 
v_p_4303_ = lean_ctor_get(v_c_4301_, 0);
if (lean_obj_tag(v_p_4303_) == 1)
{
lean_object* v_k_4304_; lean_object* v___x_4305_; uint8_t v___x_4306_; 
v_k_4304_ = lean_ctor_get(v_p_4303_, 0);
v___x_4305_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_4306_ = lean_int_dec_lt(v_k_4304_, v___x_4305_);
if (v___x_4306_ == 0)
{
lean_object* v___x_4307_; 
v___x_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4307_, 0, v_c_4301_);
return v___x_4307_;
}
else
{
lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; 
v___x_4308_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_4303_);
v___x_4309_ = l_Lean_Grind_Linarith_Poly_mul(v_p_4303_, v___x_4308_);
v___x_4310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4310_, 0, v_c_4301_);
v___x_4311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4309_);
lean_ctor_set(v___x_4311_, 1, v___x_4310_);
v___x_4312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4312_, 0, v___x_4311_);
return v___x_4312_;
}
}
else
{
lean_object* v___x_4313_; 
v___x_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4313_, 0, v_c_4301_);
return v___x_4313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg___boxed(lean_object* v_c_4314_, lean_object* v_a_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4314_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(lean_object* v_c_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_){
_start:
{
lean_object* v___x_4330_; 
v___x_4330_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4317_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___boxed(lean_object* v_c_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(v_c_4331_, v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_);
lean_dec(v_a_4342_);
lean_dec_ref(v_a_4341_);
lean_dec(v_a_4340_);
lean_dec_ref(v_a_4339_);
lean_dec(v_a_4338_);
lean_dec_ref(v_a_4337_);
lean_dec(v_a_4336_);
lean_dec_ref(v_a_4335_);
lean_dec(v_a_4334_);
lean_dec(v_a_4333_);
lean_dec(v_a_4332_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(lean_object* v___y_4345_, lean_object* v_snd_4346_, lean_object* v_fst_4347_, lean_object* v_s_4348_){
_start:
{
lean_object* v_structs_4349_; lean_object* v_typeIdOf_4350_; lean_object* v_exprToStructId_4351_; lean_object* v_exprToStructIdEntries_4352_; lean_object* v_forbiddenNatModules_4353_; lean_object* v_natStructs_4354_; lean_object* v_natTypeIdOf_4355_; lean_object* v_exprToNatStructId_4356_; lean_object* v___x_4357_; uint8_t v___x_4358_; 
v_structs_4349_ = lean_ctor_get(v_s_4348_, 0);
v_typeIdOf_4350_ = lean_ctor_get(v_s_4348_, 1);
v_exprToStructId_4351_ = lean_ctor_get(v_s_4348_, 2);
v_exprToStructIdEntries_4352_ = lean_ctor_get(v_s_4348_, 3);
v_forbiddenNatModules_4353_ = lean_ctor_get(v_s_4348_, 4);
v_natStructs_4354_ = lean_ctor_get(v_s_4348_, 5);
v_natTypeIdOf_4355_ = lean_ctor_get(v_s_4348_, 6);
v_exprToNatStructId_4356_ = lean_ctor_get(v_s_4348_, 7);
v___x_4357_ = lean_array_get_size(v_structs_4349_);
v___x_4358_ = lean_nat_dec_lt(v___y_4345_, v___x_4357_);
if (v___x_4358_ == 0)
{
lean_dec(v_fst_4347_);
lean_dec_ref(v_snd_4346_);
return v_s_4348_;
}
else
{
lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4422_; 
lean_inc_ref(v_exprToNatStructId_4356_);
lean_inc_ref(v_natTypeIdOf_4355_);
lean_inc_ref(v_natStructs_4354_);
lean_inc_ref(v_forbiddenNatModules_4353_);
lean_inc_ref(v_exprToStructIdEntries_4352_);
lean_inc_ref(v_exprToStructId_4351_);
lean_inc_ref(v_typeIdOf_4350_);
lean_inc_ref(v_structs_4349_);
v_isSharedCheck_4422_ = !lean_is_exclusive(v_s_4348_);
if (v_isSharedCheck_4422_ == 0)
{
lean_object* v_unused_4423_; lean_object* v_unused_4424_; lean_object* v_unused_4425_; lean_object* v_unused_4426_; lean_object* v_unused_4427_; lean_object* v_unused_4428_; lean_object* v_unused_4429_; lean_object* v_unused_4430_; 
v_unused_4423_ = lean_ctor_get(v_s_4348_, 7);
lean_dec(v_unused_4423_);
v_unused_4424_ = lean_ctor_get(v_s_4348_, 6);
lean_dec(v_unused_4424_);
v_unused_4425_ = lean_ctor_get(v_s_4348_, 5);
lean_dec(v_unused_4425_);
v_unused_4426_ = lean_ctor_get(v_s_4348_, 4);
lean_dec(v_unused_4426_);
v_unused_4427_ = lean_ctor_get(v_s_4348_, 3);
lean_dec(v_unused_4427_);
v_unused_4428_ = lean_ctor_get(v_s_4348_, 2);
lean_dec(v_unused_4428_);
v_unused_4429_ = lean_ctor_get(v_s_4348_, 1);
lean_dec(v_unused_4429_);
v_unused_4430_ = lean_ctor_get(v_s_4348_, 0);
lean_dec(v_unused_4430_);
v___x_4360_ = v_s_4348_;
v_isShared_4361_ = v_isSharedCheck_4422_;
goto v_resetjp_4359_;
}
else
{
lean_dec(v_s_4348_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4422_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v_v_4362_; lean_object* v_id_4363_; lean_object* v_ringId_x3f_4364_; lean_object* v_type_4365_; lean_object* v_u_4366_; lean_object* v_intModuleInst_4367_; lean_object* v_leInst_x3f_4368_; lean_object* v_ltInst_x3f_4369_; lean_object* v_lawfulOrderLTInst_x3f_4370_; lean_object* v_isPreorderInst_x3f_4371_; lean_object* v_orderedAddInst_x3f_4372_; lean_object* v_isLinearInst_x3f_4373_; lean_object* v_noNatDivInst_x3f_4374_; lean_object* v_ringInst_x3f_4375_; lean_object* v_commRingInst_x3f_4376_; lean_object* v_orderedRingInst_x3f_4377_; lean_object* v_fieldInst_x3f_4378_; lean_object* v_charInst_x3f_4379_; lean_object* v_zero_4380_; lean_object* v_ofNatZero_4381_; lean_object* v_one_x3f_4382_; lean_object* v_leFn_x3f_4383_; lean_object* v_ltFn_x3f_4384_; lean_object* v_addFn_4385_; lean_object* v_zsmulFn_4386_; lean_object* v_nsmulFn_4387_; lean_object* v_zsmulFn_x3f_4388_; lean_object* v_nsmulFn_x3f_4389_; lean_object* v_homomulFn_x3f_4390_; lean_object* v_subFn_4391_; lean_object* v_negFn_4392_; lean_object* v_vars_4393_; lean_object* v_varMap_4394_; lean_object* v_lowers_4395_; lean_object* v_uppers_4396_; lean_object* v_diseqs_4397_; lean_object* v_assignment_4398_; uint8_t v_caseSplits_4399_; lean_object* v_conflict_x3f_4400_; lean_object* v_diseqSplits_4401_; lean_object* v_elimEqs_4402_; lean_object* v_elimStack_4403_; lean_object* v_occurs_4404_; lean_object* v_ignored_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4421_; 
v_v_4362_ = lean_array_fget(v_structs_4349_, v___y_4345_);
v_id_4363_ = lean_ctor_get(v_v_4362_, 0);
v_ringId_x3f_4364_ = lean_ctor_get(v_v_4362_, 1);
v_type_4365_ = lean_ctor_get(v_v_4362_, 2);
v_u_4366_ = lean_ctor_get(v_v_4362_, 3);
v_intModuleInst_4367_ = lean_ctor_get(v_v_4362_, 4);
v_leInst_x3f_4368_ = lean_ctor_get(v_v_4362_, 5);
v_ltInst_x3f_4369_ = lean_ctor_get(v_v_4362_, 6);
v_lawfulOrderLTInst_x3f_4370_ = lean_ctor_get(v_v_4362_, 7);
v_isPreorderInst_x3f_4371_ = lean_ctor_get(v_v_4362_, 8);
v_orderedAddInst_x3f_4372_ = lean_ctor_get(v_v_4362_, 9);
v_isLinearInst_x3f_4373_ = lean_ctor_get(v_v_4362_, 10);
v_noNatDivInst_x3f_4374_ = lean_ctor_get(v_v_4362_, 11);
v_ringInst_x3f_4375_ = lean_ctor_get(v_v_4362_, 12);
v_commRingInst_x3f_4376_ = lean_ctor_get(v_v_4362_, 13);
v_orderedRingInst_x3f_4377_ = lean_ctor_get(v_v_4362_, 14);
v_fieldInst_x3f_4378_ = lean_ctor_get(v_v_4362_, 15);
v_charInst_x3f_4379_ = lean_ctor_get(v_v_4362_, 16);
v_zero_4380_ = lean_ctor_get(v_v_4362_, 17);
v_ofNatZero_4381_ = lean_ctor_get(v_v_4362_, 18);
v_one_x3f_4382_ = lean_ctor_get(v_v_4362_, 19);
v_leFn_x3f_4383_ = lean_ctor_get(v_v_4362_, 20);
v_ltFn_x3f_4384_ = lean_ctor_get(v_v_4362_, 21);
v_addFn_4385_ = lean_ctor_get(v_v_4362_, 22);
v_zsmulFn_4386_ = lean_ctor_get(v_v_4362_, 23);
v_nsmulFn_4387_ = lean_ctor_get(v_v_4362_, 24);
v_zsmulFn_x3f_4388_ = lean_ctor_get(v_v_4362_, 25);
v_nsmulFn_x3f_4389_ = lean_ctor_get(v_v_4362_, 26);
v_homomulFn_x3f_4390_ = lean_ctor_get(v_v_4362_, 27);
v_subFn_4391_ = lean_ctor_get(v_v_4362_, 28);
v_negFn_4392_ = lean_ctor_get(v_v_4362_, 29);
v_vars_4393_ = lean_ctor_get(v_v_4362_, 30);
v_varMap_4394_ = lean_ctor_get(v_v_4362_, 31);
v_lowers_4395_ = lean_ctor_get(v_v_4362_, 32);
v_uppers_4396_ = lean_ctor_get(v_v_4362_, 33);
v_diseqs_4397_ = lean_ctor_get(v_v_4362_, 34);
v_assignment_4398_ = lean_ctor_get(v_v_4362_, 35);
v_caseSplits_4399_ = lean_ctor_get_uint8(v_v_4362_, sizeof(void*)*42);
v_conflict_x3f_4400_ = lean_ctor_get(v_v_4362_, 36);
v_diseqSplits_4401_ = lean_ctor_get(v_v_4362_, 37);
v_elimEqs_4402_ = lean_ctor_get(v_v_4362_, 38);
v_elimStack_4403_ = lean_ctor_get(v_v_4362_, 39);
v_occurs_4404_ = lean_ctor_get(v_v_4362_, 40);
v_ignored_4405_ = lean_ctor_get(v_v_4362_, 41);
v_isSharedCheck_4421_ = !lean_is_exclusive(v_v_4362_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4407_ = v_v_4362_;
v_isShared_4408_ = v_isSharedCheck_4421_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_ignored_4405_);
lean_inc(v_occurs_4404_);
lean_inc(v_elimStack_4403_);
lean_inc(v_elimEqs_4402_);
lean_inc(v_diseqSplits_4401_);
lean_inc(v_conflict_x3f_4400_);
lean_inc(v_assignment_4398_);
lean_inc(v_diseqs_4397_);
lean_inc(v_uppers_4396_);
lean_inc(v_lowers_4395_);
lean_inc(v_varMap_4394_);
lean_inc(v_vars_4393_);
lean_inc(v_negFn_4392_);
lean_inc(v_subFn_4391_);
lean_inc(v_homomulFn_x3f_4390_);
lean_inc(v_nsmulFn_x3f_4389_);
lean_inc(v_zsmulFn_x3f_4388_);
lean_inc(v_nsmulFn_4387_);
lean_inc(v_zsmulFn_4386_);
lean_inc(v_addFn_4385_);
lean_inc(v_ltFn_x3f_4384_);
lean_inc(v_leFn_x3f_4383_);
lean_inc(v_one_x3f_4382_);
lean_inc(v_ofNatZero_4381_);
lean_inc(v_zero_4380_);
lean_inc(v_charInst_x3f_4379_);
lean_inc(v_fieldInst_x3f_4378_);
lean_inc(v_orderedRingInst_x3f_4377_);
lean_inc(v_commRingInst_x3f_4376_);
lean_inc(v_ringInst_x3f_4375_);
lean_inc(v_noNatDivInst_x3f_4374_);
lean_inc(v_isLinearInst_x3f_4373_);
lean_inc(v_orderedAddInst_x3f_4372_);
lean_inc(v_isPreorderInst_x3f_4371_);
lean_inc(v_lawfulOrderLTInst_x3f_4370_);
lean_inc(v_ltInst_x3f_4369_);
lean_inc(v_leInst_x3f_4368_);
lean_inc(v_intModuleInst_4367_);
lean_inc(v_u_4366_);
lean_inc(v_type_4365_);
lean_inc(v_ringId_x3f_4364_);
lean_inc(v_id_4363_);
lean_dec(v_v_4362_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4421_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4409_; lean_object* v_xs_x27_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4415_; 
v___x_4409_ = lean_box(0);
v_xs_x27_4410_ = lean_array_fset(v_structs_4349_, v___y_4345_, v___x_4409_);
v___x_4411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4411_, 0, v_snd_4346_);
v___x_4412_ = l_Lean_PersistentArray_set___redArg(v_elimEqs_4402_, v_fst_4347_, v___x_4411_);
v___x_4413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4413_, 0, v_fst_4347_);
lean_ctor_set(v___x_4413_, 1, v_elimStack_4403_);
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 39, v___x_4413_);
lean_ctor_set(v___x_4407_, 38, v___x_4412_);
v___x_4415_ = v___x_4407_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_id_4363_);
lean_ctor_set(v_reuseFailAlloc_4420_, 1, v_ringId_x3f_4364_);
lean_ctor_set(v_reuseFailAlloc_4420_, 2, v_type_4365_);
lean_ctor_set(v_reuseFailAlloc_4420_, 3, v_u_4366_);
lean_ctor_set(v_reuseFailAlloc_4420_, 4, v_intModuleInst_4367_);
lean_ctor_set(v_reuseFailAlloc_4420_, 5, v_leInst_x3f_4368_);
lean_ctor_set(v_reuseFailAlloc_4420_, 6, v_ltInst_x3f_4369_);
lean_ctor_set(v_reuseFailAlloc_4420_, 7, v_lawfulOrderLTInst_x3f_4370_);
lean_ctor_set(v_reuseFailAlloc_4420_, 8, v_isPreorderInst_x3f_4371_);
lean_ctor_set(v_reuseFailAlloc_4420_, 9, v_orderedAddInst_x3f_4372_);
lean_ctor_set(v_reuseFailAlloc_4420_, 10, v_isLinearInst_x3f_4373_);
lean_ctor_set(v_reuseFailAlloc_4420_, 11, v_noNatDivInst_x3f_4374_);
lean_ctor_set(v_reuseFailAlloc_4420_, 12, v_ringInst_x3f_4375_);
lean_ctor_set(v_reuseFailAlloc_4420_, 13, v_commRingInst_x3f_4376_);
lean_ctor_set(v_reuseFailAlloc_4420_, 14, v_orderedRingInst_x3f_4377_);
lean_ctor_set(v_reuseFailAlloc_4420_, 15, v_fieldInst_x3f_4378_);
lean_ctor_set(v_reuseFailAlloc_4420_, 16, v_charInst_x3f_4379_);
lean_ctor_set(v_reuseFailAlloc_4420_, 17, v_zero_4380_);
lean_ctor_set(v_reuseFailAlloc_4420_, 18, v_ofNatZero_4381_);
lean_ctor_set(v_reuseFailAlloc_4420_, 19, v_one_x3f_4382_);
lean_ctor_set(v_reuseFailAlloc_4420_, 20, v_leFn_x3f_4383_);
lean_ctor_set(v_reuseFailAlloc_4420_, 21, v_ltFn_x3f_4384_);
lean_ctor_set(v_reuseFailAlloc_4420_, 22, v_addFn_4385_);
lean_ctor_set(v_reuseFailAlloc_4420_, 23, v_zsmulFn_4386_);
lean_ctor_set(v_reuseFailAlloc_4420_, 24, v_nsmulFn_4387_);
lean_ctor_set(v_reuseFailAlloc_4420_, 25, v_zsmulFn_x3f_4388_);
lean_ctor_set(v_reuseFailAlloc_4420_, 26, v_nsmulFn_x3f_4389_);
lean_ctor_set(v_reuseFailAlloc_4420_, 27, v_homomulFn_x3f_4390_);
lean_ctor_set(v_reuseFailAlloc_4420_, 28, v_subFn_4391_);
lean_ctor_set(v_reuseFailAlloc_4420_, 29, v_negFn_4392_);
lean_ctor_set(v_reuseFailAlloc_4420_, 30, v_vars_4393_);
lean_ctor_set(v_reuseFailAlloc_4420_, 31, v_varMap_4394_);
lean_ctor_set(v_reuseFailAlloc_4420_, 32, v_lowers_4395_);
lean_ctor_set(v_reuseFailAlloc_4420_, 33, v_uppers_4396_);
lean_ctor_set(v_reuseFailAlloc_4420_, 34, v_diseqs_4397_);
lean_ctor_set(v_reuseFailAlloc_4420_, 35, v_assignment_4398_);
lean_ctor_set(v_reuseFailAlloc_4420_, 36, v_conflict_x3f_4400_);
lean_ctor_set(v_reuseFailAlloc_4420_, 37, v_diseqSplits_4401_);
lean_ctor_set(v_reuseFailAlloc_4420_, 38, v___x_4412_);
lean_ctor_set(v_reuseFailAlloc_4420_, 39, v___x_4413_);
lean_ctor_set(v_reuseFailAlloc_4420_, 40, v_occurs_4404_);
lean_ctor_set(v_reuseFailAlloc_4420_, 41, v_ignored_4405_);
lean_ctor_set_uint8(v_reuseFailAlloc_4420_, sizeof(void*)*42, v_caseSplits_4399_);
v___x_4415_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
lean_object* v___x_4416_; lean_object* v___x_4418_; 
v___x_4416_ = lean_array_fset(v_xs_x27_4410_, v___y_4345_, v___x_4415_);
if (v_isShared_4361_ == 0)
{
lean_ctor_set(v___x_4360_, 0, v___x_4416_);
v___x_4418_ = v___x_4360_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v___x_4416_);
lean_ctor_set(v_reuseFailAlloc_4419_, 1, v_typeIdOf_4350_);
lean_ctor_set(v_reuseFailAlloc_4419_, 2, v_exprToStructId_4351_);
lean_ctor_set(v_reuseFailAlloc_4419_, 3, v_exprToStructIdEntries_4352_);
lean_ctor_set(v_reuseFailAlloc_4419_, 4, v_forbiddenNatModules_4353_);
lean_ctor_set(v_reuseFailAlloc_4419_, 5, v_natStructs_4354_);
lean_ctor_set(v_reuseFailAlloc_4419_, 6, v_natTypeIdOf_4355_);
lean_ctor_set(v_reuseFailAlloc_4419_, 7, v_exprToNatStructId_4356_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed(lean_object* v___y_4431_, lean_object* v_snd_4432_, lean_object* v_fst_4433_, lean_object* v_s_4434_){
_start:
{
lean_object* v_res_4435_; 
v_res_4435_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(v___y_4431_, v_snd_4432_, v_fst_4433_, v_s_4434_);
lean_dec(v___y_4431_);
return v_res_4435_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1(void){
_start:
{
lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0));
v___x_4438_ = l_Lean_stringToMessageData(v___x_4437_);
return v___x_4438_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4(void){
_start:
{
lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4446_ = l_Lean_Name_append(v___x_4445_, v___x_4444_);
return v___x_4446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object* v_c_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_){
_start:
{
lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4492_; lean_object* v___y_4493_; lean_object* v___y_4494_; lean_object* v___y_4495_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; lean_object* v___y_4500_; lean_object* v_options_4526_; lean_object* v_inheritedTraceOptions_4527_; uint8_t v_hasTrace_4528_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v_options_4545_; lean_object* v_inheritedTraceOptions_4546_; lean_object* v___y_4547_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; 
v_options_4526_ = lean_ctor_get(v_a_4457_, 2);
v_inheritedTraceOptions_4527_ = lean_ctor_get(v_a_4457_, 13);
v_hasTrace_4528_ = lean_ctor_get_uint8(v_options_4526_, sizeof(void*)*1);
if (v_hasTrace_4528_ == 0)
{
v___y_4564_ = v_a_4448_;
v___y_4565_ = v_a_4449_;
v___y_4566_ = v_a_4450_;
v___y_4567_ = v_a_4451_;
v___y_4568_ = v_a_4452_;
v___y_4569_ = v_a_4453_;
v___y_4570_ = v_a_4454_;
v___y_4571_ = v_a_4455_;
v___y_4572_ = v_a_4456_;
v___y_4573_ = v_a_4457_;
v___y_4574_ = v_a_4458_;
goto v___jp_4563_;
}
else
{
lean_object* v_cls_4670_; lean_object* v___x_4671_; uint8_t v___x_4672_; 
v_cls_4670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_4671_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_4672_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4527_, v_options_4526_, v___x_4671_);
if (v___x_4672_ == 0)
{
v___y_4564_ = v_a_4448_;
v___y_4565_ = v_a_4449_;
v___y_4566_ = v_a_4450_;
v___y_4567_ = v_a_4451_;
v___y_4568_ = v_a_4452_;
v___y_4569_ = v_a_4453_;
v___y_4570_ = v_a_4454_;
v___y_4571_ = v_a_4455_;
v___y_4572_ = v_a_4456_;
v___y_4573_ = v_a_4457_;
v___y_4574_ = v_a_4458_;
goto v___jp_4563_;
}
else
{
lean_object* v___x_4673_; 
v___x_4673_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v_a_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
v_a_4674_ = lean_ctor_get(v___x_4673_, 0);
lean_inc(v_a_4674_);
lean_dec_ref_known(v___x_4673_, 1);
v___x_4675_ = l_Lean_MessageData_ofExpr(v_a_4674_);
v___x_4676_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4670_, v___x_4675_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_dec_ref_known(v___x_4676_, 1);
v___y_4564_ = v_a_4448_;
v___y_4565_ = v_a_4449_;
v___y_4566_ = v_a_4450_;
v___y_4567_ = v_a_4451_;
v___y_4568_ = v_a_4452_;
v___y_4569_ = v_a_4453_;
v___y_4570_ = v_a_4454_;
v___y_4571_ = v_a_4455_;
v___y_4572_ = v_a_4456_;
v___y_4573_ = v_a_4457_;
v___y_4574_ = v_a_4458_;
goto v___jp_4563_;
}
else
{
lean_dec_ref(v_c_4447_);
return v___x_4676_;
}
}
else
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4684_; 
lean_dec_ref(v_c_4447_);
v_a_4677_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4684_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4684_ == 0)
{
v___x_4679_ = v___x_4673_;
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v___x_4673_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4682_; 
if (v_isShared_4680_ == 0)
{
v___x_4682_ = v___x_4679_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_a_4677_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
}
}
v___jp_4460_:
{
lean_object* v___x_4461_; lean_object* v___x_4462_; 
v___x_4461_ = lean_box(0);
v___x_4462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4462_, 0, v___x_4461_);
return v___x_4462_;
}
v___jp_4463_:
{
lean_object* v___f_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; 
lean_inc(v___y_4469_);
v___f_4480_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4480_, 0, v___y_4469_);
lean_closure_set(v___f_4480_, 1, v___y_4464_);
lean_closure_set(v___f_4480_, 2, v___y_4465_);
v___x_4481_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4482_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4481_, v___f_4480_, v___y_4470_);
if (lean_obj_tag(v___x_4482_) == 0)
{
lean_object* v___x_4483_; 
lean_dec_ref_known(v___x_4482_, 1);
v___x_4483_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v___y_4468_, v___y_4467_, v___y_4466_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
return v___x_4483_;
}
else
{
lean_dec(v___y_4468_);
lean_dec(v___y_4467_);
lean_dec_ref(v___y_4466_);
return v___x_4482_;
}
}
v___jp_4484_:
{
lean_object* v___x_4501_; 
v___x_4501_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; uint8_t v_caseSplits_4503_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
lean_inc(v_a_4502_);
lean_dec_ref_known(v___x_4501_, 1);
v_caseSplits_4503_ = lean_ctor_get_uint8(v_a_4502_, sizeof(void*)*42);
lean_dec(v_a_4502_);
if (v_caseSplits_4503_ == 0)
{
lean_object* v___x_4504_; 
v___x_4504_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v___y_4487_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_);
if (lean_obj_tag(v___x_4504_) == 0)
{
lean_object* v_a_4505_; uint8_t v___x_4506_; 
v_a_4505_ = lean_ctor_get(v___x_4504_, 0);
lean_inc(v_a_4505_);
lean_dec_ref_known(v___x_4504_, 1);
v___x_4506_ = lean_unbox(v_a_4505_);
lean_dec(v_a_4505_);
if (v___x_4506_ == 0)
{
v___y_4464_ = v___y_4485_;
v___y_4465_ = v___y_4486_;
v___y_4466_ = v___y_4487_;
v___y_4467_ = v___y_4488_;
v___y_4468_ = v___y_4489_;
v___y_4469_ = v___y_4490_;
v___y_4470_ = v___y_4491_;
v___y_4471_ = v___y_4492_;
v___y_4472_ = v___y_4493_;
v___y_4473_ = v___y_4494_;
v___y_4474_ = v___y_4495_;
v___y_4475_ = v___y_4496_;
v___y_4476_ = v___y_4497_;
v___y_4477_ = v___y_4498_;
v___y_4478_ = v___y_4499_;
v___y_4479_ = v___y_4500_;
goto v___jp_4463_;
}
else
{
lean_object* v___x_4507_; lean_object* v_a_4508_; lean_object* v___x_4509_; 
lean_inc_ref(v___y_4487_);
v___x_4507_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v___y_4487_);
v_a_4508_ = lean_ctor_get(v___x_4507_, 0);
lean_inc(v_a_4508_);
lean_dec_ref(v___x_4507_);
v___x_4509_ = l_Lean_Meta_Grind_Arith_Linear_propagateImpEq(v_a_4508_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_);
if (lean_obj_tag(v___x_4509_) == 0)
{
lean_dec_ref_known(v___x_4509_, 1);
v___y_4464_ = v___y_4485_;
v___y_4465_ = v___y_4486_;
v___y_4466_ = v___y_4487_;
v___y_4467_ = v___y_4488_;
v___y_4468_ = v___y_4489_;
v___y_4469_ = v___y_4490_;
v___y_4470_ = v___y_4491_;
v___y_4471_ = v___y_4492_;
v___y_4472_ = v___y_4493_;
v___y_4473_ = v___y_4494_;
v___y_4474_ = v___y_4495_;
v___y_4475_ = v___y_4496_;
v___y_4476_ = v___y_4497_;
v___y_4477_ = v___y_4498_;
v___y_4478_ = v___y_4499_;
v___y_4479_ = v___y_4500_;
goto v___jp_4463_;
}
else
{
lean_dec(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
return v___x_4509_;
}
}
}
else
{
lean_object* v_a_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4517_; 
lean_dec(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
v_a_4510_ = lean_ctor_get(v___x_4504_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4504_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4512_ = v___x_4504_;
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_a_4510_);
lean_dec(v___x_4504_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v___x_4515_; 
if (v_isShared_4513_ == 0)
{
v___x_4515_ = v___x_4512_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v_a_4510_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
}
else
{
v___y_4464_ = v___y_4485_;
v___y_4465_ = v___y_4486_;
v___y_4466_ = v___y_4487_;
v___y_4467_ = v___y_4488_;
v___y_4468_ = v___y_4489_;
v___y_4469_ = v___y_4490_;
v___y_4470_ = v___y_4491_;
v___y_4471_ = v___y_4492_;
v___y_4472_ = v___y_4493_;
v___y_4473_ = v___y_4494_;
v___y_4474_ = v___y_4495_;
v___y_4475_ = v___y_4496_;
v___y_4476_ = v___y_4497_;
v___y_4477_ = v___y_4498_;
v___y_4478_ = v___y_4499_;
v___y_4479_ = v___y_4500_;
goto v___jp_4463_;
}
}
else
{
lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4525_; 
lean_dec(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
v_a_4518_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4520_ = v___x_4501_;
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v___x_4501_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
lean_object* v___x_4523_; 
if (v_isShared_4521_ == 0)
{
v___x_4523_ = v___x_4520_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v_a_4518_);
v___x_4523_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
return v___x_4523_;
}
}
}
}
v___jp_4529_:
{
lean_object* v___x_4548_; lean_object* v___x_4549_; uint8_t v___x_4550_; 
v___x_4548_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_4549_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_4550_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4546_, v_options_4545_, v___x_4549_);
if (v___x_4550_ == 0)
{
v___y_4485_ = v___y_4530_;
v___y_4486_ = v___y_4531_;
v___y_4487_ = v___y_4532_;
v___y_4488_ = v___y_4533_;
v___y_4489_ = v___y_4534_;
v___y_4490_ = v___y_4535_;
v___y_4491_ = v___y_4536_;
v___y_4492_ = v___y_4537_;
v___y_4493_ = v___y_4538_;
v___y_4494_ = v___y_4539_;
v___y_4495_ = v___y_4540_;
v___y_4496_ = v___y_4541_;
v___y_4497_ = v___y_4542_;
v___y_4498_ = v___y_4543_;
v___y_4499_ = v___y_4544_;
v___y_4500_ = v___y_4547_;
goto v___jp_4484_;
}
else
{
lean_object* v___x_4551_; 
v___x_4551_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v___y_4532_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4547_);
if (lean_obj_tag(v___x_4551_) == 0)
{
lean_object* v_a_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v_a_4552_ = lean_ctor_get(v___x_4551_, 0);
lean_inc(v_a_4552_);
lean_dec_ref_known(v___x_4551_, 1);
v___x_4553_ = l_Lean_MessageData_ofExpr(v_a_4552_);
v___x_4554_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4548_, v___x_4553_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4547_);
if (lean_obj_tag(v___x_4554_) == 0)
{
lean_dec_ref_known(v___x_4554_, 1);
v___y_4485_ = v___y_4530_;
v___y_4486_ = v___y_4531_;
v___y_4487_ = v___y_4532_;
v___y_4488_ = v___y_4533_;
v___y_4489_ = v___y_4534_;
v___y_4490_ = v___y_4535_;
v___y_4491_ = v___y_4536_;
v___y_4492_ = v___y_4537_;
v___y_4493_ = v___y_4538_;
v___y_4494_ = v___y_4539_;
v___y_4495_ = v___y_4540_;
v___y_4496_ = v___y_4541_;
v___y_4497_ = v___y_4542_;
v___y_4498_ = v___y_4543_;
v___y_4499_ = v___y_4544_;
v___y_4500_ = v___y_4547_;
goto v___jp_4484_;
}
else
{
lean_dec(v___y_4534_);
lean_dec(v___y_4533_);
lean_dec_ref(v___y_4532_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
return v___x_4554_;
}
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
lean_dec(v___y_4534_);
lean_dec(v___y_4533_);
lean_dec_ref(v___y_4532_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
v_a_4555_ = lean_ctor_get(v___x_4551_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4551_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4551_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4551_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4560_; 
if (v_isShared_4558_ == 0)
{
v___x_4560_ = v___x_4557_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
}
}
v___jp_4563_:
{
lean_object* v___x_4575_; 
lean_inc_ref(v___y_4573_);
v___x_4575_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_4447_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
if (lean_obj_tag(v___x_4575_) == 0)
{
lean_object* v_a_4576_; lean_object* v_p_4577_; lean_object* v___x_4578_; uint8_t v___x_4579_; 
v_a_4576_ = lean_ctor_get(v___x_4575_, 0);
lean_inc(v_a_4576_);
lean_dec_ref_known(v___x_4575_, 1);
v_p_4577_ = lean_ctor_get(v_a_4576_, 0);
v___x_4578_ = lean_box(0);
v___x_4579_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_4577_, v___x_4578_);
if (v___x_4579_ == 0)
{
lean_object* v___x_4580_; 
v___x_4580_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_a_4576_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
if (lean_obj_tag(v___x_4580_) == 0)
{
lean_object* v_a_4581_; lean_object* v_snd_4582_; lean_object* v_options_4583_; uint8_t v_hasTrace_4584_; 
v_a_4581_ = lean_ctor_get(v___x_4580_, 0);
lean_inc(v_a_4581_);
lean_dec_ref_known(v___x_4580_, 1);
v_snd_4582_ = lean_ctor_get(v_a_4581_, 1);
lean_inc(v_snd_4582_);
v_options_4583_ = lean_ctor_get(v___y_4573_, 2);
v_hasTrace_4584_ = lean_ctor_get_uint8(v_options_4583_, sizeof(void*)*1);
if (v_hasTrace_4584_ == 0)
{
lean_object* v_fst_4585_; lean_object* v_fst_4586_; lean_object* v_snd_4587_; 
v_fst_4585_ = lean_ctor_get(v_a_4581_, 0);
lean_inc(v_fst_4585_);
lean_dec(v_a_4581_);
v_fst_4586_ = lean_ctor_get(v_snd_4582_, 0);
lean_inc_n(v_fst_4586_, 2);
v_snd_4587_ = lean_ctor_get(v_snd_4582_, 1);
lean_inc_n(v_snd_4587_, 2);
lean_dec(v_snd_4582_);
v___y_4485_ = v_snd_4587_;
v___y_4486_ = v_fst_4586_;
v___y_4487_ = v_snd_4587_;
v___y_4488_ = v_fst_4586_;
v___y_4489_ = v_fst_4585_;
v___y_4490_ = v___y_4564_;
v___y_4491_ = v___y_4565_;
v___y_4492_ = v___y_4566_;
v___y_4493_ = v___y_4567_;
v___y_4494_ = v___y_4568_;
v___y_4495_ = v___y_4569_;
v___y_4496_ = v___y_4570_;
v___y_4497_ = v___y_4571_;
v___y_4498_ = v___y_4572_;
v___y_4499_ = v___y_4573_;
v___y_4500_ = v___y_4574_;
goto v___jp_4484_;
}
else
{
lean_object* v_fst_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4634_; 
v_fst_4588_ = lean_ctor_get(v_a_4581_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v_a_4581_);
if (v_isSharedCheck_4634_ == 0)
{
lean_object* v_unused_4635_; 
v_unused_4635_ = lean_ctor_get(v_a_4581_, 1);
lean_dec(v_unused_4635_);
v___x_4590_ = v_a_4581_;
v_isShared_4591_ = v_isSharedCheck_4634_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_fst_4588_);
lean_dec(v_a_4581_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4634_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v_fst_4592_; lean_object* v_snd_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4633_; 
v_fst_4592_ = lean_ctor_get(v_snd_4582_, 0);
v_snd_4593_ = lean_ctor_get(v_snd_4582_, 1);
v_isSharedCheck_4633_ = !lean_is_exclusive(v_snd_4582_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4595_ = v_snd_4582_;
v_isShared_4596_ = v_isSharedCheck_4633_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_snd_4593_);
lean_inc(v_fst_4592_);
lean_dec(v_snd_4582_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4633_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v_inheritedTraceOptions_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; uint8_t v___x_4600_; 
v_inheritedTraceOptions_4597_ = lean_ctor_get(v___y_4573_, 13);
v___x_4598_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_4599_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_4600_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4597_, v_options_4583_, v___x_4599_);
if (v___x_4600_ == 0)
{
lean_del_object(v___x_4595_);
lean_del_object(v___x_4590_);
lean_inc(v_fst_4592_);
lean_inc(v_snd_4593_);
v___y_4530_ = v_snd_4593_;
v___y_4531_ = v_fst_4592_;
v___y_4532_ = v_snd_4593_;
v___y_4533_ = v_fst_4592_;
v___y_4534_ = v_fst_4588_;
v___y_4535_ = v___y_4564_;
v___y_4536_ = v___y_4565_;
v___y_4537_ = v___y_4566_;
v___y_4538_ = v___y_4567_;
v___y_4539_ = v___y_4568_;
v___y_4540_ = v___y_4569_;
v___y_4541_ = v___y_4570_;
v___y_4542_ = v___y_4571_;
v___y_4543_ = v___y_4572_;
v___y_4544_ = v___y_4573_;
v_options_4545_ = v_options_4583_;
v_inheritedTraceOptions_4546_ = v_inheritedTraceOptions_4597_;
v___y_4547_ = v___y_4574_;
goto v___jp_4529_;
}
else
{
lean_object* v___x_4601_; 
v___x_4601_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_4592_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
if (lean_obj_tag(v___x_4601_) == 0)
{
lean_object* v_a_4602_; lean_object* v___x_4603_; 
v_a_4602_ = lean_ctor_get(v___x_4601_, 0);
lean_inc(v_a_4602_);
lean_dec_ref_known(v___x_4601_, 1);
v___x_4603_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_4593_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
if (lean_obj_tag(v___x_4603_) == 0)
{
lean_object* v_a_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4608_; 
v_a_4604_ = lean_ctor_get(v___x_4603_, 0);
lean_inc(v_a_4604_);
lean_dec_ref_known(v___x_4603_, 1);
v___x_4605_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1);
v___x_4606_ = l_Lean_MessageData_ofExpr(v_a_4602_);
if (v_isShared_4596_ == 0)
{
lean_ctor_set_tag(v___x_4595_, 7);
lean_ctor_set(v___x_4595_, 1, v___x_4606_);
lean_ctor_set(v___x_4595_, 0, v___x_4605_);
v___x_4608_ = v___x_4595_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v___x_4605_);
lean_ctor_set(v_reuseFailAlloc_4616_, 1, v___x_4606_);
v___x_4608_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
lean_object* v___x_4609_; lean_object* v___x_4611_; 
v___x_4609_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_4591_ == 0)
{
lean_ctor_set_tag(v___x_4590_, 7);
lean_ctor_set(v___x_4590_, 1, v___x_4609_);
lean_ctor_set(v___x_4590_, 0, v___x_4608_);
v___x_4611_ = v___x_4590_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v___x_4608_);
lean_ctor_set(v_reuseFailAlloc_4615_, 1, v___x_4609_);
v___x_4611_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; 
v___x_4612_ = l_Lean_MessageData_ofExpr(v_a_4604_);
v___x_4613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4613_, 0, v___x_4611_);
lean_ctor_set(v___x_4613_, 1, v___x_4612_);
v___x_4614_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4598_, v___x_4613_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_dec_ref_known(v___x_4614_, 1);
lean_inc(v_fst_4592_);
lean_inc(v_snd_4593_);
v___y_4530_ = v_snd_4593_;
v___y_4531_ = v_fst_4592_;
v___y_4532_ = v_snd_4593_;
v___y_4533_ = v_fst_4592_;
v___y_4534_ = v_fst_4588_;
v___y_4535_ = v___y_4564_;
v___y_4536_ = v___y_4565_;
v___y_4537_ = v___y_4566_;
v___y_4538_ = v___y_4567_;
v___y_4539_ = v___y_4568_;
v___y_4540_ = v___y_4569_;
v___y_4541_ = v___y_4570_;
v___y_4542_ = v___y_4571_;
v___y_4543_ = v___y_4572_;
v___y_4544_ = v___y_4573_;
v_options_4545_ = v_options_4583_;
v_inheritedTraceOptions_4546_ = v_inheritedTraceOptions_4597_;
v___y_4547_ = v___y_4574_;
goto v___jp_4529_;
}
else
{
lean_dec(v_snd_4593_);
lean_dec(v_fst_4592_);
lean_dec(v_fst_4588_);
return v___x_4614_;
}
}
}
}
else
{
lean_object* v_a_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4624_; 
lean_dec(v_a_4602_);
lean_del_object(v___x_4595_);
lean_dec(v_snd_4593_);
lean_dec(v_fst_4592_);
lean_del_object(v___x_4590_);
lean_dec(v_fst_4588_);
v_a_4617_ = lean_ctor_get(v___x_4603_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4619_ = v___x_4603_;
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_a_4617_);
lean_dec(v___x_4603_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v___x_4622_; 
if (v_isShared_4620_ == 0)
{
v___x_4622_ = v___x_4619_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_a_4617_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
}
}
else
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4632_; 
lean_del_object(v___x_4595_);
lean_dec(v_snd_4593_);
lean_dec(v_fst_4592_);
lean_del_object(v___x_4590_);
lean_dec(v_fst_4588_);
v_a_4625_ = lean_ctor_get(v___x_4601_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4601_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4627_ = v___x_4601_;
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4601_);
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
}
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
v_a_4636_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4580_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4580_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4641_; 
if (v_isShared_4639_ == 0)
{
v___x_4641_ = v___x_4638_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_a_4636_);
v___x_4641_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
return v___x_4641_;
}
}
}
}
else
{
lean_object* v_options_4644_; uint8_t v_hasTrace_4645_; 
v_options_4644_ = lean_ctor_get(v___y_4573_, 2);
v_hasTrace_4645_ = lean_ctor_get_uint8(v_options_4644_, sizeof(void*)*1);
if (v_hasTrace_4645_ == 0)
{
lean_dec(v_a_4576_);
goto v___jp_4460_;
}
else
{
lean_object* v_inheritedTraceOptions_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; uint8_t v___x_4649_; 
v_inheritedTraceOptions_4646_ = lean_ctor_get(v___y_4573_, 13);
v___x_4647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4648_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4);
v___x_4649_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4646_, v_options_4644_, v___x_4648_);
if (v___x_4649_ == 0)
{
lean_dec(v_a_4576_);
goto v___jp_4460_;
}
else
{
lean_object* v___x_4650_; 
v___x_4650_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_a_4576_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
lean_dec(v_a_4576_);
if (lean_obj_tag(v___x_4650_) == 0)
{
lean_object* v_a_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
v_a_4651_ = lean_ctor_get(v___x_4650_, 0);
lean_inc(v_a_4651_);
lean_dec_ref_known(v___x_4650_, 1);
v___x_4652_ = l_Lean_MessageData_ofExpr(v_a_4651_);
v___x_4653_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4647_, v___x_4652_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
if (lean_obj_tag(v___x_4653_) == 0)
{
lean_dec_ref_known(v___x_4653_, 1);
goto v___jp_4460_;
}
else
{
return v___x_4653_;
}
}
else
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4661_; 
v_a_4654_ = lean_ctor_get(v___x_4650_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4650_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4656_ = v___x_4650_;
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4650_);
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
}
else
{
lean_object* v_a_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4669_; 
v_a_4662_ = lean_ctor_get(v___x_4575_, 0);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4575_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4664_ = v___x_4575_;
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_a_4662_);
lean_dec(v___x_4575_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4667_; 
if (v_isShared_4665_ == 0)
{
v___x_4667_ = v___x_4664_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v_a_4662_);
v___x_4667_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
return v___x_4667_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object* v_c_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_){
_start:
{
lean_object* v_res_4698_; 
v_res_4698_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v_c_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_);
lean_dec(v_a_4696_);
lean_dec_ref(v_a_4695_);
lean_dec(v_a_4694_);
lean_dec_ref(v_a_4693_);
lean_dec(v_a_4692_);
lean_dec_ref(v_a_4691_);
lean_dec(v_a_4690_);
lean_dec_ref(v_a_4689_);
lean_dec(v_a_4688_);
lean_dec(v_a_4687_);
lean_dec(v_a_4686_);
return v_res_4698_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2(void){
_start:
{
lean_object* v_cls_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; 
v_cls_4703_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4704_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4705_ = l_Lean_Name_append(v___x_4704_, v_cls_4703_);
return v___x_4705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object* v_a_4706_, lean_object* v_b_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_){
_start:
{
lean_object* v_options_4716_; uint8_t v_hasTrace_4717_; 
v_options_4716_ = lean_ctor_get(v_a_4710_, 2);
v_hasTrace_4717_ = lean_ctor_get_uint8(v_options_4716_, sizeof(void*)*1);
if (v_hasTrace_4717_ == 0)
{
lean_dec_ref(v_b_4707_);
lean_dec_ref(v_a_4706_);
goto v___jp_4713_;
}
else
{
lean_object* v_inheritedTraceOptions_4718_; lean_object* v_cls_4719_; lean_object* v___x_4720_; uint8_t v___x_4721_; 
v_inheritedTraceOptions_4718_ = lean_ctor_get(v_a_4710_, 13);
v_cls_4719_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4720_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2);
v___x_4721_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4718_, v_options_4716_, v___x_4720_);
if (v___x_4721_ == 0)
{
lean_dec_ref(v_b_4707_);
lean_dec_ref(v_a_4706_);
goto v___jp_4713_;
}
else
{
lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4722_ = l_Lean_MessageData_ofExpr(v_a_4706_);
v___x_4723_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_4724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4724_, 0, v___x_4722_);
lean_ctor_set(v___x_4724_, 1, v___x_4723_);
v___x_4725_ = l_Lean_MessageData_ofExpr(v_b_4707_);
v___x_4726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4726_, 0, v___x_4724_);
lean_ctor_set(v___x_4726_, 1, v___x_4725_);
v___x_4727_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4719_, v___x_4726_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_);
return v___x_4727_;
}
}
v___jp_4713_:
{
lean_object* v___x_4714_; lean_object* v___x_4715_; 
v___x_4714_ = lean_box(0);
v___x_4715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4714_);
return v___x_4715_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object* v_a_4728_, lean_object* v_b_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_){
_start:
{
lean_object* v_res_4735_; 
v_res_4735_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4728_, v_b_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_);
lean_dec(v_a_4733_);
lean_dec_ref(v_a_4732_);
lean_dec(v_a_4731_);
lean_dec_ref(v_a_4730_);
return v_res_4735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object* v_a_4736_, lean_object* v_b_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_){
_start:
{
lean_object* v___x_4750_; 
v___x_4750_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4736_, v_b_4737_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object* v_a_4751_, lean_object* v_b_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_){
_start:
{
lean_object* v_res_4765_; 
v_res_4765_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(v_a_4751_, v_b_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_);
lean_dec(v_a_4763_);
lean_dec_ref(v_a_4762_);
lean_dec(v_a_4761_);
lean_dec_ref(v_a_4760_);
lean_dec(v_a_4759_);
lean_dec_ref(v_a_4758_);
lean_dec(v_a_4757_);
lean_dec_ref(v_a_4756_);
lean_dec(v_a_4755_);
lean_dec(v_a_4754_);
lean_dec(v_a_4753_);
return v_res_4765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object* v_a_4766_, lean_object* v_b_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_){
_start:
{
lean_object* v___x_4780_; 
v___x_4780_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4766_, v_a_4769_);
if (lean_obj_tag(v___x_4780_) == 0)
{
lean_object* v_a_4781_; uint8_t v___x_4782_; lean_object* v___x_4783_; 
v_a_4781_ = lean_ctor_get(v___x_4780_, 0);
lean_inc(v_a_4781_);
lean_dec_ref_known(v___x_4780_, 1);
v___x_4782_ = 0;
lean_inc_ref(v_a_4766_);
v___x_4783_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_4766_, v___x_4782_, v_a_4781_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_);
if (lean_obj_tag(v___x_4783_) == 0)
{
lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4833_; 
v_a_4784_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4833_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4833_ == 0)
{
v___x_4786_ = v___x_4783_;
v_isShared_4787_ = v_isSharedCheck_4833_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v___x_4783_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4833_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
if (lean_obj_tag(v_a_4784_) == 1)
{
lean_object* v_val_4788_; lean_object* v___x_4789_; 
lean_del_object(v___x_4786_);
v_val_4788_ = lean_ctor_get(v_a_4784_, 0);
lean_inc(v_val_4788_);
lean_dec_ref_known(v_a_4784_, 1);
v___x_4789_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4767_, v_a_4769_);
if (lean_obj_tag(v___x_4789_) == 0)
{
lean_object* v_a_4790_; lean_object* v___x_4791_; 
v_a_4790_ = lean_ctor_get(v___x_4789_, 0);
lean_inc(v_a_4790_);
lean_dec_ref_known(v___x_4789_, 1);
lean_inc_ref(v_b_4767_);
v___x_4791_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_4767_, v___x_4782_, v_a_4790_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_);
if (lean_obj_tag(v___x_4791_) == 0)
{
lean_object* v_a_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4812_; 
v_a_4792_ = lean_ctor_get(v___x_4791_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4791_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4794_ = v___x_4791_;
v_isShared_4795_ = v_isSharedCheck_4812_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_a_4792_);
lean_dec(v___x_4791_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4812_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
if (lean_obj_tag(v_a_4792_) == 1)
{
lean_object* v_val_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; uint8_t v___x_4800_; 
v_val_4796_ = lean_ctor_get(v_a_4792_, 0);
lean_inc_n(v_val_4796_, 2);
lean_dec_ref_known(v_a_4792_, 1);
lean_inc(v_val_4788_);
v___x_4797_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4797_, 0, v_val_4788_);
lean_ctor_set(v___x_4797_, 1, v_val_4796_);
v___x_4798_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4797_);
v___x_4799_ = lean_box(0);
v___x_4800_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4798_, v___x_4799_);
if (v___x_4800_ == 0)
{
lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; 
lean_del_object(v___x_4794_);
v___x_4801_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4801_, 0, v_a_4766_);
lean_ctor_set(v___x_4801_, 1, v_b_4767_);
lean_ctor_set(v___x_4801_, 2, v_val_4788_);
lean_ctor_set(v___x_4801_, 3, v_val_4796_);
v___x_4802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4802_, 0, v___x_4798_);
lean_ctor_set(v___x_4802_, 1, v___x_4801_);
v___x_4803_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_4802_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_);
return v___x_4803_;
}
else
{
lean_object* v___x_4804_; lean_object* v___x_4806_; 
lean_dec(v___x_4798_);
lean_dec(v_val_4796_);
lean_dec(v_val_4788_);
lean_dec_ref(v_b_4767_);
lean_dec_ref(v_a_4766_);
v___x_4804_ = lean_box(0);
if (v_isShared_4795_ == 0)
{
lean_ctor_set(v___x_4794_, 0, v___x_4804_);
v___x_4806_ = v___x_4794_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v___x_4804_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
}
else
{
lean_object* v___x_4808_; lean_object* v___x_4810_; 
lean_dec(v_a_4792_);
lean_dec(v_val_4788_);
lean_dec_ref(v_b_4767_);
lean_dec_ref(v_a_4766_);
v___x_4808_ = lean_box(0);
if (v_isShared_4795_ == 0)
{
lean_ctor_set(v___x_4794_, 0, v___x_4808_);
v___x_4810_ = v___x_4794_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v___x_4808_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
return v___x_4810_;
}
}
}
}
else
{
lean_object* v_a_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4820_; 
lean_dec(v_val_4788_);
lean_dec_ref(v_b_4767_);
lean_dec_ref(v_a_4766_);
v_a_4813_ = lean_ctor_get(v___x_4791_, 0);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___x_4791_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4815_ = v___x_4791_;
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_a_4813_);
lean_dec(v___x_4791_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___x_4818_; 
if (v_isShared_4816_ == 0)
{
v___x_4818_ = v___x_4815_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_a_4813_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
}
}
else
{
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4828_; 
lean_dec(v_val_4788_);
lean_dec_ref(v_b_4767_);
lean_dec_ref(v_a_4766_);
v_a_4821_ = lean_ctor_get(v___x_4789_, 0);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4823_ = v___x_4789_;
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v___x_4789_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v___x_4826_; 
if (v_isShared_4824_ == 0)
{
v___x_4826_ = v___x_4823_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v_a_4821_);
v___x_4826_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
return v___x_4826_;
}
}
}
}
else
{
lean_object* v___x_4829_; lean_object* v___x_4831_; 
lean_dec(v_a_4784_);
lean_dec_ref(v_b_4767_);
lean_dec_ref(v_a_4766_);
v___x_4829_ = lean_box(0);
if (v_isShared_4787_ == 0)
{
lean_ctor_set(v___x_4786_, 0, v___x_4829_);
v___x_4831_ = v___x_4786_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v___x_4829_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
return v___x_4831_;
}
}
}
}
else
{
lean_object* v_a_4834_; lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_4841_; 
lean_dec_ref(v_b_4767_);
lean_dec_ref(v_a_4766_);
v_a_4834_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4841_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4836_ = v___x_4783_;
v_isShared_4837_ = v_isSharedCheck_4841_;
goto v_resetjp_4835_;
}
else
{
lean_inc(v_a_4834_);
lean_dec(v___x_4783_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_4841_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
lean_object* v___x_4839_; 
if (v_isShared_4837_ == 0)
{
v___x_4839_ = v___x_4836_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v_a_4834_);
v___x_4839_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
return v___x_4839_;
}
}
}
}
else
{
lean_object* v_a_4842_; lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4849_; 
lean_dec_ref(v_b_4767_);
lean_dec_ref(v_a_4766_);
v_a_4842_ = lean_ctor_get(v___x_4780_, 0);
v_isSharedCheck_4849_ = !lean_is_exclusive(v___x_4780_);
if (v_isSharedCheck_4849_ == 0)
{
v___x_4844_ = v___x_4780_;
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
else
{
lean_inc(v_a_4842_);
lean_dec(v___x_4780_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v___x_4847_; 
if (v_isShared_4845_ == 0)
{
v___x_4847_ = v___x_4844_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v_a_4842_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___boxed(lean_object* v_a_4850_, lean_object* v_b_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_){
_start:
{
lean_object* v_res_4864_; 
v_res_4864_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_4850_, v_b_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_);
lean_dec(v_a_4862_);
lean_dec_ref(v_a_4861_);
lean_dec(v_a_4860_);
lean_dec_ref(v_a_4859_);
lean_dec(v_a_4858_);
lean_dec_ref(v_a_4857_);
lean_dec(v_a_4856_);
lean_dec_ref(v_a_4855_);
lean_dec(v_a_4854_);
lean_dec(v_a_4853_);
lean_dec(v_a_4852_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(lean_object* v_a_4865_, lean_object* v_b_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_){
_start:
{
lean_object* v___x_4879_; 
v___x_4879_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_);
if (lean_obj_tag(v___x_4879_) == 0)
{
lean_object* v_a_4880_; lean_object* v___x_4881_; 
v_a_4880_ = lean_ctor_get(v___x_4879_, 0);
lean_inc(v_a_4880_);
lean_dec_ref_known(v___x_4879_, 1);
lean_inc_ref(v_a_4865_);
v___x_4881_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_4865_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_);
if (lean_obj_tag(v___x_4881_) == 0)
{
lean_object* v_a_4882_; lean_object* v_fst_4883_; lean_object* v___x_4884_; 
v_a_4882_ = lean_ctor_get(v___x_4881_, 0);
lean_inc(v_a_4882_);
lean_dec_ref_known(v___x_4881_, 1);
v_fst_4883_ = lean_ctor_get(v_a_4882_, 0);
lean_inc(v_fst_4883_);
lean_dec(v_a_4882_);
lean_inc_ref(v_b_4866_);
v___x_4884_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_);
if (lean_obj_tag(v___x_4884_) == 0)
{
lean_object* v_a_4885_; lean_object* v_fst_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4969_; 
v_a_4885_ = lean_ctor_get(v___x_4884_, 0);
lean_inc(v_a_4885_);
lean_dec_ref_known(v___x_4884_, 1);
v_fst_4886_ = lean_ctor_get(v_a_4885_, 0);
v_isSharedCheck_4969_ = !lean_is_exclusive(v_a_4885_);
if (v_isSharedCheck_4969_ == 0)
{
lean_object* v_unused_4970_; 
v_unused_4970_ = lean_ctor_get(v_a_4885_, 1);
lean_dec(v_unused_4970_);
v___x_4888_ = v_a_4885_;
v_isShared_4889_ = v_isSharedCheck_4969_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_fst_4886_);
lean_dec(v_a_4885_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4969_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v___x_4890_; 
v___x_4890_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4865_, v_a_4868_);
if (lean_obj_tag(v___x_4890_) == 0)
{
lean_object* v_a_4891_; lean_object* v_id_4892_; lean_object* v_structId_4893_; uint8_t v___x_4894_; lean_object* v___x_4895_; 
v_a_4891_ = lean_ctor_get(v___x_4890_, 0);
lean_inc(v_a_4891_);
lean_dec_ref_known(v___x_4890_, 1);
v_id_4892_ = lean_ctor_get(v_a_4880_, 0);
lean_inc(v_id_4892_);
v_structId_4893_ = lean_ctor_get(v_a_4880_, 1);
lean_inc(v_structId_4893_);
lean_dec(v_a_4880_);
v___x_4894_ = 0;
v___x_4895_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4883_, v___x_4894_, v_a_4891_, v_structId_4893_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_object* v_a_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4952_; 
v_a_4896_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_4952_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4898_ = v___x_4895_;
v_isShared_4899_ = v_isSharedCheck_4952_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_a_4896_);
lean_dec(v___x_4895_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4952_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
if (lean_obj_tag(v_a_4896_) == 1)
{
lean_object* v_val_4900_; lean_object* v___x_4901_; 
lean_del_object(v___x_4898_);
v_val_4900_ = lean_ctor_get(v_a_4896_, 0);
lean_inc(v_val_4900_);
lean_dec_ref_known(v_a_4896_, 1);
v___x_4901_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4866_, v_a_4868_);
if (lean_obj_tag(v___x_4901_) == 0)
{
lean_object* v_a_4902_; lean_object* v___x_4903_; 
v_a_4902_ = lean_ctor_get(v___x_4901_, 0);
lean_inc(v_a_4902_);
lean_dec_ref_known(v___x_4901_, 1);
v___x_4903_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4886_, v___x_4894_, v_a_4902_, v_structId_4893_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_);
if (lean_obj_tag(v___x_4903_) == 0)
{
lean_object* v_a_4904_; lean_object* v___x_4906_; uint8_t v_isShared_4907_; uint8_t v_isSharedCheck_4931_; 
v_a_4904_ = lean_ctor_get(v___x_4903_, 0);
v_isSharedCheck_4931_ = !lean_is_exclusive(v___x_4903_);
if (v_isSharedCheck_4931_ == 0)
{
v___x_4906_ = v___x_4903_;
v_isShared_4907_ = v_isSharedCheck_4931_;
goto v_resetjp_4905_;
}
else
{
lean_inc(v_a_4904_);
lean_dec(v___x_4903_);
v___x_4906_ = lean_box(0);
v_isShared_4907_ = v_isSharedCheck_4931_;
goto v_resetjp_4905_;
}
v_resetjp_4905_:
{
if (lean_obj_tag(v_a_4904_) == 1)
{
lean_object* v_val_4908_; lean_object* v___x_4910_; 
v_val_4908_ = lean_ctor_get(v_a_4904_, 0);
lean_inc_n(v_val_4908_, 2);
lean_dec_ref_known(v_a_4904_, 1);
lean_inc(v_val_4900_);
if (v_isShared_4889_ == 0)
{
lean_ctor_set_tag(v___x_4888_, 3);
lean_ctor_set(v___x_4888_, 1, v_val_4908_);
lean_ctor_set(v___x_4888_, 0, v_val_4900_);
v___x_4910_ = v___x_4888_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v_val_4900_);
lean_ctor_set(v_reuseFailAlloc_4926_, 1, v_val_4908_);
v___x_4910_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
lean_object* v___x_4911_; lean_object* v___x_4912_; uint8_t v___x_4913_; 
v___x_4911_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4910_);
v___x_4912_ = lean_box(0);
v___x_4913_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4911_, v___x_4912_);
if (v___x_4913_ == 0)
{
lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; 
lean_del_object(v___x_4906_);
lean_inc(v_val_4908_);
lean_inc(v_val_4900_);
lean_inc(v_id_4892_);
lean_inc_ref(v_b_4866_);
lean_inc_ref(v_a_4865_);
v___x_4914_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4914_, 0, v_a_4865_);
lean_ctor_set(v___x_4914_, 1, v_b_4866_);
lean_ctor_set(v___x_4914_, 2, v_id_4892_);
lean_ctor_set(v___x_4914_, 3, v_val_4900_);
lean_ctor_set(v___x_4914_, 4, v_val_4908_);
lean_inc(v___x_4911_);
v___x_4915_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4915_, 0, v___x_4911_);
lean_ctor_set(v___x_4915_, 1, v___x_4914_);
lean_ctor_set_uint8(v___x_4915_, sizeof(void*)*2, v___x_4894_);
v___x_4916_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4915_, v_structId_4893_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_);
if (lean_obj_tag(v___x_4916_) == 0)
{
lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; 
lean_dec_ref_known(v___x_4916_, 1);
v___x_4917_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4918_ = l_Lean_Grind_Linarith_Poly_mul(v___x_4911_, v___x_4917_);
v___x_4919_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4919_, 0, v_b_4866_);
lean_ctor_set(v___x_4919_, 1, v_a_4865_);
lean_ctor_set(v___x_4919_, 2, v_id_4892_);
lean_ctor_set(v___x_4919_, 3, v_val_4908_);
lean_ctor_set(v___x_4919_, 4, v_val_4900_);
v___x_4920_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4920_, 0, v___x_4918_);
lean_ctor_set(v___x_4920_, 1, v___x_4919_);
lean_ctor_set_uint8(v___x_4920_, sizeof(void*)*2, v___x_4894_);
v___x_4921_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4920_, v_structId_4893_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_);
lean_dec(v_structId_4893_);
return v___x_4921_;
}
else
{
lean_dec(v___x_4911_);
lean_dec(v_val_4908_);
lean_dec(v_val_4900_);
lean_dec(v_structId_4893_);
lean_dec(v_id_4892_);
lean_dec_ref(v_b_4866_);
lean_dec_ref(v_a_4865_);
return v___x_4916_;
}
}
else
{
lean_object* v___x_4922_; lean_object* v___x_4924_; 
lean_dec(v___x_4911_);
lean_dec(v_val_4908_);
lean_dec(v_val_4900_);
lean_dec(v_structId_4893_);
lean_dec(v_id_4892_);
lean_dec_ref(v_b_4866_);
lean_dec_ref(v_a_4865_);
v___x_4922_ = lean_box(0);
if (v_isShared_4907_ == 0)
{
lean_ctor_set(v___x_4906_, 0, v___x_4922_);
v___x_4924_ = v___x_4906_;
goto v_reusejp_4923_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v___x_4922_);
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
else
{
lean_object* v___x_4927_; lean_object* v___x_4929_; 
lean_dec(v_a_4904_);
lean_dec(v_val_4900_);
lean_dec(v_structId_4893_);
lean_dec(v_id_4892_);
lean_del_object(v___x_4888_);
lean_dec_ref(v_b_4866_);
lean_dec_ref(v_a_4865_);
v___x_4927_ = lean_box(0);
if (v_isShared_4907_ == 0)
{
lean_ctor_set(v___x_4906_, 0, v___x_4927_);
v___x_4929_ = v___x_4906_;
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
lean_object* v_a_4932_; lean_object* v___x_4934_; uint8_t v_isShared_4935_; uint8_t v_isSharedCheck_4939_; 
lean_dec(v_val_4900_);
lean_dec(v_structId_4893_);
lean_dec(v_id_4892_);
lean_del_object(v___x_4888_);
lean_dec_ref(v_b_4866_);
lean_dec_ref(v_a_4865_);
v_a_4932_ = lean_ctor_get(v___x_4903_, 0);
v_isSharedCheck_4939_ = !lean_is_exclusive(v___x_4903_);
if (v_isSharedCheck_4939_ == 0)
{
v___x_4934_ = v___x_4903_;
v_isShared_4935_ = v_isSharedCheck_4939_;
goto v_resetjp_4933_;
}
else
{
lean_inc(v_a_4932_);
lean_dec(v___x_4903_);
v___x_4934_ = lean_box(0);
v_isShared_4935_ = v_isSharedCheck_4939_;
goto v_resetjp_4933_;
}
v_resetjp_4933_:
{
lean_object* v___x_4937_; 
if (v_isShared_4935_ == 0)
{
v___x_4937_ = v___x_4934_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_a_4932_);
v___x_4937_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
return v___x_4937_;
}
}
}
}
else
{
lean_object* v_a_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4947_; 
lean_dec(v_val_4900_);
lean_dec(v_structId_4893_);
lean_dec(v_id_4892_);
lean_del_object(v___x_4888_);
lean_dec(v_fst_4886_);
lean_dec_ref(v_b_4866_);
lean_dec_ref(v_a_4865_);
v_a_4940_ = lean_ctor_get(v___x_4901_, 0);
v_isSharedCheck_4947_ = !lean_is_exclusive(v___x_4901_);
if (v_isSharedCheck_4947_ == 0)
{
v___x_4942_ = v___x_4901_;
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_a_4940_);
lean_dec(v___x_4901_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
lean_object* v___x_4945_; 
if (v_isShared_4943_ == 0)
{
v___x_4945_ = v___x_4942_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v_a_4940_);
v___x_4945_ = v_reuseFailAlloc_4946_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
return v___x_4945_;
}
}
}
}
else
{
lean_object* v___x_4948_; lean_object* v___x_4950_; 
lean_dec(v_a_4896_);
lean_dec(v_structId_4893_);
lean_dec(v_id_4892_);
lean_del_object(v___x_4888_);
lean_dec(v_fst_4886_);
lean_dec_ref(v_b_4866_);
lean_dec_ref(v_a_4865_);
v___x_4948_ = lean_box(0);
if (v_isShared_4899_ == 0)
{
lean_ctor_set(v___x_4898_, 0, v___x_4948_);
v___x_4950_ = v___x_4898_;
goto v_reusejp_4949_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v___x_4948_);
v___x_4950_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4949_;
}
v_reusejp_4949_:
{
return v___x_4950_;
}
}
}
}
else
{
lean_object* v_a_4953_; lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_4960_; 
lean_dec(v_structId_4893_);
lean_dec(v_id_4892_);
lean_del_object(v___x_4888_);
lean_dec(v_fst_4886_);
lean_dec_ref(v_b_4866_);
lean_dec_ref(v_a_4865_);
v_a_4953_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_4960_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4960_ == 0)
{
v___x_4955_ = v___x_4895_;
v_isShared_4956_ = v_isSharedCheck_4960_;
goto v_resetjp_4954_;
}
else
{
lean_inc(v_a_4953_);
lean_dec(v___x_4895_);
v___x_4955_ = lean_box(0);
v_isShared_4956_ = v_isSharedCheck_4960_;
goto v_resetjp_4954_;
}
v_resetjp_4954_:
{
lean_object* v___x_4958_; 
if (v_isShared_4956_ == 0)
{
v___x_4958_ = v___x_4955_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_a_4953_);
v___x_4958_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
return v___x_4958_;
}
}
}
}
else
{
lean_object* v_a_4961_; lean_object* v___x_4963_; uint8_t v_isShared_4964_; uint8_t v_isSharedCheck_4968_; 
lean_del_object(v___x_4888_);
lean_dec(v_fst_4886_);
lean_dec(v_fst_4883_);
lean_dec(v_a_4880_);
lean_dec_ref(v_b_4866_);
lean_dec_ref(v_a_4865_);
v_a_4961_ = lean_ctor_get(v___x_4890_, 0);
v_isSharedCheck_4968_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4968_ == 0)
{
v___x_4963_ = v___x_4890_;
v_isShared_4964_ = v_isSharedCheck_4968_;
goto v_resetjp_4962_;
}
else
{
lean_inc(v_a_4961_);
lean_dec(v___x_4890_);
v___x_4963_ = lean_box(0);
v_isShared_4964_ = v_isSharedCheck_4968_;
goto v_resetjp_4962_;
}
v_resetjp_4962_:
{
lean_object* v___x_4966_; 
if (v_isShared_4964_ == 0)
{
v___x_4966_ = v___x_4963_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_a_4961_);
v___x_4966_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
return v___x_4966_;
}
}
}
}
}
else
{
lean_object* v_a_4971_; lean_object* v___x_4973_; uint8_t v_isShared_4974_; uint8_t v_isSharedCheck_4978_; 
lean_dec(v_fst_4883_);
lean_dec(v_a_4880_);
lean_dec_ref(v_b_4866_);
lean_dec_ref(v_a_4865_);
v_a_4971_ = lean_ctor_get(v___x_4884_, 0);
v_isSharedCheck_4978_ = !lean_is_exclusive(v___x_4884_);
if (v_isSharedCheck_4978_ == 0)
{
v___x_4973_ = v___x_4884_;
v_isShared_4974_ = v_isSharedCheck_4978_;
goto v_resetjp_4972_;
}
else
{
lean_inc(v_a_4971_);
lean_dec(v___x_4884_);
v___x_4973_ = lean_box(0);
v_isShared_4974_ = v_isSharedCheck_4978_;
goto v_resetjp_4972_;
}
v_resetjp_4972_:
{
lean_object* v___x_4976_; 
if (v_isShared_4974_ == 0)
{
v___x_4976_ = v___x_4973_;
goto v_reusejp_4975_;
}
else
{
lean_object* v_reuseFailAlloc_4977_; 
v_reuseFailAlloc_4977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4977_, 0, v_a_4971_);
v___x_4976_ = v_reuseFailAlloc_4977_;
goto v_reusejp_4975_;
}
v_reusejp_4975_:
{
return v___x_4976_;
}
}
}
}
else
{
lean_object* v_a_4979_; lean_object* v___x_4981_; uint8_t v_isShared_4982_; uint8_t v_isSharedCheck_4986_; 
lean_dec(v_a_4880_);
lean_dec_ref(v_b_4866_);
lean_dec_ref(v_a_4865_);
v_a_4979_ = lean_ctor_get(v___x_4881_, 0);
v_isSharedCheck_4986_ = !lean_is_exclusive(v___x_4881_);
if (v_isSharedCheck_4986_ == 0)
{
v___x_4981_ = v___x_4881_;
v_isShared_4982_ = v_isSharedCheck_4986_;
goto v_resetjp_4980_;
}
else
{
lean_inc(v_a_4979_);
lean_dec(v___x_4881_);
v___x_4981_ = lean_box(0);
v_isShared_4982_ = v_isSharedCheck_4986_;
goto v_resetjp_4980_;
}
v_resetjp_4980_:
{
lean_object* v___x_4984_; 
if (v_isShared_4982_ == 0)
{
v___x_4984_ = v___x_4981_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_4985_; 
v_reuseFailAlloc_4985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4985_, 0, v_a_4979_);
v___x_4984_ = v_reuseFailAlloc_4985_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
return v___x_4984_;
}
}
}
}
else
{
lean_object* v_a_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_4994_; 
lean_dec_ref(v_b_4866_);
lean_dec_ref(v_a_4865_);
v_a_4987_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4994_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4994_ == 0)
{
v___x_4989_ = v___x_4879_;
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_a_4987_);
lean_dec(v___x_4879_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4992_; 
if (v_isShared_4990_ == 0)
{
v___x_4992_ = v___x_4989_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4993_; 
v_reuseFailAlloc_4993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4993_, 0, v_a_4987_);
v___x_4992_ = v_reuseFailAlloc_4993_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
return v___x_4992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27___boxed(lean_object* v_a_4995_, lean_object* v_b_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_){
_start:
{
lean_object* v_res_5009_; 
v_res_5009_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_4995_, v_b_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_);
lean_dec(v_a_5007_);
lean_dec_ref(v_a_5006_);
lean_dec(v_a_5005_);
lean_dec_ref(v_a_5004_);
lean_dec(v_a_5003_);
lean_dec_ref(v_a_5002_);
lean_dec(v_a_5001_);
lean_dec_ref(v_a_5000_);
lean_dec(v_a_4999_);
lean_dec(v_a_4998_);
lean_dec(v_a_4997_);
return v_res_5009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(lean_object* v_a_5010_, lean_object* v_b_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_, lean_object* v_a_5022_){
_start:
{
lean_object* v___x_5024_; 
v___x_5024_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_);
if (lean_obj_tag(v___x_5024_) == 0)
{
lean_object* v_a_5025_; lean_object* v___x_5026_; 
v_a_5025_ = lean_ctor_get(v___x_5024_, 0);
lean_inc(v_a_5025_);
lean_dec_ref_known(v___x_5024_, 1);
lean_inc_ref(v_a_5010_);
v___x_5026_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5010_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_);
if (lean_obj_tag(v___x_5026_) == 0)
{
lean_object* v_a_5027_; lean_object* v_fst_5028_; lean_object* v___x_5030_; uint8_t v_isShared_5031_; uint8_t v_isSharedCheck_5124_; 
v_a_5027_ = lean_ctor_get(v___x_5026_, 0);
lean_inc(v_a_5027_);
lean_dec_ref_known(v___x_5026_, 1);
v_fst_5028_ = lean_ctor_get(v_a_5027_, 0);
v_isSharedCheck_5124_ = !lean_is_exclusive(v_a_5027_);
if (v_isSharedCheck_5124_ == 0)
{
lean_object* v_unused_5125_; 
v_unused_5125_ = lean_ctor_get(v_a_5027_, 1);
lean_dec(v_unused_5125_);
v___x_5030_ = v_a_5027_;
v_isShared_5031_ = v_isSharedCheck_5124_;
goto v_resetjp_5029_;
}
else
{
lean_inc(v_fst_5028_);
lean_dec(v_a_5027_);
v___x_5030_ = lean_box(0);
v_isShared_5031_ = v_isSharedCheck_5124_;
goto v_resetjp_5029_;
}
v_resetjp_5029_:
{
lean_object* v___x_5032_; 
lean_inc_ref(v_b_5011_);
v___x_5032_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_);
if (lean_obj_tag(v___x_5032_) == 0)
{
lean_object* v_a_5033_; lean_object* v_fst_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5114_; 
v_a_5033_ = lean_ctor_get(v___x_5032_, 0);
lean_inc(v_a_5033_);
lean_dec_ref_known(v___x_5032_, 1);
v_fst_5034_ = lean_ctor_get(v_a_5033_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v_a_5033_);
if (v_isSharedCheck_5114_ == 0)
{
lean_object* v_unused_5115_; 
v_unused_5115_ = lean_ctor_get(v_a_5033_, 1);
lean_dec(v_unused_5115_);
v___x_5036_ = v_a_5033_;
v_isShared_5037_ = v_isSharedCheck_5114_;
goto v_resetjp_5035_;
}
else
{
lean_inc(v_fst_5034_);
lean_dec(v_a_5033_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5114_;
goto v_resetjp_5035_;
}
v_resetjp_5035_:
{
lean_object* v___x_5038_; 
v___x_5038_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5010_, v_a_5013_);
if (lean_obj_tag(v___x_5038_) == 0)
{
lean_object* v_a_5039_; lean_object* v_id_5040_; lean_object* v_structId_5041_; uint8_t v___x_5042_; lean_object* v___x_5043_; 
v_a_5039_ = lean_ctor_get(v___x_5038_, 0);
lean_inc(v_a_5039_);
lean_dec_ref_known(v___x_5038_, 1);
v_id_5040_ = lean_ctor_get(v_a_5025_, 0);
lean_inc(v_id_5040_);
v_structId_5041_ = lean_ctor_get(v_a_5025_, 1);
lean_inc(v_structId_5041_);
lean_dec(v_a_5025_);
v___x_5042_ = 0;
v___x_5043_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5028_, v___x_5042_, v_a_5039_, v_structId_5041_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_);
if (lean_obj_tag(v___x_5043_) == 0)
{
lean_object* v_a_5044_; lean_object* v___x_5046_; uint8_t v_isShared_5047_; uint8_t v_isSharedCheck_5097_; 
v_a_5044_ = lean_ctor_get(v___x_5043_, 0);
v_isSharedCheck_5097_ = !lean_is_exclusive(v___x_5043_);
if (v_isSharedCheck_5097_ == 0)
{
v___x_5046_ = v___x_5043_;
v_isShared_5047_ = v_isSharedCheck_5097_;
goto v_resetjp_5045_;
}
else
{
lean_inc(v_a_5044_);
lean_dec(v___x_5043_);
v___x_5046_ = lean_box(0);
v_isShared_5047_ = v_isSharedCheck_5097_;
goto v_resetjp_5045_;
}
v_resetjp_5045_:
{
if (lean_obj_tag(v_a_5044_) == 1)
{
lean_object* v_val_5048_; lean_object* v___x_5049_; 
lean_del_object(v___x_5046_);
v_val_5048_ = lean_ctor_get(v_a_5044_, 0);
lean_inc(v_val_5048_);
lean_dec_ref_known(v_a_5044_, 1);
v___x_5049_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5011_, v_a_5013_);
if (lean_obj_tag(v___x_5049_) == 0)
{
lean_object* v_a_5050_; lean_object* v___x_5051_; 
v_a_5050_ = lean_ctor_get(v___x_5049_, 0);
lean_inc(v_a_5050_);
lean_dec_ref_known(v___x_5049_, 1);
v___x_5051_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5034_, v___x_5042_, v_a_5050_, v_structId_5041_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_);
if (lean_obj_tag(v___x_5051_) == 0)
{
lean_object* v_a_5052_; lean_object* v___x_5054_; uint8_t v_isShared_5055_; uint8_t v_isSharedCheck_5076_; 
v_a_5052_ = lean_ctor_get(v___x_5051_, 0);
v_isSharedCheck_5076_ = !lean_is_exclusive(v___x_5051_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_5054_ = v___x_5051_;
v_isShared_5055_ = v_isSharedCheck_5076_;
goto v_resetjp_5053_;
}
else
{
lean_inc(v_a_5052_);
lean_dec(v___x_5051_);
v___x_5054_ = lean_box(0);
v_isShared_5055_ = v_isSharedCheck_5076_;
goto v_resetjp_5053_;
}
v_resetjp_5053_:
{
if (lean_obj_tag(v_a_5052_) == 1)
{
lean_object* v_val_5056_; lean_object* v___x_5058_; 
v_val_5056_ = lean_ctor_get(v_a_5052_, 0);
lean_inc_n(v_val_5056_, 2);
lean_dec_ref_known(v_a_5052_, 1);
lean_inc(v_val_5048_);
if (v_isShared_5037_ == 0)
{
lean_ctor_set_tag(v___x_5036_, 3);
lean_ctor_set(v___x_5036_, 1, v_val_5056_);
lean_ctor_set(v___x_5036_, 0, v_val_5048_);
v___x_5058_ = v___x_5036_;
goto v_reusejp_5057_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_val_5048_);
lean_ctor_set(v_reuseFailAlloc_5071_, 1, v_val_5056_);
v___x_5058_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5057_;
}
v_reusejp_5057_:
{
lean_object* v___x_5059_; lean_object* v___x_5060_; uint8_t v___x_5061_; 
v___x_5059_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5058_);
v___x_5060_ = lean_box(0);
v___x_5061_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_5059_, v___x_5060_);
if (v___x_5061_ == 0)
{
lean_object* v___x_5062_; lean_object* v___x_5064_; 
lean_del_object(v___x_5054_);
v___x_5062_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5062_, 0, v_a_5010_);
lean_ctor_set(v___x_5062_, 1, v_b_5011_);
lean_ctor_set(v___x_5062_, 2, v_id_5040_);
lean_ctor_set(v___x_5062_, 3, v_val_5048_);
lean_ctor_set(v___x_5062_, 4, v_val_5056_);
if (v_isShared_5031_ == 0)
{
lean_ctor_set(v___x_5030_, 1, v___x_5062_);
lean_ctor_set(v___x_5030_, 0, v___x_5059_);
v___x_5064_ = v___x_5030_;
goto v_reusejp_5063_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v___x_5059_);
lean_ctor_set(v_reuseFailAlloc_5066_, 1, v___x_5062_);
v___x_5064_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5063_;
}
v_reusejp_5063_:
{
lean_object* v___x_5065_; 
v___x_5065_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_5064_, v_structId_5041_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_);
lean_dec(v_structId_5041_);
return v___x_5065_;
}
}
else
{
lean_object* v___x_5067_; lean_object* v___x_5069_; 
lean_dec(v___x_5059_);
lean_dec(v_val_5056_);
lean_dec(v_val_5048_);
lean_dec(v_structId_5041_);
lean_dec(v_id_5040_);
lean_del_object(v___x_5030_);
lean_dec_ref(v_b_5011_);
lean_dec_ref(v_a_5010_);
v___x_5067_ = lean_box(0);
if (v_isShared_5055_ == 0)
{
lean_ctor_set(v___x_5054_, 0, v___x_5067_);
v___x_5069_ = v___x_5054_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5070_; 
v_reuseFailAlloc_5070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5070_, 0, v___x_5067_);
v___x_5069_ = v_reuseFailAlloc_5070_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
return v___x_5069_;
}
}
}
}
else
{
lean_object* v___x_5072_; lean_object* v___x_5074_; 
lean_dec(v_a_5052_);
lean_dec(v_val_5048_);
lean_dec(v_structId_5041_);
lean_dec(v_id_5040_);
lean_del_object(v___x_5036_);
lean_del_object(v___x_5030_);
lean_dec_ref(v_b_5011_);
lean_dec_ref(v_a_5010_);
v___x_5072_ = lean_box(0);
if (v_isShared_5055_ == 0)
{
lean_ctor_set(v___x_5054_, 0, v___x_5072_);
v___x_5074_ = v___x_5054_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v___x_5072_);
v___x_5074_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
return v___x_5074_;
}
}
}
}
else
{
lean_object* v_a_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5084_; 
lean_dec(v_val_5048_);
lean_dec(v_structId_5041_);
lean_dec(v_id_5040_);
lean_del_object(v___x_5036_);
lean_del_object(v___x_5030_);
lean_dec_ref(v_b_5011_);
lean_dec_ref(v_a_5010_);
v_a_5077_ = lean_ctor_get(v___x_5051_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5051_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5079_ = v___x_5051_;
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_a_5077_);
lean_dec(v___x_5051_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v___x_5082_; 
if (v_isShared_5080_ == 0)
{
v___x_5082_ = v___x_5079_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_a_5077_);
v___x_5082_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
return v___x_5082_;
}
}
}
}
else
{
lean_object* v_a_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5092_; 
lean_dec(v_val_5048_);
lean_dec(v_structId_5041_);
lean_dec(v_id_5040_);
lean_del_object(v___x_5036_);
lean_dec(v_fst_5034_);
lean_del_object(v___x_5030_);
lean_dec_ref(v_b_5011_);
lean_dec_ref(v_a_5010_);
v_a_5085_ = lean_ctor_get(v___x_5049_, 0);
v_isSharedCheck_5092_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5092_ == 0)
{
v___x_5087_ = v___x_5049_;
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_a_5085_);
lean_dec(v___x_5049_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
lean_object* v___x_5090_; 
if (v_isShared_5088_ == 0)
{
v___x_5090_ = v___x_5087_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_a_5085_);
v___x_5090_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
return v___x_5090_;
}
}
}
}
else
{
lean_object* v___x_5093_; lean_object* v___x_5095_; 
lean_dec(v_a_5044_);
lean_dec(v_structId_5041_);
lean_dec(v_id_5040_);
lean_del_object(v___x_5036_);
lean_dec(v_fst_5034_);
lean_del_object(v___x_5030_);
lean_dec_ref(v_b_5011_);
lean_dec_ref(v_a_5010_);
v___x_5093_ = lean_box(0);
if (v_isShared_5047_ == 0)
{
lean_ctor_set(v___x_5046_, 0, v___x_5093_);
v___x_5095_ = v___x_5046_;
goto v_reusejp_5094_;
}
else
{
lean_object* v_reuseFailAlloc_5096_; 
v_reuseFailAlloc_5096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5096_, 0, v___x_5093_);
v___x_5095_ = v_reuseFailAlloc_5096_;
goto v_reusejp_5094_;
}
v_reusejp_5094_:
{
return v___x_5095_;
}
}
}
}
else
{
lean_object* v_a_5098_; lean_object* v___x_5100_; uint8_t v_isShared_5101_; uint8_t v_isSharedCheck_5105_; 
lean_dec(v_structId_5041_);
lean_dec(v_id_5040_);
lean_del_object(v___x_5036_);
lean_dec(v_fst_5034_);
lean_del_object(v___x_5030_);
lean_dec_ref(v_b_5011_);
lean_dec_ref(v_a_5010_);
v_a_5098_ = lean_ctor_get(v___x_5043_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_5043_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5100_ = v___x_5043_;
v_isShared_5101_ = v_isSharedCheck_5105_;
goto v_resetjp_5099_;
}
else
{
lean_inc(v_a_5098_);
lean_dec(v___x_5043_);
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
lean_object* v_a_5106_; lean_object* v___x_5108_; uint8_t v_isShared_5109_; uint8_t v_isSharedCheck_5113_; 
lean_del_object(v___x_5036_);
lean_dec(v_fst_5034_);
lean_del_object(v___x_5030_);
lean_dec(v_fst_5028_);
lean_dec(v_a_5025_);
lean_dec_ref(v_b_5011_);
lean_dec_ref(v_a_5010_);
v_a_5106_ = lean_ctor_get(v___x_5038_, 0);
v_isSharedCheck_5113_ = !lean_is_exclusive(v___x_5038_);
if (v_isSharedCheck_5113_ == 0)
{
v___x_5108_ = v___x_5038_;
v_isShared_5109_ = v_isSharedCheck_5113_;
goto v_resetjp_5107_;
}
else
{
lean_inc(v_a_5106_);
lean_dec(v___x_5038_);
v___x_5108_ = lean_box(0);
v_isShared_5109_ = v_isSharedCheck_5113_;
goto v_resetjp_5107_;
}
v_resetjp_5107_:
{
lean_object* v___x_5111_; 
if (v_isShared_5109_ == 0)
{
v___x_5111_ = v___x_5108_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v_a_5106_);
v___x_5111_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5110_;
}
v_reusejp_5110_:
{
return v___x_5111_;
}
}
}
}
}
else
{
lean_object* v_a_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5123_; 
lean_del_object(v___x_5030_);
lean_dec(v_fst_5028_);
lean_dec(v_a_5025_);
lean_dec_ref(v_b_5011_);
lean_dec_ref(v_a_5010_);
v_a_5116_ = lean_ctor_get(v___x_5032_, 0);
v_isSharedCheck_5123_ = !lean_is_exclusive(v___x_5032_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_5118_ = v___x_5032_;
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
else
{
lean_inc(v_a_5116_);
lean_dec(v___x_5032_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v___x_5121_; 
if (v_isShared_5119_ == 0)
{
v___x_5121_ = v___x_5118_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v_a_5116_);
v___x_5121_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
return v___x_5121_;
}
}
}
}
}
else
{
lean_object* v_a_5126_; lean_object* v___x_5128_; uint8_t v_isShared_5129_; uint8_t v_isSharedCheck_5133_; 
lean_dec(v_a_5025_);
lean_dec_ref(v_b_5011_);
lean_dec_ref(v_a_5010_);
v_a_5126_ = lean_ctor_get(v___x_5026_, 0);
v_isSharedCheck_5133_ = !lean_is_exclusive(v___x_5026_);
if (v_isSharedCheck_5133_ == 0)
{
v___x_5128_ = v___x_5026_;
v_isShared_5129_ = v_isSharedCheck_5133_;
goto v_resetjp_5127_;
}
else
{
lean_inc(v_a_5126_);
lean_dec(v___x_5026_);
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
lean_object* v_a_5134_; lean_object* v___x_5136_; uint8_t v_isShared_5137_; uint8_t v_isSharedCheck_5141_; 
lean_dec_ref(v_b_5011_);
lean_dec_ref(v_a_5010_);
v_a_5134_ = lean_ctor_get(v___x_5024_, 0);
v_isSharedCheck_5141_ = !lean_is_exclusive(v___x_5024_);
if (v_isSharedCheck_5141_ == 0)
{
v___x_5136_ = v___x_5024_;
v_isShared_5137_ = v_isSharedCheck_5141_;
goto v_resetjp_5135_;
}
else
{
lean_inc(v_a_5134_);
lean_dec(v___x_5024_);
v___x_5136_ = lean_box(0);
v_isShared_5137_ = v_isSharedCheck_5141_;
goto v_resetjp_5135_;
}
v_resetjp_5135_:
{
lean_object* v___x_5139_; 
if (v_isShared_5137_ == 0)
{
v___x_5139_ = v___x_5136_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5140_; 
v_reuseFailAlloc_5140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5140_, 0, v_a_5134_);
v___x_5139_ = v_reuseFailAlloc_5140_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
return v___x_5139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq___boxed(lean_object* v_a_5142_, lean_object* v_b_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_){
_start:
{
lean_object* v_res_5156_; 
v_res_5156_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5142_, v_b_5143_, v_a_5144_, v_a_5145_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_);
lean_dec(v_a_5154_);
lean_dec_ref(v_a_5153_);
lean_dec(v_a_5152_);
lean_dec_ref(v_a_5151_);
lean_dec(v_a_5150_);
lean_dec_ref(v_a_5149_);
lean_dec(v_a_5148_);
lean_dec_ref(v_a_5147_);
lean_dec(v_a_5146_);
lean_dec(v_a_5145_);
lean_dec(v_a_5144_);
return v_res_5156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq(lean_object* v_a_5157_, lean_object* v_b_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_){
_start:
{
uint8_t v___x_5170_; 
v___x_5170_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_5157_, v_b_5158_);
if (v___x_5170_ == 0)
{
lean_object* v___x_5171_; 
v___x_5171_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5157_, v_b_5158_, v_a_5159_, v_a_5167_);
if (lean_obj_tag(v___x_5171_) == 0)
{
lean_object* v_a_5172_; 
v_a_5172_ = lean_ctor_get(v___x_5171_, 0);
lean_inc(v_a_5172_);
lean_dec_ref_known(v___x_5171_, 1);
if (lean_obj_tag(v_a_5172_) == 1)
{
lean_object* v_val_5173_; lean_object* v___x_5174_; 
v_val_5173_ = lean_ctor_get(v_a_5172_, 0);
lean_inc(v_val_5173_);
lean_dec_ref_known(v_a_5172_, 1);
v___x_5174_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_val_5173_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_);
if (lean_obj_tag(v___x_5174_) == 0)
{
lean_object* v_a_5175_; uint8_t v___x_5176_; 
v_a_5175_ = lean_ctor_get(v___x_5174_, 0);
lean_inc(v_a_5175_);
lean_dec_ref_known(v___x_5174_, 1);
v___x_5176_ = lean_unbox(v_a_5175_);
lean_dec(v_a_5175_);
if (v___x_5176_ == 0)
{
lean_object* v___x_5177_; 
v___x_5177_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5173_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_);
if (lean_obj_tag(v___x_5177_) == 0)
{
lean_object* v_a_5178_; uint8_t v___x_5179_; 
v_a_5178_ = lean_ctor_get(v___x_5177_, 0);
lean_inc(v_a_5178_);
lean_dec_ref_known(v___x_5177_, 1);
v___x_5179_ = lean_unbox(v_a_5178_);
lean_dec(v_a_5178_);
if (v___x_5179_ == 0)
{
lean_object* v___x_5180_; 
v___x_5180_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_5157_, v_b_5158_, v_val_5173_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_);
lean_dec(v_val_5173_);
return v___x_5180_;
}
else
{
lean_object* v___x_5181_; 
lean_dec(v_val_5173_);
v___x_5181_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_5157_, v_b_5158_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_);
return v___x_5181_;
}
}
else
{
lean_object* v_a_5182_; lean_object* v___x_5184_; uint8_t v_isShared_5185_; uint8_t v_isSharedCheck_5189_; 
lean_dec(v_val_5173_);
lean_dec_ref(v_b_5158_);
lean_dec_ref(v_a_5157_);
v_a_5182_ = lean_ctor_get(v___x_5177_, 0);
v_isSharedCheck_5189_ = !lean_is_exclusive(v___x_5177_);
if (v_isSharedCheck_5189_ == 0)
{
v___x_5184_ = v___x_5177_;
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
else
{
lean_inc(v_a_5182_);
lean_dec(v___x_5177_);
v___x_5184_ = lean_box(0);
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
v_resetjp_5183_:
{
lean_object* v___x_5187_; 
if (v_isShared_5185_ == 0)
{
v___x_5187_ = v___x_5184_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v_a_5182_);
v___x_5187_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5186_;
}
v_reusejp_5186_:
{
return v___x_5187_;
}
}
}
}
else
{
lean_object* v___x_5190_; 
v___x_5190_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5173_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_);
if (lean_obj_tag(v___x_5190_) == 0)
{
lean_object* v_a_5191_; uint8_t v___x_5192_; 
v_a_5191_ = lean_ctor_get(v___x_5190_, 0);
lean_inc(v_a_5191_);
lean_dec_ref_known(v___x_5190_, 1);
v___x_5192_ = lean_unbox(v_a_5191_);
lean_dec(v_a_5191_);
if (v___x_5192_ == 0)
{
lean_object* v___x_5193_; 
v___x_5193_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_5157_, v_b_5158_, v_val_5173_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_);
lean_dec(v_val_5173_);
return v___x_5193_;
}
else
{
lean_object* v___x_5194_; 
v___x_5194_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_5157_, v_b_5158_, v_val_5173_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_);
lean_dec(v_val_5173_);
return v___x_5194_;
}
}
else
{
lean_object* v_a_5195_; lean_object* v___x_5197_; uint8_t v_isShared_5198_; uint8_t v_isSharedCheck_5202_; 
lean_dec(v_val_5173_);
lean_dec_ref(v_b_5158_);
lean_dec_ref(v_a_5157_);
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
}
else
{
lean_object* v_a_5203_; lean_object* v___x_5205_; uint8_t v_isShared_5206_; uint8_t v_isSharedCheck_5210_; 
lean_dec(v_val_5173_);
lean_dec_ref(v_b_5158_);
lean_dec_ref(v_a_5157_);
v_a_5203_ = lean_ctor_get(v___x_5174_, 0);
v_isSharedCheck_5210_ = !lean_is_exclusive(v___x_5174_);
if (v_isSharedCheck_5210_ == 0)
{
v___x_5205_ = v___x_5174_;
v_isShared_5206_ = v_isSharedCheck_5210_;
goto v_resetjp_5204_;
}
else
{
lean_inc(v_a_5203_);
lean_dec(v___x_5174_);
v___x_5205_ = lean_box(0);
v_isShared_5206_ = v_isSharedCheck_5210_;
goto v_resetjp_5204_;
}
v_resetjp_5204_:
{
lean_object* v___x_5208_; 
if (v_isShared_5206_ == 0)
{
v___x_5208_ = v___x_5205_;
goto v_reusejp_5207_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v_a_5203_);
v___x_5208_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5207_;
}
v_reusejp_5207_:
{
return v___x_5208_;
}
}
}
}
else
{
lean_object* v___x_5211_; 
lean_dec(v_a_5172_);
v___x_5211_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5157_, v_b_5158_, v_a_5159_, v_a_5167_);
if (lean_obj_tag(v___x_5211_) == 0)
{
lean_object* v_a_5212_; lean_object* v___x_5214_; uint8_t v_isShared_5215_; uint8_t v_isSharedCheck_5234_; 
v_a_5212_ = lean_ctor_get(v___x_5211_, 0);
v_isSharedCheck_5234_ = !lean_is_exclusive(v___x_5211_);
if (v_isSharedCheck_5234_ == 0)
{
v___x_5214_ = v___x_5211_;
v_isShared_5215_ = v_isSharedCheck_5234_;
goto v_resetjp_5213_;
}
else
{
lean_inc(v_a_5212_);
lean_dec(v___x_5211_);
v___x_5214_ = lean_box(0);
v_isShared_5215_ = v_isSharedCheck_5234_;
goto v_resetjp_5213_;
}
v_resetjp_5213_:
{
if (lean_obj_tag(v_a_5212_) == 1)
{
lean_object* v_val_5216_; lean_object* v___x_5217_; 
lean_del_object(v___x_5214_);
v_val_5216_ = lean_ctor_get(v_a_5212_, 0);
lean_inc(v_val_5216_);
lean_dec_ref_known(v_a_5212_, 1);
v___x_5217_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_5216_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_);
if (lean_obj_tag(v___x_5217_) == 0)
{
lean_object* v_a_5218_; lean_object* v_orderedAddInst_x3f_5219_; 
v_a_5218_ = lean_ctor_get(v___x_5217_, 0);
lean_inc(v_a_5218_);
lean_dec_ref_known(v___x_5217_, 1);
v_orderedAddInst_x3f_5219_ = lean_ctor_get(v_a_5218_, 9);
lean_inc(v_orderedAddInst_x3f_5219_);
lean_dec(v_a_5218_);
if (lean_obj_tag(v_orderedAddInst_x3f_5219_) == 0)
{
lean_object* v___x_5220_; 
v___x_5220_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5157_, v_b_5158_, v_val_5216_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_);
lean_dec(v_val_5216_);
return v___x_5220_;
}
else
{
lean_object* v___x_5221_; 
lean_dec_ref_known(v_orderedAddInst_x3f_5219_, 1);
v___x_5221_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5157_, v_b_5158_, v_val_5216_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_);
lean_dec(v_val_5216_);
return v___x_5221_;
}
}
else
{
lean_object* v_a_5222_; lean_object* v___x_5224_; uint8_t v_isShared_5225_; uint8_t v_isSharedCheck_5229_; 
lean_dec(v_val_5216_);
lean_dec_ref(v_b_5158_);
lean_dec_ref(v_a_5157_);
v_a_5222_ = lean_ctor_get(v___x_5217_, 0);
v_isSharedCheck_5229_ = !lean_is_exclusive(v___x_5217_);
if (v_isSharedCheck_5229_ == 0)
{
v___x_5224_ = v___x_5217_;
v_isShared_5225_ = v_isSharedCheck_5229_;
goto v_resetjp_5223_;
}
else
{
lean_inc(v_a_5222_);
lean_dec(v___x_5217_);
v___x_5224_ = lean_box(0);
v_isShared_5225_ = v_isSharedCheck_5229_;
goto v_resetjp_5223_;
}
v_resetjp_5223_:
{
lean_object* v___x_5227_; 
if (v_isShared_5225_ == 0)
{
v___x_5227_ = v___x_5224_;
goto v_reusejp_5226_;
}
else
{
lean_object* v_reuseFailAlloc_5228_; 
v_reuseFailAlloc_5228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5228_, 0, v_a_5222_);
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
lean_object* v___x_5230_; lean_object* v___x_5232_; 
lean_dec(v_a_5212_);
lean_dec_ref(v_b_5158_);
lean_dec_ref(v_a_5157_);
v___x_5230_ = lean_box(0);
if (v_isShared_5215_ == 0)
{
lean_ctor_set(v___x_5214_, 0, v___x_5230_);
v___x_5232_ = v___x_5214_;
goto v_reusejp_5231_;
}
else
{
lean_object* v_reuseFailAlloc_5233_; 
v_reuseFailAlloc_5233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5233_, 0, v___x_5230_);
v___x_5232_ = v_reuseFailAlloc_5233_;
goto v_reusejp_5231_;
}
v_reusejp_5231_:
{
return v___x_5232_;
}
}
}
}
else
{
lean_object* v_a_5235_; lean_object* v___x_5237_; uint8_t v_isShared_5238_; uint8_t v_isSharedCheck_5242_; 
lean_dec_ref(v_b_5158_);
lean_dec_ref(v_a_5157_);
v_a_5235_ = lean_ctor_get(v___x_5211_, 0);
v_isSharedCheck_5242_ = !lean_is_exclusive(v___x_5211_);
if (v_isSharedCheck_5242_ == 0)
{
v___x_5237_ = v___x_5211_;
v_isShared_5238_ = v_isSharedCheck_5242_;
goto v_resetjp_5236_;
}
else
{
lean_inc(v_a_5235_);
lean_dec(v___x_5211_);
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
}
else
{
lean_object* v_a_5243_; lean_object* v___x_5245_; uint8_t v_isShared_5246_; uint8_t v_isSharedCheck_5250_; 
lean_dec_ref(v_b_5158_);
lean_dec_ref(v_a_5157_);
v_a_5243_ = lean_ctor_get(v___x_5171_, 0);
v_isSharedCheck_5250_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5250_ == 0)
{
v___x_5245_ = v___x_5171_;
v_isShared_5246_ = v_isSharedCheck_5250_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_a_5243_);
lean_dec(v___x_5171_);
v___x_5245_ = lean_box(0);
v_isShared_5246_ = v_isSharedCheck_5250_;
goto v_resetjp_5244_;
}
v_resetjp_5244_:
{
lean_object* v___x_5248_; 
if (v_isShared_5246_ == 0)
{
v___x_5248_ = v___x_5245_;
goto v_reusejp_5247_;
}
else
{
lean_object* v_reuseFailAlloc_5249_; 
v_reuseFailAlloc_5249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5249_, 0, v_a_5243_);
v___x_5248_ = v_reuseFailAlloc_5249_;
goto v_reusejp_5247_;
}
v_reusejp_5247_:
{
return v___x_5248_;
}
}
}
}
else
{
lean_object* v___x_5251_; lean_object* v___x_5252_; 
lean_dec_ref(v_b_5158_);
lean_dec_ref(v_a_5157_);
v___x_5251_ = lean_box(0);
v___x_5252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5252_, 0, v___x_5251_);
return v___x_5252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed(lean_object* v_a_5253_, lean_object* v_b_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_){
_start:
{
lean_object* v_res_5266_; 
v_res_5266_ = l_Lean_Meta_Grind_Arith_Linear_processNewEq(v_a_5253_, v_b_5254_, v_a_5255_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_);
lean_dec(v_a_5264_);
lean_dec_ref(v_a_5263_);
lean_dec(v_a_5262_);
lean_dec_ref(v_a_5261_);
lean_dec(v_a_5260_);
lean_dec_ref(v_a_5259_);
lean_dec(v_a_5258_);
lean_dec_ref(v_a_5257_);
lean_dec(v_a_5256_);
lean_dec(v_a_5255_);
return v_res_5266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object* v_a_5267_, lean_object* v_b_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_, lean_object* v_a_5276_, lean_object* v_a_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_){
_start:
{
uint8_t v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; 
v___x_5281_ = 0;
v___x_5282_ = lean_unsigned_to_nat(0u);
v___x_5283_ = lean_box(v___x_5281_);
lean_inc_ref(v_a_5267_);
v___x_5284_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5284_, 0, v_a_5267_);
lean_closure_set(v___x_5284_, 1, v___x_5283_);
lean_closure_set(v___x_5284_, 2, v___x_5282_);
v___x_5285_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5284_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_);
if (lean_obj_tag(v___x_5285_) == 0)
{
lean_object* v_a_5286_; lean_object* v___x_5288_; uint8_t v_isShared_5289_; uint8_t v_isSharedCheck_5387_; 
v_a_5286_ = lean_ctor_get(v___x_5285_, 0);
v_isSharedCheck_5387_ = !lean_is_exclusive(v___x_5285_);
if (v_isSharedCheck_5387_ == 0)
{
v___x_5288_ = v___x_5285_;
v_isShared_5289_ = v_isSharedCheck_5387_;
goto v_resetjp_5287_;
}
else
{
lean_inc(v_a_5286_);
lean_dec(v___x_5285_);
v___x_5288_ = lean_box(0);
v_isShared_5289_ = v_isSharedCheck_5387_;
goto v_resetjp_5287_;
}
v_resetjp_5287_:
{
if (lean_obj_tag(v_a_5286_) == 1)
{
lean_object* v_val_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; 
lean_del_object(v___x_5288_);
v_val_5290_ = lean_ctor_get(v_a_5286_, 0);
lean_inc(v_val_5290_);
lean_dec_ref_known(v_a_5286_, 1);
v___x_5291_ = lean_box(v___x_5281_);
lean_inc_ref(v_b_5268_);
v___x_5292_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5292_, 0, v_b_5268_);
lean_closure_set(v___x_5292_, 1, v___x_5291_);
lean_closure_set(v___x_5292_, 2, v___x_5282_);
v___x_5293_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5292_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_);
if (lean_obj_tag(v___x_5293_) == 0)
{
lean_object* v_a_5294_; lean_object* v___x_5296_; uint8_t v_isShared_5297_; uint8_t v_isSharedCheck_5374_; 
v_a_5294_ = lean_ctor_get(v___x_5293_, 0);
v_isSharedCheck_5374_ = !lean_is_exclusive(v___x_5293_);
if (v_isSharedCheck_5374_ == 0)
{
v___x_5296_ = v___x_5293_;
v_isShared_5297_ = v_isSharedCheck_5374_;
goto v_resetjp_5295_;
}
else
{
lean_inc(v_a_5294_);
lean_dec(v___x_5293_);
v___x_5296_ = lean_box(0);
v_isShared_5297_ = v_isSharedCheck_5374_;
goto v_resetjp_5295_;
}
v_resetjp_5295_:
{
if (lean_obj_tag(v_a_5294_) == 1)
{
lean_object* v_val_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; 
lean_del_object(v___x_5296_);
v_val_5298_ = lean_ctor_get(v_a_5294_, 0);
lean_inc_n(v_val_5298_, 2);
lean_dec_ref_known(v_a_5294_, 1);
lean_inc(v_val_5290_);
v___x_5299_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_5299_, 0, v_val_5290_);
lean_ctor_set(v___x_5299_, 1, v_val_5298_);
v___x_5300_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_5299_);
lean_inc_ref(v_b_5268_);
lean_inc_ref(v_a_5267_);
v___x_5301_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5301_, 0, v_a_5267_);
lean_ctor_set(v___x_5301_, 1, v_b_5268_);
lean_ctor_set(v___x_5301_, 2, v_val_5290_);
lean_ctor_set(v___x_5301_, 3, v_val_5298_);
v___x_5302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5302_, 0, v___x_5300_);
lean_ctor_set(v___x_5302_, 1, v___x_5301_);
v___x_5303_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(v___x_5302_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_);
if (lean_obj_tag(v___x_5303_) == 0)
{
lean_object* v_a_5304_; lean_object* v___x_5305_; 
v_a_5304_ = lean_ctor_get(v___x_5303_, 0);
lean_inc(v_a_5304_);
lean_dec_ref_known(v___x_5303_, 1);
v___x_5305_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5267_, v_a_5270_);
lean_dec_ref(v_a_5267_);
if (lean_obj_tag(v___x_5305_) == 0)
{
lean_object* v_a_5306_; lean_object* v___x_5307_; 
v_a_5306_ = lean_ctor_get(v___x_5305_, 0);
lean_inc(v_a_5306_);
lean_dec_ref_known(v___x_5305_, 1);
v___x_5307_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5268_, v_a_5270_);
lean_dec_ref(v_b_5268_);
if (lean_obj_tag(v___x_5307_) == 0)
{
lean_object* v_a_5308_; lean_object* v_p_5309_; lean_object* v___y_5311_; uint8_t v___x_5345_; 
v_a_5308_ = lean_ctor_get(v___x_5307_, 0);
lean_inc(v_a_5308_);
lean_dec_ref_known(v___x_5307_, 1);
v_p_5309_ = lean_ctor_get(v_a_5304_, 0);
v___x_5345_ = lean_nat_dec_le(v_a_5306_, v_a_5308_);
if (v___x_5345_ == 0)
{
lean_dec(v_a_5308_);
v___y_5311_ = v_a_5306_;
goto v___jp_5310_;
}
else
{
lean_dec(v_a_5306_);
v___y_5311_ = v_a_5308_;
goto v___jp_5310_;
}
v___jp_5310_:
{
lean_object* v___x_5312_; 
lean_inc(v___y_5311_);
lean_inc_ref(v_p_5309_);
v___x_5312_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_5309_, v___y_5311_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_);
if (lean_obj_tag(v___x_5312_) == 0)
{
lean_object* v_a_5313_; lean_object* v___x_5314_; 
v_a_5313_ = lean_ctor_get(v___x_5312_, 0);
lean_inc(v_a_5313_);
lean_dec_ref_known(v___x_5312_, 1);
v___x_5314_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5313_, v___x_5281_, v___y_5311_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_);
if (lean_obj_tag(v___x_5314_) == 0)
{
lean_object* v_a_5315_; lean_object* v___x_5317_; uint8_t v_isShared_5318_; uint8_t v_isSharedCheck_5328_; 
v_a_5315_ = lean_ctor_get(v___x_5314_, 0);
v_isSharedCheck_5328_ = !lean_is_exclusive(v___x_5314_);
if (v_isSharedCheck_5328_ == 0)
{
v___x_5317_ = v___x_5314_;
v_isShared_5318_ = v_isSharedCheck_5328_;
goto v_resetjp_5316_;
}
else
{
lean_inc(v_a_5315_);
lean_dec(v___x_5314_);
v___x_5317_ = lean_box(0);
v_isShared_5318_ = v_isSharedCheck_5328_;
goto v_resetjp_5316_;
}
v_resetjp_5316_:
{
if (lean_obj_tag(v_a_5315_) == 1)
{
lean_object* v_val_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; 
lean_del_object(v___x_5317_);
v_val_5319_ = lean_ctor_get(v_a_5315_, 0);
lean_inc_n(v_val_5319_, 2);
lean_dec_ref_known(v_a_5315_, 1);
v___x_5320_ = l_Lean_Grind_Linarith_Expr_norm(v_val_5319_);
v___x_5321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5321_, 0, v_a_5304_);
lean_ctor_set(v___x_5321_, 1, v_val_5319_);
v___x_5322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5322_, 0, v___x_5320_);
lean_ctor_set(v___x_5322_, 1, v___x_5321_);
v___x_5323_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5322_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_);
return v___x_5323_;
}
else
{
lean_object* v___x_5324_; lean_object* v___x_5326_; 
lean_dec(v_a_5315_);
lean_dec(v_a_5304_);
v___x_5324_ = lean_box(0);
if (v_isShared_5318_ == 0)
{
lean_ctor_set(v___x_5317_, 0, v___x_5324_);
v___x_5326_ = v___x_5317_;
goto v_reusejp_5325_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v___x_5324_);
v___x_5326_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5325_;
}
v_reusejp_5325_:
{
return v___x_5326_;
}
}
}
}
else
{
lean_object* v_a_5329_; lean_object* v___x_5331_; uint8_t v_isShared_5332_; uint8_t v_isSharedCheck_5336_; 
lean_dec(v_a_5304_);
v_a_5329_ = lean_ctor_get(v___x_5314_, 0);
v_isSharedCheck_5336_ = !lean_is_exclusive(v___x_5314_);
if (v_isSharedCheck_5336_ == 0)
{
v___x_5331_ = v___x_5314_;
v_isShared_5332_ = v_isSharedCheck_5336_;
goto v_resetjp_5330_;
}
else
{
lean_inc(v_a_5329_);
lean_dec(v___x_5314_);
v___x_5331_ = lean_box(0);
v_isShared_5332_ = v_isSharedCheck_5336_;
goto v_resetjp_5330_;
}
v_resetjp_5330_:
{
lean_object* v___x_5334_; 
if (v_isShared_5332_ == 0)
{
v___x_5334_ = v___x_5331_;
goto v_reusejp_5333_;
}
else
{
lean_object* v_reuseFailAlloc_5335_; 
v_reuseFailAlloc_5335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5335_, 0, v_a_5329_);
v___x_5334_ = v_reuseFailAlloc_5335_;
goto v_reusejp_5333_;
}
v_reusejp_5333_:
{
return v___x_5334_;
}
}
}
}
else
{
lean_object* v_a_5337_; lean_object* v___x_5339_; uint8_t v_isShared_5340_; uint8_t v_isSharedCheck_5344_; 
lean_dec(v___y_5311_);
lean_dec(v_a_5304_);
v_a_5337_ = lean_ctor_get(v___x_5312_, 0);
v_isSharedCheck_5344_ = !lean_is_exclusive(v___x_5312_);
if (v_isSharedCheck_5344_ == 0)
{
v___x_5339_ = v___x_5312_;
v_isShared_5340_ = v_isSharedCheck_5344_;
goto v_resetjp_5338_;
}
else
{
lean_inc(v_a_5337_);
lean_dec(v___x_5312_);
v___x_5339_ = lean_box(0);
v_isShared_5340_ = v_isSharedCheck_5344_;
goto v_resetjp_5338_;
}
v_resetjp_5338_:
{
lean_object* v___x_5342_; 
if (v_isShared_5340_ == 0)
{
v___x_5342_ = v___x_5339_;
goto v_reusejp_5341_;
}
else
{
lean_object* v_reuseFailAlloc_5343_; 
v_reuseFailAlloc_5343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5343_, 0, v_a_5337_);
v___x_5342_ = v_reuseFailAlloc_5343_;
goto v_reusejp_5341_;
}
v_reusejp_5341_:
{
return v___x_5342_;
}
}
}
}
}
else
{
lean_object* v_a_5346_; lean_object* v___x_5348_; uint8_t v_isShared_5349_; uint8_t v_isSharedCheck_5353_; 
lean_dec(v_a_5306_);
lean_dec(v_a_5304_);
v_a_5346_ = lean_ctor_get(v___x_5307_, 0);
v_isSharedCheck_5353_ = !lean_is_exclusive(v___x_5307_);
if (v_isSharedCheck_5353_ == 0)
{
v___x_5348_ = v___x_5307_;
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
else
{
lean_inc(v_a_5346_);
lean_dec(v___x_5307_);
v___x_5348_ = lean_box(0);
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
v_resetjp_5347_:
{
lean_object* v___x_5351_; 
if (v_isShared_5349_ == 0)
{
v___x_5351_ = v___x_5348_;
goto v_reusejp_5350_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v_a_5346_);
v___x_5351_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5350_;
}
v_reusejp_5350_:
{
return v___x_5351_;
}
}
}
}
else
{
lean_object* v_a_5354_; lean_object* v___x_5356_; uint8_t v_isShared_5357_; uint8_t v_isSharedCheck_5361_; 
lean_dec(v_a_5304_);
lean_dec_ref(v_b_5268_);
v_a_5354_ = lean_ctor_get(v___x_5305_, 0);
v_isSharedCheck_5361_ = !lean_is_exclusive(v___x_5305_);
if (v_isSharedCheck_5361_ == 0)
{
v___x_5356_ = v___x_5305_;
v_isShared_5357_ = v_isSharedCheck_5361_;
goto v_resetjp_5355_;
}
else
{
lean_inc(v_a_5354_);
lean_dec(v___x_5305_);
v___x_5356_ = lean_box(0);
v_isShared_5357_ = v_isSharedCheck_5361_;
goto v_resetjp_5355_;
}
v_resetjp_5355_:
{
lean_object* v___x_5359_; 
if (v_isShared_5357_ == 0)
{
v___x_5359_ = v___x_5356_;
goto v_reusejp_5358_;
}
else
{
lean_object* v_reuseFailAlloc_5360_; 
v_reuseFailAlloc_5360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5360_, 0, v_a_5354_);
v___x_5359_ = v_reuseFailAlloc_5360_;
goto v_reusejp_5358_;
}
v_reusejp_5358_:
{
return v___x_5359_;
}
}
}
}
else
{
lean_object* v_a_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5369_; 
lean_dec_ref(v_b_5268_);
lean_dec_ref(v_a_5267_);
v_a_5362_ = lean_ctor_get(v___x_5303_, 0);
v_isSharedCheck_5369_ = !lean_is_exclusive(v___x_5303_);
if (v_isSharedCheck_5369_ == 0)
{
v___x_5364_ = v___x_5303_;
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_a_5362_);
lean_dec(v___x_5303_);
v___x_5364_ = lean_box(0);
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
v_resetjp_5363_:
{
lean_object* v___x_5367_; 
if (v_isShared_5365_ == 0)
{
v___x_5367_ = v___x_5364_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v_a_5362_);
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
lean_object* v___x_5370_; lean_object* v___x_5372_; 
lean_dec(v_a_5294_);
lean_dec(v_val_5290_);
lean_dec_ref(v_b_5268_);
lean_dec_ref(v_a_5267_);
v___x_5370_ = lean_box(0);
if (v_isShared_5297_ == 0)
{
lean_ctor_set(v___x_5296_, 0, v___x_5370_);
v___x_5372_ = v___x_5296_;
goto v_reusejp_5371_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v___x_5370_);
v___x_5372_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5371_;
}
v_reusejp_5371_:
{
return v___x_5372_;
}
}
}
}
else
{
lean_object* v_a_5375_; lean_object* v___x_5377_; uint8_t v_isShared_5378_; uint8_t v_isSharedCheck_5382_; 
lean_dec(v_val_5290_);
lean_dec_ref(v_b_5268_);
lean_dec_ref(v_a_5267_);
v_a_5375_ = lean_ctor_get(v___x_5293_, 0);
v_isSharedCheck_5382_ = !lean_is_exclusive(v___x_5293_);
if (v_isSharedCheck_5382_ == 0)
{
v___x_5377_ = v___x_5293_;
v_isShared_5378_ = v_isSharedCheck_5382_;
goto v_resetjp_5376_;
}
else
{
lean_inc(v_a_5375_);
lean_dec(v___x_5293_);
v___x_5377_ = lean_box(0);
v_isShared_5378_ = v_isSharedCheck_5382_;
goto v_resetjp_5376_;
}
v_resetjp_5376_:
{
lean_object* v___x_5380_; 
if (v_isShared_5378_ == 0)
{
v___x_5380_ = v___x_5377_;
goto v_reusejp_5379_;
}
else
{
lean_object* v_reuseFailAlloc_5381_; 
v_reuseFailAlloc_5381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5381_, 0, v_a_5375_);
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
lean_object* v___x_5383_; lean_object* v___x_5385_; 
lean_dec(v_a_5286_);
lean_dec_ref(v_b_5268_);
lean_dec_ref(v_a_5267_);
v___x_5383_ = lean_box(0);
if (v_isShared_5289_ == 0)
{
lean_ctor_set(v___x_5288_, 0, v___x_5383_);
v___x_5385_ = v___x_5288_;
goto v_reusejp_5384_;
}
else
{
lean_object* v_reuseFailAlloc_5386_; 
v_reuseFailAlloc_5386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5386_, 0, v___x_5383_);
v___x_5385_ = v_reuseFailAlloc_5386_;
goto v_reusejp_5384_;
}
v_reusejp_5384_:
{
return v___x_5385_;
}
}
}
}
else
{
lean_object* v_a_5388_; lean_object* v___x_5390_; uint8_t v_isShared_5391_; uint8_t v_isSharedCheck_5395_; 
lean_dec_ref(v_b_5268_);
lean_dec_ref(v_a_5267_);
v_a_5388_ = lean_ctor_get(v___x_5285_, 0);
v_isSharedCheck_5395_ = !lean_is_exclusive(v___x_5285_);
if (v_isSharedCheck_5395_ == 0)
{
v___x_5390_ = v___x_5285_;
v_isShared_5391_ = v_isSharedCheck_5395_;
goto v_resetjp_5389_;
}
else
{
lean_inc(v_a_5388_);
lean_dec(v___x_5285_);
v___x_5390_ = lean_box(0);
v_isShared_5391_ = v_isSharedCheck_5395_;
goto v_resetjp_5389_;
}
v_resetjp_5389_:
{
lean_object* v___x_5393_; 
if (v_isShared_5391_ == 0)
{
v___x_5393_ = v___x_5390_;
goto v_reusejp_5392_;
}
else
{
lean_object* v_reuseFailAlloc_5394_; 
v_reuseFailAlloc_5394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5394_, 0, v_a_5388_);
v___x_5393_ = v_reuseFailAlloc_5394_;
goto v_reusejp_5392_;
}
v_reusejp_5392_:
{
return v___x_5393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq___boxed(lean_object* v_a_5396_, lean_object* v_b_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_){
_start:
{
lean_object* v_res_5410_; 
v_res_5410_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5396_, v_b_5397_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_);
lean_dec(v_a_5408_);
lean_dec_ref(v_a_5407_);
lean_dec(v_a_5406_);
lean_dec_ref(v_a_5405_);
lean_dec(v_a_5404_);
lean_dec_ref(v_a_5403_);
lean_dec(v_a_5402_);
lean_dec_ref(v_a_5401_);
lean_dec(v_a_5400_);
lean_dec(v_a_5399_);
lean_dec(v_a_5398_);
return v_res_5410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(lean_object* v_a_5411_, lean_object* v_b_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_){
_start:
{
lean_object* v___x_5425_; 
v___x_5425_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5411_, v_a_5414_);
if (lean_obj_tag(v___x_5425_) == 0)
{
lean_object* v_a_5426_; uint8_t v___x_5427_; lean_object* v___x_5428_; 
v_a_5426_ = lean_ctor_get(v___x_5425_, 0);
lean_inc(v_a_5426_);
lean_dec_ref_known(v___x_5425_, 1);
v___x_5427_ = 0;
lean_inc_ref(v_a_5411_);
v___x_5428_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5411_, v___x_5427_, v_a_5426_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_, v_a_5420_, v_a_5421_, v_a_5422_, v_a_5423_);
if (lean_obj_tag(v___x_5428_) == 0)
{
lean_object* v_a_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5472_; 
v_a_5429_ = lean_ctor_get(v___x_5428_, 0);
v_isSharedCheck_5472_ = !lean_is_exclusive(v___x_5428_);
if (v_isSharedCheck_5472_ == 0)
{
v___x_5431_ = v___x_5428_;
v_isShared_5432_ = v_isSharedCheck_5472_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_a_5429_);
lean_dec(v___x_5428_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5472_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
if (lean_obj_tag(v_a_5429_) == 1)
{
lean_object* v_val_5433_; lean_object* v___x_5434_; 
lean_del_object(v___x_5431_);
v_val_5433_ = lean_ctor_get(v_a_5429_, 0);
lean_inc(v_val_5433_);
lean_dec_ref_known(v_a_5429_, 1);
v___x_5434_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5412_, v_a_5414_);
if (lean_obj_tag(v___x_5434_) == 0)
{
lean_object* v_a_5435_; lean_object* v___x_5436_; 
v_a_5435_ = lean_ctor_get(v___x_5434_, 0);
lean_inc(v_a_5435_);
lean_dec_ref_known(v___x_5434_, 1);
lean_inc_ref(v_b_5412_);
v___x_5436_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_5412_, v___x_5427_, v_a_5435_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_, v_a_5420_, v_a_5421_, v_a_5422_, v_a_5423_);
if (lean_obj_tag(v___x_5436_) == 0)
{
lean_object* v_a_5437_; lean_object* v___x_5439_; uint8_t v_isShared_5440_; uint8_t v_isSharedCheck_5451_; 
v_a_5437_ = lean_ctor_get(v___x_5436_, 0);
v_isSharedCheck_5451_ = !lean_is_exclusive(v___x_5436_);
if (v_isSharedCheck_5451_ == 0)
{
v___x_5439_ = v___x_5436_;
v_isShared_5440_ = v_isSharedCheck_5451_;
goto v_resetjp_5438_;
}
else
{
lean_inc(v_a_5437_);
lean_dec(v___x_5436_);
v___x_5439_ = lean_box(0);
v_isShared_5440_ = v_isSharedCheck_5451_;
goto v_resetjp_5438_;
}
v_resetjp_5438_:
{
if (lean_obj_tag(v_a_5437_) == 1)
{
lean_object* v_val_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; 
lean_del_object(v___x_5439_);
v_val_5441_ = lean_ctor_get(v_a_5437_, 0);
lean_inc_n(v_val_5441_, 2);
lean_dec_ref_known(v_a_5437_, 1);
lean_inc(v_val_5433_);
v___x_5442_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5442_, 0, v_val_5433_);
lean_ctor_set(v___x_5442_, 1, v_val_5441_);
v___x_5443_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5442_);
v___x_5444_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5444_, 0, v_a_5411_);
lean_ctor_set(v___x_5444_, 1, v_b_5412_);
lean_ctor_set(v___x_5444_, 2, v_val_5433_);
lean_ctor_set(v___x_5444_, 3, v_val_5441_);
v___x_5445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5445_, 0, v___x_5443_);
lean_ctor_set(v___x_5445_, 1, v___x_5444_);
v___x_5446_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5445_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_, v_a_5420_, v_a_5421_, v_a_5422_, v_a_5423_);
return v___x_5446_;
}
else
{
lean_object* v___x_5447_; lean_object* v___x_5449_; 
lean_dec(v_a_5437_);
lean_dec(v_val_5433_);
lean_dec_ref(v_b_5412_);
lean_dec_ref(v_a_5411_);
v___x_5447_ = lean_box(0);
if (v_isShared_5440_ == 0)
{
lean_ctor_set(v___x_5439_, 0, v___x_5447_);
v___x_5449_ = v___x_5439_;
goto v_reusejp_5448_;
}
else
{
lean_object* v_reuseFailAlloc_5450_; 
v_reuseFailAlloc_5450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5450_, 0, v___x_5447_);
v___x_5449_ = v_reuseFailAlloc_5450_;
goto v_reusejp_5448_;
}
v_reusejp_5448_:
{
return v___x_5449_;
}
}
}
}
else
{
lean_object* v_a_5452_; lean_object* v___x_5454_; uint8_t v_isShared_5455_; uint8_t v_isSharedCheck_5459_; 
lean_dec(v_val_5433_);
lean_dec_ref(v_b_5412_);
lean_dec_ref(v_a_5411_);
v_a_5452_ = lean_ctor_get(v___x_5436_, 0);
v_isSharedCheck_5459_ = !lean_is_exclusive(v___x_5436_);
if (v_isSharedCheck_5459_ == 0)
{
v___x_5454_ = v___x_5436_;
v_isShared_5455_ = v_isSharedCheck_5459_;
goto v_resetjp_5453_;
}
else
{
lean_inc(v_a_5452_);
lean_dec(v___x_5436_);
v___x_5454_ = lean_box(0);
v_isShared_5455_ = v_isSharedCheck_5459_;
goto v_resetjp_5453_;
}
v_resetjp_5453_:
{
lean_object* v___x_5457_; 
if (v_isShared_5455_ == 0)
{
v___x_5457_ = v___x_5454_;
goto v_reusejp_5456_;
}
else
{
lean_object* v_reuseFailAlloc_5458_; 
v_reuseFailAlloc_5458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5458_, 0, v_a_5452_);
v___x_5457_ = v_reuseFailAlloc_5458_;
goto v_reusejp_5456_;
}
v_reusejp_5456_:
{
return v___x_5457_;
}
}
}
}
else
{
lean_object* v_a_5460_; lean_object* v___x_5462_; uint8_t v_isShared_5463_; uint8_t v_isSharedCheck_5467_; 
lean_dec(v_val_5433_);
lean_dec_ref(v_b_5412_);
lean_dec_ref(v_a_5411_);
v_a_5460_ = lean_ctor_get(v___x_5434_, 0);
v_isSharedCheck_5467_ = !lean_is_exclusive(v___x_5434_);
if (v_isSharedCheck_5467_ == 0)
{
v___x_5462_ = v___x_5434_;
v_isShared_5463_ = v_isSharedCheck_5467_;
goto v_resetjp_5461_;
}
else
{
lean_inc(v_a_5460_);
lean_dec(v___x_5434_);
v___x_5462_ = lean_box(0);
v_isShared_5463_ = v_isSharedCheck_5467_;
goto v_resetjp_5461_;
}
v_resetjp_5461_:
{
lean_object* v___x_5465_; 
if (v_isShared_5463_ == 0)
{
v___x_5465_ = v___x_5462_;
goto v_reusejp_5464_;
}
else
{
lean_object* v_reuseFailAlloc_5466_; 
v_reuseFailAlloc_5466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5466_, 0, v_a_5460_);
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
lean_object* v___x_5468_; lean_object* v___x_5470_; 
lean_dec(v_a_5429_);
lean_dec_ref(v_b_5412_);
lean_dec_ref(v_a_5411_);
v___x_5468_ = lean_box(0);
if (v_isShared_5432_ == 0)
{
lean_ctor_set(v___x_5431_, 0, v___x_5468_);
v___x_5470_ = v___x_5431_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5471_; 
v_reuseFailAlloc_5471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5471_, 0, v___x_5468_);
v___x_5470_ = v_reuseFailAlloc_5471_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
return v___x_5470_;
}
}
}
}
else
{
lean_object* v_a_5473_; lean_object* v___x_5475_; uint8_t v_isShared_5476_; uint8_t v_isSharedCheck_5480_; 
lean_dec_ref(v_b_5412_);
lean_dec_ref(v_a_5411_);
v_a_5473_ = lean_ctor_get(v___x_5428_, 0);
v_isSharedCheck_5480_ = !lean_is_exclusive(v___x_5428_);
if (v_isSharedCheck_5480_ == 0)
{
v___x_5475_ = v___x_5428_;
v_isShared_5476_ = v_isSharedCheck_5480_;
goto v_resetjp_5474_;
}
else
{
lean_inc(v_a_5473_);
lean_dec(v___x_5428_);
v___x_5475_ = lean_box(0);
v_isShared_5476_ = v_isSharedCheck_5480_;
goto v_resetjp_5474_;
}
v_resetjp_5474_:
{
lean_object* v___x_5478_; 
if (v_isShared_5476_ == 0)
{
v___x_5478_ = v___x_5475_;
goto v_reusejp_5477_;
}
else
{
lean_object* v_reuseFailAlloc_5479_; 
v_reuseFailAlloc_5479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5479_, 0, v_a_5473_);
v___x_5478_ = v_reuseFailAlloc_5479_;
goto v_reusejp_5477_;
}
v_reusejp_5477_:
{
return v___x_5478_;
}
}
}
}
else
{
lean_object* v_a_5481_; lean_object* v___x_5483_; uint8_t v_isShared_5484_; uint8_t v_isSharedCheck_5488_; 
lean_dec_ref(v_b_5412_);
lean_dec_ref(v_a_5411_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq___boxed(lean_object* v_a_5489_, lean_object* v_b_5490_, lean_object* v_a_5491_, lean_object* v_a_5492_, lean_object* v_a_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_, lean_object* v_a_5502_){
_start:
{
lean_object* v_res_5503_; 
v_res_5503_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5489_, v_b_5490_, v_a_5491_, v_a_5492_, v_a_5493_, v_a_5494_, v_a_5495_, v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
lean_dec(v_a_5501_);
lean_dec_ref(v_a_5500_);
lean_dec(v_a_5499_);
lean_dec_ref(v_a_5498_);
lean_dec(v_a_5497_);
lean_dec_ref(v_a_5496_);
lean_dec(v_a_5495_);
lean_dec_ref(v_a_5494_);
lean_dec(v_a_5493_);
lean_dec(v_a_5492_);
lean_dec(v_a_5491_);
return v_res_5503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(lean_object* v_a_5504_, lean_object* v_b_5505_, lean_object* v_a_5506_, lean_object* v_a_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_, lean_object* v_a_5516_){
_start:
{
lean_object* v___x_5518_; 
v___x_5518_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_);
if (lean_obj_tag(v___x_5518_) == 0)
{
lean_object* v_a_5519_; lean_object* v_addRightCancelInst_x3f_5520_; 
v_a_5519_ = lean_ctor_get(v___x_5518_, 0);
lean_inc(v_a_5519_);
lean_dec_ref_known(v___x_5518_, 1);
v_addRightCancelInst_x3f_5520_ = lean_ctor_get(v_a_5519_, 11);
if (lean_obj_tag(v_addRightCancelInst_x3f_5520_) == 0)
{
lean_object* v___x_5521_; 
lean_dec(v_a_5519_);
v___x_5521_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(v_a_5504_, v_b_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_);
return v___x_5521_;
}
else
{
lean_object* v_id_5522_; lean_object* v_structId_5523_; lean_object* v___x_5524_; 
v_id_5522_ = lean_ctor_get(v_a_5519_, 0);
lean_inc(v_id_5522_);
v_structId_5523_ = lean_ctor_get(v_a_5519_, 1);
lean_inc(v_structId_5523_);
lean_dec(v_a_5519_);
lean_inc_ref(v_a_5504_);
v___x_5524_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5504_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_);
if (lean_obj_tag(v___x_5524_) == 0)
{
lean_object* v_a_5525_; lean_object* v_fst_5526_; lean_object* v___x_5528_; uint8_t v_isShared_5529_; uint8_t v_isSharedCheck_5614_; 
v_a_5525_ = lean_ctor_get(v___x_5524_, 0);
lean_inc(v_a_5525_);
lean_dec_ref_known(v___x_5524_, 1);
v_fst_5526_ = lean_ctor_get(v_a_5525_, 0);
v_isSharedCheck_5614_ = !lean_is_exclusive(v_a_5525_);
if (v_isSharedCheck_5614_ == 0)
{
lean_object* v_unused_5615_; 
v_unused_5615_ = lean_ctor_get(v_a_5525_, 1);
lean_dec(v_unused_5615_);
v___x_5528_ = v_a_5525_;
v_isShared_5529_ = v_isSharedCheck_5614_;
goto v_resetjp_5527_;
}
else
{
lean_inc(v_fst_5526_);
lean_dec(v_a_5525_);
v___x_5528_ = lean_box(0);
v_isShared_5529_ = v_isSharedCheck_5614_;
goto v_resetjp_5527_;
}
v_resetjp_5527_:
{
lean_object* v___x_5530_; 
lean_inc_ref(v_b_5505_);
v___x_5530_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_);
if (lean_obj_tag(v___x_5530_) == 0)
{
lean_object* v_a_5531_; lean_object* v_fst_5532_; lean_object* v___x_5534_; uint8_t v_isShared_5535_; uint8_t v_isSharedCheck_5604_; 
v_a_5531_ = lean_ctor_get(v___x_5530_, 0);
lean_inc(v_a_5531_);
lean_dec_ref_known(v___x_5530_, 1);
v_fst_5532_ = lean_ctor_get(v_a_5531_, 0);
v_isSharedCheck_5604_ = !lean_is_exclusive(v_a_5531_);
if (v_isSharedCheck_5604_ == 0)
{
lean_object* v_unused_5605_; 
v_unused_5605_ = lean_ctor_get(v_a_5531_, 1);
lean_dec(v_unused_5605_);
v___x_5534_ = v_a_5531_;
v_isShared_5535_ = v_isSharedCheck_5604_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_fst_5532_);
lean_dec(v_a_5531_);
v___x_5534_ = lean_box(0);
v_isShared_5535_ = v_isSharedCheck_5604_;
goto v_resetjp_5533_;
}
v_resetjp_5533_:
{
lean_object* v___x_5536_; 
v___x_5536_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5504_, v_a_5507_);
if (lean_obj_tag(v___x_5536_) == 0)
{
lean_object* v_a_5537_; uint8_t v___x_5538_; lean_object* v___x_5539_; 
v_a_5537_ = lean_ctor_get(v___x_5536_, 0);
lean_inc(v_a_5537_);
lean_dec_ref_known(v___x_5536_, 1);
v___x_5538_ = 0;
v___x_5539_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5526_, v___x_5538_, v_a_5537_, v_structId_5523_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_);
if (lean_obj_tag(v___x_5539_) == 0)
{
lean_object* v_a_5540_; lean_object* v___x_5542_; uint8_t v_isShared_5543_; uint8_t v_isSharedCheck_5587_; 
v_a_5540_ = lean_ctor_get(v___x_5539_, 0);
v_isSharedCheck_5587_ = !lean_is_exclusive(v___x_5539_);
if (v_isSharedCheck_5587_ == 0)
{
v___x_5542_ = v___x_5539_;
v_isShared_5543_ = v_isSharedCheck_5587_;
goto v_resetjp_5541_;
}
else
{
lean_inc(v_a_5540_);
lean_dec(v___x_5539_);
v___x_5542_ = lean_box(0);
v_isShared_5543_ = v_isSharedCheck_5587_;
goto v_resetjp_5541_;
}
v_resetjp_5541_:
{
if (lean_obj_tag(v_a_5540_) == 1)
{
lean_object* v_val_5544_; lean_object* v___x_5545_; 
lean_del_object(v___x_5542_);
v_val_5544_ = lean_ctor_get(v_a_5540_, 0);
lean_inc(v_val_5544_);
lean_dec_ref_known(v_a_5540_, 1);
v___x_5545_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5505_, v_a_5507_);
if (lean_obj_tag(v___x_5545_) == 0)
{
lean_object* v_a_5546_; lean_object* v___x_5547_; 
v_a_5546_ = lean_ctor_get(v___x_5545_, 0);
lean_inc(v_a_5546_);
lean_dec_ref_known(v___x_5545_, 1);
v___x_5547_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5532_, v___x_5538_, v_a_5546_, v_structId_5523_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_);
if (lean_obj_tag(v___x_5547_) == 0)
{
lean_object* v_a_5548_; lean_object* v___x_5550_; uint8_t v_isShared_5551_; uint8_t v_isSharedCheck_5566_; 
v_a_5548_ = lean_ctor_get(v___x_5547_, 0);
v_isSharedCheck_5566_ = !lean_is_exclusive(v___x_5547_);
if (v_isSharedCheck_5566_ == 0)
{
v___x_5550_ = v___x_5547_;
v_isShared_5551_ = v_isSharedCheck_5566_;
goto v_resetjp_5549_;
}
else
{
lean_inc(v_a_5548_);
lean_dec(v___x_5547_);
v___x_5550_ = lean_box(0);
v_isShared_5551_ = v_isSharedCheck_5566_;
goto v_resetjp_5549_;
}
v_resetjp_5549_:
{
if (lean_obj_tag(v_a_5548_) == 1)
{
lean_object* v_val_5552_; lean_object* v___x_5554_; 
lean_del_object(v___x_5550_);
v_val_5552_ = lean_ctor_get(v_a_5548_, 0);
lean_inc_n(v_val_5552_, 2);
lean_dec_ref_known(v_a_5548_, 1);
lean_inc(v_val_5544_);
if (v_isShared_5535_ == 0)
{
lean_ctor_set_tag(v___x_5534_, 3);
lean_ctor_set(v___x_5534_, 1, v_val_5552_);
lean_ctor_set(v___x_5534_, 0, v_val_5544_);
v___x_5554_ = v___x_5534_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_val_5544_);
lean_ctor_set(v_reuseFailAlloc_5561_, 1, v_val_5552_);
v___x_5554_ = v_reuseFailAlloc_5561_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5558_; 
v___x_5555_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5554_);
v___x_5556_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5556_, 0, v_a_5504_);
lean_ctor_set(v___x_5556_, 1, v_b_5505_);
lean_ctor_set(v___x_5556_, 2, v_id_5522_);
lean_ctor_set(v___x_5556_, 3, v_val_5544_);
lean_ctor_set(v___x_5556_, 4, v_val_5552_);
if (v_isShared_5529_ == 0)
{
lean_ctor_set(v___x_5528_, 1, v___x_5556_);
lean_ctor_set(v___x_5528_, 0, v___x_5555_);
v___x_5558_ = v___x_5528_;
goto v_reusejp_5557_;
}
else
{
lean_object* v_reuseFailAlloc_5560_; 
v_reuseFailAlloc_5560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5560_, 0, v___x_5555_);
lean_ctor_set(v_reuseFailAlloc_5560_, 1, v___x_5556_);
v___x_5558_ = v_reuseFailAlloc_5560_;
goto v_reusejp_5557_;
}
v_reusejp_5557_:
{
lean_object* v___x_5559_; 
v___x_5559_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5558_, v_structId_5523_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_);
lean_dec(v_structId_5523_);
return v___x_5559_;
}
}
}
else
{
lean_object* v___x_5562_; lean_object* v___x_5564_; 
lean_dec(v_a_5548_);
lean_dec(v_val_5544_);
lean_del_object(v___x_5534_);
lean_del_object(v___x_5528_);
lean_dec(v_structId_5523_);
lean_dec(v_id_5522_);
lean_dec_ref(v_b_5505_);
lean_dec_ref(v_a_5504_);
v___x_5562_ = lean_box(0);
if (v_isShared_5551_ == 0)
{
lean_ctor_set(v___x_5550_, 0, v___x_5562_);
v___x_5564_ = v___x_5550_;
goto v_reusejp_5563_;
}
else
{
lean_object* v_reuseFailAlloc_5565_; 
v_reuseFailAlloc_5565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5565_, 0, v___x_5562_);
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
else
{
lean_object* v_a_5567_; lean_object* v___x_5569_; uint8_t v_isShared_5570_; uint8_t v_isSharedCheck_5574_; 
lean_dec(v_val_5544_);
lean_del_object(v___x_5534_);
lean_del_object(v___x_5528_);
lean_dec(v_structId_5523_);
lean_dec(v_id_5522_);
lean_dec_ref(v_b_5505_);
lean_dec_ref(v_a_5504_);
v_a_5567_ = lean_ctor_get(v___x_5547_, 0);
v_isSharedCheck_5574_ = !lean_is_exclusive(v___x_5547_);
if (v_isSharedCheck_5574_ == 0)
{
v___x_5569_ = v___x_5547_;
v_isShared_5570_ = v_isSharedCheck_5574_;
goto v_resetjp_5568_;
}
else
{
lean_inc(v_a_5567_);
lean_dec(v___x_5547_);
v___x_5569_ = lean_box(0);
v_isShared_5570_ = v_isSharedCheck_5574_;
goto v_resetjp_5568_;
}
v_resetjp_5568_:
{
lean_object* v___x_5572_; 
if (v_isShared_5570_ == 0)
{
v___x_5572_ = v___x_5569_;
goto v_reusejp_5571_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v_a_5567_);
v___x_5572_ = v_reuseFailAlloc_5573_;
goto v_reusejp_5571_;
}
v_reusejp_5571_:
{
return v___x_5572_;
}
}
}
}
else
{
lean_object* v_a_5575_; lean_object* v___x_5577_; uint8_t v_isShared_5578_; uint8_t v_isSharedCheck_5582_; 
lean_dec(v_val_5544_);
lean_del_object(v___x_5534_);
lean_dec(v_fst_5532_);
lean_del_object(v___x_5528_);
lean_dec(v_structId_5523_);
lean_dec(v_id_5522_);
lean_dec_ref(v_b_5505_);
lean_dec_ref(v_a_5504_);
v_a_5575_ = lean_ctor_get(v___x_5545_, 0);
v_isSharedCheck_5582_ = !lean_is_exclusive(v___x_5545_);
if (v_isSharedCheck_5582_ == 0)
{
v___x_5577_ = v___x_5545_;
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
else
{
lean_inc(v_a_5575_);
lean_dec(v___x_5545_);
v___x_5577_ = lean_box(0);
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
v_resetjp_5576_:
{
lean_object* v___x_5580_; 
if (v_isShared_5578_ == 0)
{
v___x_5580_ = v___x_5577_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v_a_5575_);
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
lean_object* v___x_5583_; lean_object* v___x_5585_; 
lean_dec(v_a_5540_);
lean_del_object(v___x_5534_);
lean_dec(v_fst_5532_);
lean_del_object(v___x_5528_);
lean_dec(v_structId_5523_);
lean_dec(v_id_5522_);
lean_dec_ref(v_b_5505_);
lean_dec_ref(v_a_5504_);
v___x_5583_ = lean_box(0);
if (v_isShared_5543_ == 0)
{
lean_ctor_set(v___x_5542_, 0, v___x_5583_);
v___x_5585_ = v___x_5542_;
goto v_reusejp_5584_;
}
else
{
lean_object* v_reuseFailAlloc_5586_; 
v_reuseFailAlloc_5586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5586_, 0, v___x_5583_);
v___x_5585_ = v_reuseFailAlloc_5586_;
goto v_reusejp_5584_;
}
v_reusejp_5584_:
{
return v___x_5585_;
}
}
}
}
else
{
lean_object* v_a_5588_; lean_object* v___x_5590_; uint8_t v_isShared_5591_; uint8_t v_isSharedCheck_5595_; 
lean_del_object(v___x_5534_);
lean_dec(v_fst_5532_);
lean_del_object(v___x_5528_);
lean_dec(v_structId_5523_);
lean_dec(v_id_5522_);
lean_dec_ref(v_b_5505_);
lean_dec_ref(v_a_5504_);
v_a_5588_ = lean_ctor_get(v___x_5539_, 0);
v_isSharedCheck_5595_ = !lean_is_exclusive(v___x_5539_);
if (v_isSharedCheck_5595_ == 0)
{
v___x_5590_ = v___x_5539_;
v_isShared_5591_ = v_isSharedCheck_5595_;
goto v_resetjp_5589_;
}
else
{
lean_inc(v_a_5588_);
lean_dec(v___x_5539_);
v___x_5590_ = lean_box(0);
v_isShared_5591_ = v_isSharedCheck_5595_;
goto v_resetjp_5589_;
}
v_resetjp_5589_:
{
lean_object* v___x_5593_; 
if (v_isShared_5591_ == 0)
{
v___x_5593_ = v___x_5590_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v_a_5588_);
v___x_5593_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
return v___x_5593_;
}
}
}
}
else
{
lean_object* v_a_5596_; lean_object* v___x_5598_; uint8_t v_isShared_5599_; uint8_t v_isSharedCheck_5603_; 
lean_del_object(v___x_5534_);
lean_dec(v_fst_5532_);
lean_del_object(v___x_5528_);
lean_dec(v_fst_5526_);
lean_dec(v_structId_5523_);
lean_dec(v_id_5522_);
lean_dec_ref(v_b_5505_);
lean_dec_ref(v_a_5504_);
v_a_5596_ = lean_ctor_get(v___x_5536_, 0);
v_isSharedCheck_5603_ = !lean_is_exclusive(v___x_5536_);
if (v_isSharedCheck_5603_ == 0)
{
v___x_5598_ = v___x_5536_;
v_isShared_5599_ = v_isSharedCheck_5603_;
goto v_resetjp_5597_;
}
else
{
lean_inc(v_a_5596_);
lean_dec(v___x_5536_);
v___x_5598_ = lean_box(0);
v_isShared_5599_ = v_isSharedCheck_5603_;
goto v_resetjp_5597_;
}
v_resetjp_5597_:
{
lean_object* v___x_5601_; 
if (v_isShared_5599_ == 0)
{
v___x_5601_ = v___x_5598_;
goto v_reusejp_5600_;
}
else
{
lean_object* v_reuseFailAlloc_5602_; 
v_reuseFailAlloc_5602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5602_, 0, v_a_5596_);
v___x_5601_ = v_reuseFailAlloc_5602_;
goto v_reusejp_5600_;
}
v_reusejp_5600_:
{
return v___x_5601_;
}
}
}
}
}
else
{
lean_object* v_a_5606_; lean_object* v___x_5608_; uint8_t v_isShared_5609_; uint8_t v_isSharedCheck_5613_; 
lean_del_object(v___x_5528_);
lean_dec(v_fst_5526_);
lean_dec(v_structId_5523_);
lean_dec(v_id_5522_);
lean_dec_ref(v_b_5505_);
lean_dec_ref(v_a_5504_);
v_a_5606_ = lean_ctor_get(v___x_5530_, 0);
v_isSharedCheck_5613_ = !lean_is_exclusive(v___x_5530_);
if (v_isSharedCheck_5613_ == 0)
{
v___x_5608_ = v___x_5530_;
v_isShared_5609_ = v_isSharedCheck_5613_;
goto v_resetjp_5607_;
}
else
{
lean_inc(v_a_5606_);
lean_dec(v___x_5530_);
v___x_5608_ = lean_box(0);
v_isShared_5609_ = v_isSharedCheck_5613_;
goto v_resetjp_5607_;
}
v_resetjp_5607_:
{
lean_object* v___x_5611_; 
if (v_isShared_5609_ == 0)
{
v___x_5611_ = v___x_5608_;
goto v_reusejp_5610_;
}
else
{
lean_object* v_reuseFailAlloc_5612_; 
v_reuseFailAlloc_5612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5612_, 0, v_a_5606_);
v___x_5611_ = v_reuseFailAlloc_5612_;
goto v_reusejp_5610_;
}
v_reusejp_5610_:
{
return v___x_5611_;
}
}
}
}
}
else
{
lean_object* v_a_5616_; lean_object* v___x_5618_; uint8_t v_isShared_5619_; uint8_t v_isSharedCheck_5623_; 
lean_dec(v_structId_5523_);
lean_dec(v_id_5522_);
lean_dec_ref(v_b_5505_);
lean_dec_ref(v_a_5504_);
v_a_5616_ = lean_ctor_get(v___x_5524_, 0);
v_isSharedCheck_5623_ = !lean_is_exclusive(v___x_5524_);
if (v_isSharedCheck_5623_ == 0)
{
v___x_5618_ = v___x_5524_;
v_isShared_5619_ = v_isSharedCheck_5623_;
goto v_resetjp_5617_;
}
else
{
lean_inc(v_a_5616_);
lean_dec(v___x_5524_);
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
}
else
{
lean_object* v_a_5624_; lean_object* v___x_5626_; uint8_t v_isShared_5627_; uint8_t v_isSharedCheck_5631_; 
lean_dec_ref(v_b_5505_);
lean_dec_ref(v_a_5504_);
v_a_5624_ = lean_ctor_get(v___x_5518_, 0);
v_isSharedCheck_5631_ = !lean_is_exclusive(v___x_5518_);
if (v_isSharedCheck_5631_ == 0)
{
v___x_5626_ = v___x_5518_;
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
else
{
lean_inc(v_a_5624_);
lean_dec(v___x_5518_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq___boxed(lean_object* v_a_5632_, lean_object* v_b_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_, lean_object* v_a_5638_, lean_object* v_a_5639_, lean_object* v_a_5640_, lean_object* v_a_5641_, lean_object* v_a_5642_, lean_object* v_a_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_){
_start:
{
lean_object* v_res_5646_; 
v_res_5646_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5632_, v_b_5633_, v_a_5634_, v_a_5635_, v_a_5636_, v_a_5637_, v_a_5638_, v_a_5639_, v_a_5640_, v_a_5641_, v_a_5642_, v_a_5643_, v_a_5644_);
lean_dec(v_a_5644_);
lean_dec_ref(v_a_5643_);
lean_dec(v_a_5642_);
lean_dec_ref(v_a_5641_);
lean_dec(v_a_5640_);
lean_dec_ref(v_a_5639_);
lean_dec(v_a_5638_);
lean_dec_ref(v_a_5637_);
lean_dec(v_a_5636_);
lean_dec(v_a_5635_);
lean_dec(v_a_5634_);
return v_res_5646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(lean_object* v_a_5647_, lean_object* v_b_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_){
_start:
{
lean_object* v___x_5660_; 
v___x_5660_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5647_, v_b_5648_, v_a_5649_, v_a_5657_);
if (lean_obj_tag(v___x_5660_) == 0)
{
lean_object* v_a_5661_; 
v_a_5661_ = lean_ctor_get(v___x_5660_, 0);
lean_inc(v_a_5661_);
lean_dec_ref_known(v___x_5660_, 1);
if (lean_obj_tag(v_a_5661_) == 1)
{
lean_object* v_val_5662_; lean_object* v___x_5663_; 
v_val_5662_ = lean_ctor_get(v_a_5661_, 0);
lean_inc(v_val_5662_);
lean_dec_ref_known(v_a_5661_, 1);
v___x_5663_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5662_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_);
if (lean_obj_tag(v___x_5663_) == 0)
{
lean_object* v_a_5664_; uint8_t v___x_5665_; 
v_a_5664_ = lean_ctor_get(v___x_5663_, 0);
lean_inc(v_a_5664_);
lean_dec_ref_known(v___x_5663_, 1);
v___x_5665_ = lean_unbox(v_a_5664_);
lean_dec(v_a_5664_);
if (v___x_5665_ == 0)
{
lean_object* v___x_5666_; 
v___x_5666_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5647_, v_b_5648_, v_val_5662_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_);
lean_dec(v_val_5662_);
return v___x_5666_;
}
else
{
lean_object* v___x_5667_; 
v___x_5667_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5647_, v_b_5648_, v_val_5662_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_);
lean_dec(v_val_5662_);
return v___x_5667_;
}
}
else
{
lean_object* v_a_5668_; lean_object* v___x_5670_; uint8_t v_isShared_5671_; uint8_t v_isSharedCheck_5675_; 
lean_dec(v_val_5662_);
lean_dec_ref(v_b_5648_);
lean_dec_ref(v_a_5647_);
v_a_5668_ = lean_ctor_get(v___x_5663_, 0);
v_isSharedCheck_5675_ = !lean_is_exclusive(v___x_5663_);
if (v_isSharedCheck_5675_ == 0)
{
v___x_5670_ = v___x_5663_;
v_isShared_5671_ = v_isSharedCheck_5675_;
goto v_resetjp_5669_;
}
else
{
lean_inc(v_a_5668_);
lean_dec(v___x_5663_);
v___x_5670_ = lean_box(0);
v_isShared_5671_ = v_isSharedCheck_5675_;
goto v_resetjp_5669_;
}
v_resetjp_5669_:
{
lean_object* v___x_5673_; 
if (v_isShared_5671_ == 0)
{
v___x_5673_ = v___x_5670_;
goto v_reusejp_5672_;
}
else
{
lean_object* v_reuseFailAlloc_5674_; 
v_reuseFailAlloc_5674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5674_, 0, v_a_5668_);
v___x_5673_ = v_reuseFailAlloc_5674_;
goto v_reusejp_5672_;
}
v_reusejp_5672_:
{
return v___x_5673_;
}
}
}
}
else
{
lean_object* v___x_5676_; 
lean_dec(v_a_5661_);
v___x_5676_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5647_, v_b_5648_, v_a_5649_, v_a_5657_);
if (lean_obj_tag(v___x_5676_) == 0)
{
lean_object* v_a_5677_; lean_object* v___x_5679_; uint8_t v_isShared_5680_; uint8_t v_isSharedCheck_5687_; 
v_a_5677_ = lean_ctor_get(v___x_5676_, 0);
v_isSharedCheck_5687_ = !lean_is_exclusive(v___x_5676_);
if (v_isSharedCheck_5687_ == 0)
{
v___x_5679_ = v___x_5676_;
v_isShared_5680_ = v_isSharedCheck_5687_;
goto v_resetjp_5678_;
}
else
{
lean_inc(v_a_5677_);
lean_dec(v___x_5676_);
v___x_5679_ = lean_box(0);
v_isShared_5680_ = v_isSharedCheck_5687_;
goto v_resetjp_5678_;
}
v_resetjp_5678_:
{
if (lean_obj_tag(v_a_5677_) == 1)
{
lean_object* v_val_5681_; lean_object* v___x_5682_; 
lean_del_object(v___x_5679_);
v_val_5681_ = lean_ctor_get(v_a_5677_, 0);
lean_inc(v_val_5681_);
lean_dec_ref_known(v_a_5677_, 1);
v___x_5682_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5647_, v_b_5648_, v_val_5681_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_);
lean_dec(v_val_5681_);
return v___x_5682_;
}
else
{
lean_object* v___x_5683_; lean_object* v___x_5685_; 
lean_dec(v_a_5677_);
lean_dec_ref(v_b_5648_);
lean_dec_ref(v_a_5647_);
v___x_5683_ = lean_box(0);
if (v_isShared_5680_ == 0)
{
lean_ctor_set(v___x_5679_, 0, v___x_5683_);
v___x_5685_ = v___x_5679_;
goto v_reusejp_5684_;
}
else
{
lean_object* v_reuseFailAlloc_5686_; 
v_reuseFailAlloc_5686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5686_, 0, v___x_5683_);
v___x_5685_ = v_reuseFailAlloc_5686_;
goto v_reusejp_5684_;
}
v_reusejp_5684_:
{
return v___x_5685_;
}
}
}
}
else
{
lean_object* v_a_5688_; lean_object* v___x_5690_; uint8_t v_isShared_5691_; uint8_t v_isSharedCheck_5695_; 
lean_dec_ref(v_b_5648_);
lean_dec_ref(v_a_5647_);
v_a_5688_ = lean_ctor_get(v___x_5676_, 0);
v_isSharedCheck_5695_ = !lean_is_exclusive(v___x_5676_);
if (v_isSharedCheck_5695_ == 0)
{
v___x_5690_ = v___x_5676_;
v_isShared_5691_ = v_isSharedCheck_5695_;
goto v_resetjp_5689_;
}
else
{
lean_inc(v_a_5688_);
lean_dec(v___x_5676_);
v___x_5690_ = lean_box(0);
v_isShared_5691_ = v_isSharedCheck_5695_;
goto v_resetjp_5689_;
}
v_resetjp_5689_:
{
lean_object* v___x_5693_; 
if (v_isShared_5691_ == 0)
{
v___x_5693_ = v___x_5690_;
goto v_reusejp_5692_;
}
else
{
lean_object* v_reuseFailAlloc_5694_; 
v_reuseFailAlloc_5694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5694_, 0, v_a_5688_);
v___x_5693_ = v_reuseFailAlloc_5694_;
goto v_reusejp_5692_;
}
v_reusejp_5692_:
{
return v___x_5693_;
}
}
}
}
}
else
{
lean_object* v_a_5696_; lean_object* v___x_5698_; uint8_t v_isShared_5699_; uint8_t v_isSharedCheck_5703_; 
lean_dec_ref(v_b_5648_);
lean_dec_ref(v_a_5647_);
v_a_5696_ = lean_ctor_get(v___x_5660_, 0);
v_isSharedCheck_5703_ = !lean_is_exclusive(v___x_5660_);
if (v_isSharedCheck_5703_ == 0)
{
v___x_5698_ = v___x_5660_;
v_isShared_5699_ = v_isSharedCheck_5703_;
goto v_resetjp_5697_;
}
else
{
lean_inc(v_a_5696_);
lean_dec(v___x_5660_);
v___x_5698_ = lean_box(0);
v_isShared_5699_ = v_isSharedCheck_5703_;
goto v_resetjp_5697_;
}
v_resetjp_5697_:
{
lean_object* v___x_5701_; 
if (v_isShared_5699_ == 0)
{
v___x_5701_ = v___x_5698_;
goto v_reusejp_5700_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v_a_5696_);
v___x_5701_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5700_;
}
v_reusejp_5700_:
{
return v___x_5701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed(lean_object* v_a_5704_, lean_object* v_b_5705_, lean_object* v_a_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_, lean_object* v_a_5712_, lean_object* v_a_5713_, lean_object* v_a_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_){
_start:
{
lean_object* v_res_5717_; 
v_res_5717_ = l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(v_a_5704_, v_b_5705_, v_a_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_, v_a_5711_, v_a_5712_, v_a_5713_, v_a_5714_, v_a_5715_);
lean_dec(v_a_5715_);
lean_dec_ref(v_a_5714_);
lean_dec(v_a_5713_);
lean_dec_ref(v_a_5712_);
lean_dec(v_a_5711_);
lean_dec_ref(v_a_5710_);
lean_dec(v_a_5709_);
lean_dec_ref(v_a_5708_);
lean_dec(v_a_5707_);
lean_dec(v_a_5706_);
return v_res_5717_;
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
