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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_dec_ref(v___x_19_);
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
lean_dec_ref(v___x_116_);
v___x_118_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0(v_k_113_, v_v_114_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v_a_119_; lean_object* v_addFn_120_; lean_object* v___x_121_; 
v_a_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_a_119_);
lean_dec_ref(v___x_118_);
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
lean_dec_ref(v___x_180_);
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
lean_dec_ref(v___x_268_);
v___x_270_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v_ofNatZero_272_; lean_object* v___x_273_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref(v___x_270_);
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
lean_object* v_ref_330_; lean_object* v___x_331_; lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_377_; 
v_ref_330_ = lean_ctor_get(v___y_327_, 5);
v___x_331_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msg_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_377_ == 0)
{
v___x_334_ = v___x_331_;
v_isShared_335_ = v_isSharedCheck_377_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_377_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v_traceState_337_; lean_object* v_env_338_; lean_object* v_nextMacroScope_339_; lean_object* v_ngen_340_; lean_object* v_auxDeclNGen_341_; lean_object* v_cache_342_; lean_object* v_messages_343_; lean_object* v_infoState_344_; lean_object* v_snapshotTasks_345_; lean_object* v_newDecls_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_376_; 
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
v_newDecls_346_ = lean_ctor_get(v___x_336_, 9);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_376_ == 0)
{
v___x_348_ = v___x_336_;
v_isShared_349_ = v_isSharedCheck_376_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_newDecls_346_);
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
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_376_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
uint64_t v_tid_350_; lean_object* v_traces_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_375_; 
v_tid_350_ = lean_ctor_get_uint64(v_traceState_337_, sizeof(void*)*1);
v_traces_351_ = lean_ctor_get(v_traceState_337_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v_traceState_337_);
if (v_isSharedCheck_375_ == 0)
{
v___x_353_ = v_traceState_337_;
v_isShared_354_ = v_isSharedCheck_375_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_traces_351_);
lean_dec(v_traceState_337_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_375_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; double v___x_356_; uint8_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_355_ = lean_box(0);
v___x_356_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__0);
v___x_357_ = 0;
v___x_358_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__1));
v___x_359_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_359_, 0, v_cls_323_);
lean_ctor_set(v___x_359_, 1, v___x_355_);
lean_ctor_set(v___x_359_, 2, v___x_358_);
lean_ctor_set_float(v___x_359_, sizeof(void*)*3, v___x_356_);
lean_ctor_set_float(v___x_359_, sizeof(void*)*3 + 8, v___x_356_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*3 + 16, v___x_357_);
v___x_360_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___closed__2));
v___x_361_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set(v___x_361_, 1, v_a_332_);
lean_ctor_set(v___x_361_, 2, v___x_360_);
lean_inc(v_ref_330_);
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v_ref_330_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = l_Lean_PersistentArray_push___redArg(v_traces_351_, v___x_362_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_363_);
v___x_365_ = v___x_353_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_363_);
lean_ctor_set_uint64(v_reuseFailAlloc_374_, sizeof(void*)*1, v_tid_350_);
v___x_365_ = v_reuseFailAlloc_374_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_367_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 4, v___x_365_);
v___x_367_ = v___x_348_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_env_338_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_nextMacroScope_339_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_ngen_340_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_auxDeclNGen_341_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_373_, 5, v_cache_342_);
lean_ctor_set(v_reuseFailAlloc_373_, 6, v_messages_343_);
lean_ctor_set(v_reuseFailAlloc_373_, 7, v_infoState_344_);
lean_ctor_set(v_reuseFailAlloc_373_, 8, v_snapshotTasks_345_);
lean_ctor_set(v_reuseFailAlloc_373_, 9, v_newDecls_346_);
v___x_367_ = v_reuseFailAlloc_373_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_368_ = lean_st_ref_set(v___y_328_, v___x_367_);
v___x_369_ = lean_box(0);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_369_);
v___x_371_ = v___x_334_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg___boxed(lean_object* v_cls_378_, lean_object* v_msg_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_378_, v_msg_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_385_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_399_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_400_ = l_Lean_Name_append(v___x_399_, v___x_398_);
return v___x_400_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__8));
v___x_403_ = l_Lean_stringToMessageData(v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(lean_object* v_p_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_540_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_540_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_540_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_540_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
if (lean_obj_tag(v_a_418_) == 1)
{
lean_object* v_val_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_535_; 
v_val_422_ = lean_ctor_get(v_a_418_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v_a_418_);
if (v_isSharedCheck_535_ == 0)
{
v___x_424_ = v_a_418_;
v_isShared_425_ = v_isSharedCheck_535_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_val_422_);
lean_dec(v_a_418_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_535_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v_snd_426_; lean_object* v_snd_427_; lean_object* v_options_428_; lean_object* v_fst_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_533_; 
v_snd_426_ = lean_ctor_get(v_val_422_, 1);
lean_inc(v_snd_426_);
v_snd_427_ = lean_ctor_get(v_snd_426_, 1);
lean_inc(v_snd_427_);
v_options_428_ = lean_ctor_get(v_a_414_, 2);
v_fst_429_ = lean_ctor_get(v_val_422_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v_val_422_);
if (v_isSharedCheck_533_ == 0)
{
lean_object* v_unused_534_; 
v_unused_534_ = lean_ctor_get(v_val_422_, 1);
lean_dec(v_unused_534_);
v___x_431_ = v_val_422_;
v_isShared_432_ = v_isSharedCheck_533_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_fst_429_);
lean_dec(v_val_422_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_533_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v_fst_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_531_; 
v_fst_433_ = lean_ctor_get(v_snd_426_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v_snd_426_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v_snd_426_, 1);
lean_dec(v_unused_532_);
v___x_435_ = v_snd_426_;
v_isShared_436_ = v_isSharedCheck_531_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_fst_433_);
lean_dec(v_snd_426_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_531_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v_p_437_; lean_object* v_inheritedTraceOptions_438_; uint8_t v_hasTrace_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_p_437_ = lean_ctor_get(v_snd_427_, 0);
v_inheritedTraceOptions_438_ = lean_ctor_get(v_a_414_, 13);
v_hasTrace_439_ = lean_ctor_get_uint8(v_options_428_, sizeof(void*)*1);
v___x_440_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_437_, v_fst_433_);
lean_inc(v_p_404_);
v___x_441_ = l_Lean_Grind_Linarith_Poly_mul(v_p_404_, v___x_440_);
v___x_442_ = lean_int_neg(v_fst_429_);
lean_inc(v_p_437_);
v___x_443_ = l_Lean_Grind_Linarith_Poly_mul(v_p_437_, v___x_442_);
lean_dec(v___x_442_);
v___x_444_ = l_Lean_Grind_Linarith_Poly_combine(v___x_441_, v___x_443_);
if (v_hasTrace_439_ == 0)
{
lean_dec(v___x_440_);
lean_dec(v_fst_429_);
lean_dec(v_p_404_);
goto v___jp_445_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_458_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_459_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_460_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_438_, v_options_428_, v___x_459_);
if (v___x_460_ == 0)
{
lean_dec(v___x_440_);
lean_dec(v_fst_429_);
lean_dec(v_p_404_);
goto v___jp_445_;
}
else
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec(v_p_404_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_463_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref(v___x_461_);
v___x_463_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_433_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_465_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_464_);
lean_dec_ref(v___x_463_);
v___x_465_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_427_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_467_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
lean_dec_ref(v___x_465_);
v___x_467_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v___x_444_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref(v___x_467_);
v___x_469_ = l_Lean_MessageData_ofExpr(v_a_462_);
v___x_470_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_469_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
v___x_472_ = l_Int_repr(v_fst_429_);
lean_dec(v_fst_429_);
v___x_473_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
v___x_474_ = l_Lean_MessageData_ofFormat(v___x_473_);
v___x_475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_471_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
lean_ctor_set(v___x_476_, 1, v___x_470_);
v___x_477_ = l_Lean_MessageData_ofExpr(v_a_464_);
v___x_478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_476_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v___x_470_);
v___x_480_ = l_Lean_MessageData_ofExpr(v_a_466_);
v___x_481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_479_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v___x_470_);
v___x_483_ = l_Int_repr(v___x_440_);
lean_dec(v___x_440_);
v___x_484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
v___x_485_ = l_Lean_MessageData_ofFormat(v___x_484_);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_482_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v___x_470_);
v___x_488_ = l_Lean_MessageData_ofExpr(v_a_468_);
v___x_489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_458_, v___x_489_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_dec_ref(v___x_490_);
goto v___jp_445_;
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec(v___x_444_);
lean_del_object(v___x_435_);
lean_dec(v_fst_433_);
lean_del_object(v___x_431_);
lean_dec(v_snd_427_);
lean_del_object(v___x_424_);
lean_del_object(v___x_420_);
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec(v_a_466_);
lean_dec(v_a_464_);
lean_dec(v_a_462_);
lean_dec(v___x_444_);
lean_dec(v___x_440_);
lean_del_object(v___x_435_);
lean_dec(v_fst_433_);
lean_del_object(v___x_431_);
lean_dec(v_fst_429_);
lean_dec(v_snd_427_);
lean_del_object(v___x_424_);
lean_del_object(v___x_420_);
v_a_499_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_467_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_467_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_dec(v_a_464_);
lean_dec(v_a_462_);
lean_dec(v___x_444_);
lean_dec(v___x_440_);
lean_del_object(v___x_435_);
lean_dec(v_fst_433_);
lean_del_object(v___x_431_);
lean_dec(v_fst_429_);
lean_dec(v_snd_427_);
lean_del_object(v___x_424_);
lean_del_object(v___x_420_);
v_a_507_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_465_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_465_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_dec(v_a_462_);
lean_dec(v___x_444_);
lean_dec(v___x_440_);
lean_del_object(v___x_435_);
lean_dec(v_fst_433_);
lean_del_object(v___x_431_);
lean_dec(v_fst_429_);
lean_dec(v_snd_427_);
lean_del_object(v___x_424_);
lean_del_object(v___x_420_);
v_a_515_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_463_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_463_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec(v___x_444_);
lean_dec(v___x_440_);
lean_del_object(v___x_435_);
lean_dec(v_fst_433_);
lean_del_object(v___x_431_);
lean_dec(v_fst_429_);
lean_dec(v_snd_427_);
lean_del_object(v___x_424_);
lean_del_object(v___x_420_);
v_a_523_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_461_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_461_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
v___jp_445_:
{
lean_object* v___x_447_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_444_);
lean_ctor_set(v___x_435_, 0, v_snd_427_);
v___x_447_ = v___x_435_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_snd_427_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_444_);
v___x_447_ = v_reuseFailAlloc_457_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_449_; 
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 1, v___x_447_);
lean_ctor_set(v___x_431_, 0, v_fst_433_);
v___x_449_ = v___x_431_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_fst_433_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v___x_447_);
v___x_449_ = v_reuseFailAlloc_456_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_451_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_449_);
v___x_451_ = v___x_424_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_455_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_453_; 
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_451_);
v___x_453_ = v___x_420_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
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
lean_object* v___x_536_; lean_object* v___x_538_; 
lean_dec(v_a_418_);
lean_dec(v_p_404_);
v___x_536_ = lean_box(0);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_536_);
v___x_538_ = v___x_420_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
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
lean_dec(v_p_404_);
v_a_541_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_417_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_417_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___boxed(lean_object* v_p_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
lean_dec(v_a_552_);
lean_dec(v_a_551_);
lean_dec(v_a_550_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(lean_object* v_cls_563_, lean_object* v_msg_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_563_, v_msg_564_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___boxed(lean_object* v_cls_578_, lean_object* v_msg_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2(v_cls_578_, v_msg_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec(v___y_581_);
lean_dec(v___y_580_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(lean_object* v_c_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v_p_606_; lean_object* v___x_607_; 
v_p_606_ = lean_ctor_get(v_c_593_, 0);
v___x_607_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_606_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_609_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref(v___x_607_);
v___x_609_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v_ofNatZero_611_; lean_object* v___x_612_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_a_610_);
lean_dec_ref(v___x_609_);
v_ofNatZero_611_ = lean_ctor_get(v_a_610_, 18);
lean_inc_ref(v_ofNatZero_611_);
lean_dec(v_a_610_);
v___x_612_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1_spec__3(v_a_608_, v_ofNatZero_611_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_621_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_621_ == 0)
{
v___x_615_ = v___x_612_;
v_isShared_616_ = v_isSharedCheck_621_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_621_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_617_ = l_Lean_mkNot(v_a_613_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_617_);
v___x_619_ = v___x_615_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
else
{
return v___x_612_;
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec(v_a_608_);
v_a_622_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_609_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_609_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
else
{
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0___boxed(lean_object* v_c_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v_c_630_);
return v_res_643_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_unsigned_to_nat(0u);
v___x_645_ = lean_nat_to_int(v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2(void){
_start:
{
lean_object* v_cls_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_cls_650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_652_ = l_Lean_Name_append(v___x_651_, v_cls_650_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(lean_object* v_a_653_, lean_object* v_x_654_, lean_object* v_c_u2081_655_, lean_object* v_b_656_, lean_object* v_c_u2082_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v_options_724_; uint8_t v_hasTrace_725_; 
v_options_724_ = lean_ctor_get(v_a_667_, 2);
v_hasTrace_725_ = lean_ctor_get_uint8(v_options_724_, sizeof(void*)*1);
if (v_hasTrace_725_ == 0)
{
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
v___y_681_ = v_a_668_;
goto v___jp_670_;
}
else
{
lean_object* v_inheritedTraceOptions_726_; lean_object* v_cls_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v_inheritedTraceOptions_726_ = lean_ctor_get(v_a_667_, 13);
v_cls_727_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_728_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2);
v___x_729_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_726_, v_options_724_, v___x_728_);
if (v___x_729_ == 0)
{
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
v___y_681_ = v_a_668_;
goto v___jp_670_;
}
else
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_654_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref(v___x_730_);
v___x_732_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_655_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref(v___x_732_);
v___x_734_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_u2082_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref(v___x_734_);
v___x_736_ = l_Lean_MessageData_ofExpr(v_a_731_);
v___x_737_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_736_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = l_Lean_MessageData_ofExpr(v_a_733_);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v___x_737_);
v___x_742_ = l_Lean_MessageData_ofExpr(v_a_735_);
v___x_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_727_, v___x_743_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_dec_ref(v___x_744_);
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
v___y_681_ = v_a_668_;
goto v___jp_670_;
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v_c_u2082_657_);
lean_dec(v_b_656_);
lean_dec_ref(v_c_u2081_655_);
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec(v_a_733_);
lean_dec(v_a_731_);
lean_dec_ref(v_c_u2082_657_);
lean_dec(v_b_656_);
lean_dec_ref(v_c_u2081_655_);
v_a_753_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_734_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_734_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec(v_a_731_);
lean_dec_ref(v_c_u2082_657_);
lean_dec(v_b_656_);
lean_dec_ref(v_c_u2081_655_);
v_a_761_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_732_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_732_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec_ref(v_c_u2082_657_);
lean_dec(v_b_656_);
lean_dec_ref(v_c_u2081_655_);
v_a_769_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_730_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_730_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
v___jp_670_:
{
lean_object* v_p_682_; lean_object* v_p_683_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v_p_682_ = lean_ctor_get(v_c_u2081_655_, 0);
v_p_683_ = lean_ctor_get(v_c_u2082_657_, 0);
v___x_684_ = lean_int_emod(v_b_656_, v_a_653_);
v___x_685_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_686_ = lean_int_dec_eq(v___x_684_, v___x_685_);
lean_dec(v___x_684_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_707_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_707_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_707_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_707_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
uint8_t v___x_692_; 
v___x_692_ = lean_unbox(v_a_688_);
lean_dec(v_a_688_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_695_; 
lean_dec_ref(v_c_u2082_657_);
lean_dec(v_b_656_);
lean_dec_ref(v_c_u2081_655_);
v___x_693_ = lean_box(0);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_693_);
v___x_695_ = v___x_690_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
lean_inc(v_p_682_);
v___x_697_ = l_Lean_Grind_Linarith_Poly_mul(v_p_682_, v_b_656_);
v___x_698_ = lean_int_neg(v_a_653_);
lean_inc(v_p_683_);
v___x_699_ = l_Lean_Grind_Linarith_Poly_mul(v_p_683_, v___x_698_);
v___x_700_ = l_Lean_Grind_Linarith_Poly_combine(v___x_697_, v___x_699_);
v___x_701_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v___x_701_, 0, v___x_698_);
lean_ctor_set(v___x_701_, 1, v_b_656_);
lean_ctor_set(v___x_701_, 2, v_c_u2081_655_);
lean_ctor_set(v___x_701_, 3, v_c_u2082_657_);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_703_);
v___x_705_ = v___x_690_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref(v_c_u2082_657_);
lean_dec(v_b_656_);
lean_dec_ref(v_c_u2081_655_);
v_a_708_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_687_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_687_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_716_ = lean_int_neg(v_b_656_);
lean_dec(v_b_656_);
v___x_717_ = lean_int_ediv(v___x_716_, v_a_653_);
lean_dec(v___x_716_);
lean_inc(v_p_682_);
v___x_718_ = l_Lean_Grind_Linarith_Poly_mul(v_p_682_, v___x_717_);
lean_inc(v_p_683_);
v___x_719_ = l_Lean_Grind_Linarith_Poly_combine(v___x_718_, v_p_683_);
v___x_720_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_720_, 0, v___x_717_);
lean_ctor_set(v___x_720_, 1, v_c_u2081_655_);
lean_ctor_set(v___x_720_, 2, v_c_u2082_657_);
v___x_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
return v___x_723_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___boxed(lean_object** _args){
lean_object* v_a_777_ = _args[0];
lean_object* v_x_778_ = _args[1];
lean_object* v_c_u2081_779_ = _args[2];
lean_object* v_b_780_ = _args[3];
lean_object* v_c_u2082_781_ = _args[4];
lean_object* v_a_782_ = _args[5];
lean_object* v_a_783_ = _args[6];
lean_object* v_a_784_ = _args[7];
lean_object* v_a_785_ = _args[8];
lean_object* v_a_786_ = _args[9];
lean_object* v_a_787_ = _args[10];
lean_object* v_a_788_ = _args[11];
lean_object* v_a_789_ = _args[12];
lean_object* v_a_790_ = _args[13];
lean_object* v_a_791_ = _args[14];
lean_object* v_a_792_ = _args[15];
lean_object* v_a_793_ = _args[16];
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_777_, v_x_778_, v_c_u2081_779_, v_b_780_, v_c_u2082_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec(v_a_783_);
lean_dec(v_a_782_);
lean_dec(v_x_778_);
lean_dec(v_a_777_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(lean_object* v_a_795_, lean_object* v_b_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_a_795_, v_a_797_, v_a_798_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_829_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_829_ == 0)
{
v___x_803_ = v___x_800_;
v_isShared_804_ = v_isSharedCheck_829_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_800_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_829_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
if (lean_obj_tag(v_a_801_) == 1)
{
lean_object* v_val_805_; lean_object* v___x_806_; 
lean_del_object(v___x_803_);
v_val_805_ = lean_ctor_get(v_a_801_, 0);
v___x_806_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_b_796_, v_a_797_, v_a_798_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_824_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_824_ == 0)
{
v___x_809_ = v___x_806_;
v_isShared_810_ = v_isSharedCheck_824_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_824_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
if (lean_obj_tag(v_a_807_) == 1)
{
lean_object* v_val_811_; uint8_t v___x_812_; 
v_val_811_ = lean_ctor_get(v_a_807_, 0);
lean_inc(v_val_811_);
lean_dec_ref(v_a_807_);
v___x_812_ = lean_nat_dec_eq(v_val_805_, v_val_811_);
lean_dec(v_val_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_815_; 
lean_dec_ref(v_a_801_);
v___x_813_ = lean_box(0);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_813_);
v___x_815_ = v___x_809_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
else
{
lean_object* v___x_818_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v_a_801_);
v___x_818_ = v___x_809_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_801_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
else
{
lean_object* v___x_820_; lean_object* v___x_822_; 
lean_dec(v_a_807_);
lean_dec_ref(v_a_801_);
v___x_820_ = lean_box(0);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_820_);
v___x_822_ = v___x_809_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
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
lean_dec_ref(v_a_801_);
return v___x_806_;
}
}
else
{
lean_object* v___x_825_; lean_object* v___x_827_; 
lean_dec(v_a_801_);
v___x_825_ = lean_box(0);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_825_);
v___x_827_ = v___x_803_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
else
{
return v___x_800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg___boxed(lean_object* v_a_830_, lean_object* v_b_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_830_, v_b_831_, v_a_832_, v_a_833_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_b_831_);
lean_dec_ref(v_a_830_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(lean_object* v_a_836_, lean_object* v_b_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_836_, v_b_837_, v_a_838_, v_a_846_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___boxed(lean_object* v_a_850_, lean_object* v_b_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f(v_a_850_, v_b_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec(v_a_852_);
lean_dec_ref(v_b_851_);
lean_dec_ref(v_a_850_);
return v_res_863_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_865_ = lean_int_neg(v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(lean_object* v_a_866_, lean_object* v_b_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
uint8_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_880_ = 0;
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = lean_box(v___x_880_);
lean_inc_ref(v_a_866_);
v___x_883_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_883_, 0, v_a_866_);
lean_closure_set(v___x_883_, 1, v___x_882_);
lean_closure_set(v___x_883_, 2, v___x_881_);
v___x_884_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_883_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_1036_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_1036_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_1036_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
if (lean_obj_tag(v_a_885_) == 1)
{
lean_object* v_val_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
lean_del_object(v___x_887_);
v_val_889_ = lean_ctor_get(v_a_885_, 0);
lean_inc(v_val_889_);
lean_dec_ref(v_a_885_);
v___x_890_ = lean_box(v___x_880_);
lean_inc_ref(v_b_867_);
v___x_891_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_891_, 0, v_b_867_);
lean_closure_set(v___x_891_, 1, v___x_890_);
lean_closure_set(v___x_891_, 2, v___x_881_);
v___x_892_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_891_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_1023_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_1023_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_1023_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
if (lean_obj_tag(v_a_893_) == 1)
{
lean_object* v_val_897_; lean_object* v___x_898_; 
lean_del_object(v___x_895_);
v_val_897_ = lean_ctor_get(v_a_893_, 0);
lean_inc(v_val_897_);
lean_dec_ref(v_a_893_);
v___x_898_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_866_, v_a_869_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_900_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref(v___x_898_);
v___x_900_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_867_, v_a_869_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___y_903_; uint8_t v___x_1002_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
lean_dec_ref(v___x_900_);
v___x_1002_ = lean_nat_dec_le(v_a_899_, v_a_901_);
if (v___x_1002_ == 0)
{
lean_dec(v_a_901_);
v___y_903_ = v_a_899_;
goto v___jp_902_;
}
else
{
lean_dec(v_a_899_);
v___y_903_ = v_a_901_;
goto v___jp_902_;
}
v___jp_902_:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
lean_inc(v_val_897_);
lean_inc(v_val_889_);
v___x_904_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_904_, 0, v_val_889_);
lean_ctor_set(v___x_904_, 1, v_val_897_);
v___x_905_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_904_);
v___x_906_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_906_, 0, v_a_866_);
lean_ctor_set(v___x_906_, 1, v_b_867_);
lean_ctor_set(v___x_906_, 2, v_val_889_);
lean_ctor_set(v___x_906_, 3, v_val_897_);
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(v___x_907_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v_p_910_; lean_object* v___x_911_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref(v___x_908_);
v_p_910_ = lean_ctor_get(v_a_909_, 0);
lean_inc(v___y_903_);
lean_inc_ref(v_p_910_);
v___x_911_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_910_, v___y_903_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref(v___x_911_);
lean_inc(v___y_903_);
v___x_913_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_912_, v___x_880_, v___y_903_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_977_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_977_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_977_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_977_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
if (lean_obj_tag(v_a_914_) == 1)
{
lean_object* v_val_918_; lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v_val_918_ = lean_ctor_get(v_a_914_, 0);
lean_inc_n(v_val_918_, 2);
lean_dec_ref(v_a_914_);
v___x_919_ = l_Lean_Grind_Linarith_Expr_norm(v_val_918_);
v___x_920_ = lean_box(0);
v___x_921_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_919_, v___x_920_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
lean_del_object(v___x_916_);
lean_inc(v_a_909_);
v___x_922_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_922_, 0, v_a_909_);
lean_ctor_set(v___x_922_, 1, v_val_918_);
lean_inc(v___x_919_);
v___x_923_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_923_, 0, v___x_919_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*2, v___x_880_);
v___x_924_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_923_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_967_; 
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_967_ == 0)
{
lean_object* v_unused_968_; 
v_unused_968_ = lean_ctor_get(v___x_924_, 0);
lean_dec(v_unused_968_);
v___x_926_ = v___x_924_;
v_isShared_927_ = v_isSharedCheck_967_;
goto v_resetjp_925_;
}
else
{
lean_dec(v___x_924_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_967_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_928_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_910_);
v___x_929_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_928_, v_p_910_);
if (v_isShared_927_ == 0)
{
lean_ctor_set_tag(v___x_926_, 1);
lean_ctor_set(v___x_926_, 0, v_a_909_);
v___x_931_ = v___x_926_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_909_);
v___x_931_ = v_reuseFailAlloc_966_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_inc_ref(v___x_929_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_929_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
lean_inc(v___y_903_);
v___x_933_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v___x_929_, v___y_903_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_935_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref(v___x_933_);
v___x_935_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_934_, v___x_880_, v___y_903_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_949_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_949_ == 0)
{
v___x_938_ = v___x_935_;
v_isShared_939_ = v_isSharedCheck_949_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_949_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
if (lean_obj_tag(v_a_936_) == 1)
{
lean_object* v_val_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
lean_del_object(v___x_938_);
v_val_940_ = lean_ctor_get(v_a_936_, 0);
lean_inc(v_val_940_);
lean_dec_ref(v_a_936_);
v___x_941_ = l_Lean_Grind_Linarith_Poly_mul(v___x_919_, v___x_928_);
v___x_942_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_932_);
lean_ctor_set(v___x_942_, 1, v_val_940_);
v___x_943_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
lean_ctor_set_uint8(v___x_943_, sizeof(void*)*2, v___x_880_);
v___x_944_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_943_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
return v___x_944_;
}
else
{
lean_object* v___x_945_; lean_object* v___x_947_; 
lean_dec(v_a_936_);
lean_dec_ref(v___x_932_);
lean_dec(v___x_919_);
v___x_945_ = lean_box(0);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_945_);
v___x_947_ = v___x_938_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_945_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v___x_932_);
lean_dec(v___x_919_);
v_a_950_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_935_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_935_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec_ref(v___x_932_);
lean_dec(v___x_919_);
lean_dec(v___y_903_);
v_a_958_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_933_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_933_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
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
}
}
else
{
lean_dec(v___x_919_);
lean_dec(v_a_909_);
lean_dec(v___y_903_);
return v___x_924_;
}
}
else
{
lean_object* v___x_969_; lean_object* v___x_971_; 
lean_dec(v___x_919_);
lean_dec(v_val_918_);
lean_dec(v_a_909_);
lean_dec(v___y_903_);
v___x_969_ = lean_box(0);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_969_);
v___x_971_ = v___x_916_;
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
}
else
{
lean_object* v___x_973_; lean_object* v___x_975_; 
lean_dec(v_a_914_);
lean_dec(v_a_909_);
lean_dec(v___y_903_);
v___x_973_ = lean_box(0);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_973_);
v___x_975_ = v___x_916_;
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
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec(v_a_909_);
lean_dec(v___y_903_);
v_a_978_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_913_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_913_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec(v_a_909_);
lean_dec(v___y_903_);
v_a_986_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_911_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_911_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
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
lean_dec(v___y_903_);
v_a_994_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_908_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_908_);
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
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec(v_a_899_);
lean_dec(v_val_897_);
lean_dec(v_val_889_);
lean_dec_ref(v_b_867_);
lean_dec_ref(v_a_866_);
v_a_1003_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_900_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_900_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec(v_val_897_);
lean_dec(v_val_889_);
lean_dec_ref(v_b_867_);
lean_dec_ref(v_a_866_);
v_a_1011_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_898_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_898_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
else
{
lean_object* v___x_1019_; lean_object* v___x_1021_; 
lean_dec(v_a_893_);
lean_dec(v_val_889_);
lean_dec_ref(v_b_867_);
lean_dec_ref(v_a_866_);
v___x_1019_ = lean_box(0);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v___x_1019_);
v___x_1021_ = v___x_895_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
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
lean_dec(v_val_889_);
lean_dec_ref(v_b_867_);
lean_dec_ref(v_a_866_);
v_a_1024_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_892_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_892_);
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
lean_object* v___x_1032_; lean_object* v___x_1034_; 
lean_dec(v_a_885_);
lean_dec_ref(v_b_867_);
lean_dec_ref(v_a_866_);
v___x_1032_ = lean_box(0);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_1032_);
v___x_1034_ = v___x_887_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
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
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec_ref(v_b_867_);
lean_dec_ref(v_a_866_);
v_a_1037_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_884_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_884_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___boxed(lean_object* v_a_1045_, lean_object* v_b_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_1045_, v_b_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec(v_a_1047_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(lean_object* v_a_1060_, lean_object* v_b_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1060_, v_a_1063_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; uint8_t v___x_1076_; lean_object* v___x_1077_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref(v___x_1074_);
v___x_1076_ = 0;
lean_inc_ref(v_a_1060_);
v___x_1077_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_1060_, v___x_1076_, v_a_1075_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1132_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1132_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1132_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
if (lean_obj_tag(v_a_1078_) == 1)
{
lean_object* v_val_1082_; lean_object* v___x_1083_; 
lean_del_object(v___x_1080_);
v_val_1082_ = lean_ctor_get(v_a_1078_, 0);
lean_inc(v_val_1082_);
lean_dec_ref(v_a_1078_);
v___x_1083_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1061_, v_a_1063_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1085_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref(v___x_1083_);
lean_inc_ref(v_b_1061_);
v___x_1085_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_1061_, v___x_1076_, v_a_1084_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1111_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1111_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1111_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
if (lean_obj_tag(v_a_1086_) == 1)
{
lean_object* v_val_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v_val_1090_ = lean_ctor_get(v_a_1086_, 0);
lean_inc_n(v_val_1090_, 2);
lean_dec_ref(v_a_1086_);
lean_inc(v_val_1082_);
v___x_1091_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1091_, 0, v_val_1082_);
lean_ctor_set(v___x_1091_, 1, v_val_1090_);
v___x_1092_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1091_);
v___x_1093_ = lean_box(0);
v___x_1094_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_1092_, v___x_1093_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_del_object(v___x_1088_);
lean_inc(v_val_1090_);
lean_inc(v_val_1082_);
lean_inc_ref(v_b_1061_);
lean_inc_ref(v_a_1060_);
v___x_1095_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1095_, 0, v_a_1060_);
lean_ctor_set(v___x_1095_, 1, v_b_1061_);
lean_ctor_set(v___x_1095_, 2, v_val_1082_);
lean_ctor_set(v___x_1095_, 3, v_val_1090_);
lean_inc(v___x_1092_);
v___x_1096_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1096_, 0, v___x_1092_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*2, v___x_1076_);
v___x_1097_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1096_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_dec_ref(v___x_1097_);
v___x_1098_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_1099_ = l_Lean_Grind_Linarith_Poly_mul(v___x_1092_, v___x_1098_);
v___x_1100_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v___x_1100_, 0, v_b_1061_);
lean_ctor_set(v___x_1100_, 1, v_a_1060_);
lean_ctor_set(v___x_1100_, 2, v_val_1090_);
lean_ctor_set(v___x_1100_, 3, v_val_1082_);
v___x_1101_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
lean_ctor_set_uint8(v___x_1101_, sizeof(void*)*2, v___x_1076_);
v___x_1102_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_1101_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
return v___x_1102_;
}
else
{
lean_dec(v___x_1092_);
lean_dec(v_val_1090_);
lean_dec(v_val_1082_);
lean_dec_ref(v_b_1061_);
lean_dec_ref(v_a_1060_);
return v___x_1097_;
}
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1105_; 
lean_dec(v___x_1092_);
lean_dec(v_val_1090_);
lean_dec(v_val_1082_);
lean_dec_ref(v_b_1061_);
lean_dec_ref(v_a_1060_);
v___x_1103_ = lean_box(0);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1103_);
v___x_1105_ = v___x_1088_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1109_; 
lean_dec(v_a_1086_);
lean_dec(v_val_1082_);
lean_dec_ref(v_b_1061_);
lean_dec_ref(v_a_1060_);
v___x_1107_ = lean_box(0);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1107_);
v___x_1109_ = v___x_1088_;
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
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec(v_val_1082_);
lean_dec_ref(v_b_1061_);
lean_dec_ref(v_a_1060_);
v_a_1112_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1085_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1085_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec(v_val_1082_);
lean_dec_ref(v_b_1061_);
lean_dec_ref(v_a_1060_);
v_a_1120_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1083_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1083_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
else
{
lean_object* v___x_1128_; lean_object* v___x_1130_; 
lean_dec(v_a_1078_);
lean_dec_ref(v_b_1061_);
lean_dec_ref(v_a_1060_);
v___x_1128_ = lean_box(0);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1128_);
v___x_1130_ = v___x_1080_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1128_);
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
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec_ref(v_b_1061_);
lean_dec_ref(v_a_1060_);
v_a_1133_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1077_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1077_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec_ref(v_b_1061_);
lean_dec_ref(v_a_1060_);
v_a_1141_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1074_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1074_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27___boxed(lean_object* v_a_1149_, lean_object* v_b_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_1149_, v_b_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec(v_a_1151_);
return v_res_1163_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(lean_object* v_msg_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; lean_object* v___f_1179_; lean_object* v___x_3483__overap_1180_; lean_object* v___x_1181_; 
v___x_1178_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0);
v___f_1179_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1179_, 0, v___x_1178_);
v___x_3483__overap_1180_ = lean_panic_fn_borrowed(v___f_1179_, v_msg_1165_);
lean_dec_ref(v___f_1179_);
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
lean_inc(v___y_1174_);
lean_inc_ref(v___y_1173_);
lean_inc(v___y_1172_);
lean_inc_ref(v___y_1171_);
lean_inc(v___y_1170_);
lean_inc_ref(v___y_1169_);
lean_inc(v___y_1168_);
lean_inc(v___y_1167_);
lean_inc(v___y_1166_);
v___x_1181_ = lean_apply_12(v___x_3483__overap_1180_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, lean_box(0));
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___boxed(lean_object* v_msg_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v_msg_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec(v___y_1183_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__1(lean_object* v_a_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_nat_to_int(v_a_1196_);
return v___x_1197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__2));
v___x_1202_ = lean_unsigned_to_nat(42u);
v___x_1203_ = lean_unsigned_to_nat(87u);
v___x_1204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__1));
v___x_1205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__0));
v___x_1206_ = l_mkPanicMessageWithDecl(v___x_1205_, v___x_1204_, v___x_1203_, v___x_1202_, v___x_1201_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(lean_object* v_c_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v_c_1223_; lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v_c_1231_; lean_object* v_p_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; uint8_t v___x_1268_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1229_);
lean_dec_ref(v___x_1228_);
v___x_1268_ = lean_unbox(v_a_1229_);
lean_dec(v_a_1229_);
if (v___x_1268_ == 0)
{
lean_object* v_p_1269_; 
v_p_1269_ = lean_ctor_get(v_c_1207_, 0);
lean_inc(v_p_1269_);
v_c_1231_ = v_c_1207_;
v_p_1232_ = v_p_1269_;
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
v___y_1243_ = v_a_1218_;
goto v___jp_1230_;
}
else
{
lean_object* v_p_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v_p_1270_ = lean_ctor_get(v_c_1207_, 0);
v___x_1271_ = l_Lean_Grind_Linarith_Poly_gcdCoeffs(v_p_1270_);
v___x_1272_ = lean_unsigned_to_nat(1u);
v___x_1273_ = lean_nat_dec_eq(v___x_1271_, v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_inc(v___x_1271_);
v___x_1274_ = lean_nat_to_int(v___x_1271_);
lean_inc(v_p_1270_);
v___x_1275_ = l_Lean_Grind_Linarith_Poly_div(v_p_1270_, v___x_1274_);
lean_dec(v___x_1274_);
v___x_1276_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1271_);
lean_ctor_set(v___x_1276_, 1, v_c_1207_);
lean_inc(v___x_1275_);
v___x_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1275_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v_c_1231_ = v___x_1277_;
v_p_1232_ = v___x_1275_;
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
v___y_1243_ = v_a_1218_;
goto v___jp_1230_;
}
else
{
lean_inc(v_p_1270_);
lean_dec(v___x_1271_);
v_c_1231_ = v_c_1207_;
v_p_1232_ = v_p_1270_;
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
v___y_1243_ = v_a_1218_;
goto v___jp_1230_;
}
}
v___jp_1230_:
{
lean_object* v___x_1244_; 
lean_inc(v_p_1232_);
v___x_1244_ = l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(v_p_1232_);
if (lean_obj_tag(v___x_1244_) == 1)
{
lean_object* v_val_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1265_; 
v_val_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1265_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_val_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1265_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v_fst_1249_; lean_object* v_snd_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1264_; 
v_fst_1249_ = lean_ctor_get(v_val_1245_, 0);
v_snd_1250_ = lean_ctor_get(v_val_1245_, 1);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_val_1245_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1252_ = v_val_1245_;
v_isShared_1253_ = v_isSharedCheck_1264_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_snd_1250_);
lean_inc(v_fst_1249_);
lean_dec(v_val_1245_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1264_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_1255_ = lean_int_dec_lt(v_fst_1249_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_del_object(v___x_1252_);
lean_del_object(v___x_1247_);
lean_dec(v_p_1232_);
v___y_1221_ = v_fst_1249_;
v___y_1222_ = v_snd_1250_;
v_c_1223_ = v_c_1231_;
goto v___jp_1220_;
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1256_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_1257_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1232_, v___x_1256_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set_tag(v___x_1247_, 3);
lean_ctor_set(v___x_1247_, 0, v_c_1231_);
v___x_1259_ = v___x_1247_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_c_1231_);
v___x_1259_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1261_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 1, v___x_1259_);
lean_ctor_set(v___x_1252_, 0, v___x_1257_);
v___x_1261_ = v___x_1252_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
v___y_1221_ = v_fst_1249_;
v___y_1222_ = v_snd_1250_;
v_c_1223_ = v___x_1261_;
goto v___jp_1220_;
}
}
}
}
}
}
else
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_dec(v___x_1244_);
lean_dec(v_p_1232_);
lean_dec_ref(v_c_1231_);
v___x_1266_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___closed__3);
v___x_1267_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0(v___x_1266_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
return v___x_1267_;
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec_ref(v_c_1207_);
v_a_1278_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1228_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1228_);
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
v___jp_1220_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1224_ = lean_nat_abs(v___y_1221_);
lean_dec(v___y_1221_);
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___y_1222_);
lean_ctor_set(v___x_1225_, 1, v_c_1223_);
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
return v___x_1227_;
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
lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v_p_1381_; lean_object* v_fileName_1382_; lean_object* v_fileMap_1383_; lean_object* v_options_1384_; lean_object* v_currRecDepth_1385_; lean_object* v_maxRecDepth_1386_; lean_object* v_ref_1387_; lean_object* v_currNamespace_1388_; lean_object* v_openDecls_1389_; lean_object* v_initHeartbeats_1390_; lean_object* v_maxHeartbeats_1391_; lean_object* v_quotContext_1392_; lean_object* v_currMacroScope_1393_; uint8_t v_diag_1394_; lean_object* v_cancelTk_x3f_1395_; uint8_t v_suppressElabErrors_1396_; lean_object* v_inheritedTraceOptions_1397_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
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
v___x_1491_ = lean_unsigned_to_nat(0u);
v___x_1492_ = lean_nat_dec_eq(v_maxRecDepth_1386_, v___x_1491_);
if (v___x_1492_ == 0)
{
uint8_t v___x_1493_; 
v___x_1493_ = lean_nat_dec_eq(v_currRecDepth_1385_, v_maxRecDepth_1386_);
if (v___x_1493_ == 0)
{
goto v___jp_1398_;
}
else
{
lean_object* v___x_1494_; 
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
v___x_1494_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1387_);
return v___x_1494_;
}
}
else
{
goto v___jp_1398_;
}
v___jp_1363_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_1378_, 0, v___y_1366_);
lean_ctor_set(v___x_1378_, 1, v___y_1364_);
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
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1399_ = lean_unsigned_to_nat(1u);
v___x_1400_ = lean_nat_add(v_currRecDepth_1385_, v___x_1399_);
lean_dec(v_currRecDepth_1385_);
lean_inc_ref(v_inheritedTraceOptions_1397_);
lean_inc_ref(v_options_1384_);
v___x_1401_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1401_, 0, v_fileName_1382_);
lean_ctor_set(v___x_1401_, 1, v_fileMap_1383_);
lean_ctor_set(v___x_1401_, 2, v_options_1384_);
lean_ctor_set(v___x_1401_, 3, v___x_1400_);
lean_ctor_set(v___x_1401_, 4, v_maxRecDepth_1386_);
lean_ctor_set(v___x_1401_, 5, v_ref_1387_);
lean_ctor_set(v___x_1401_, 6, v_currNamespace_1388_);
lean_ctor_set(v___x_1401_, 7, v_openDecls_1389_);
lean_ctor_set(v___x_1401_, 8, v_initHeartbeats_1390_);
lean_ctor_set(v___x_1401_, 9, v_maxHeartbeats_1391_);
lean_ctor_set(v___x_1401_, 10, v_quotContext_1392_);
lean_ctor_set(v___x_1401_, 11, v_currMacroScope_1393_);
lean_ctor_set(v___x_1401_, 12, v_cancelTk_x3f_1395_);
lean_ctor_set(v___x_1401_, 13, v_inheritedTraceOptions_1397_);
lean_ctor_set_uint8(v___x_1401_, sizeof(void*)*14, v_diag_1394_);
lean_ctor_set_uint8(v___x_1401_, sizeof(void*)*14 + 1, v_suppressElabErrors_1396_);
lean_inc(v_p_1381_);
v___x_1402_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_1381_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v___x_1401_, v_a_1361_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1482_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1482_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1482_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
if (lean_obj_tag(v_a_1403_) == 1)
{
lean_object* v_val_1407_; lean_object* v_snd_1408_; uint8_t v_hasTrace_1409_; 
lean_del_object(v___x_1405_);
v_val_1407_ = lean_ctor_get(v_a_1403_, 0);
lean_inc(v_val_1407_);
lean_dec_ref(v_a_1403_);
v_snd_1408_ = lean_ctor_get(v_val_1407_, 1);
lean_inc(v_snd_1408_);
v_hasTrace_1409_ = lean_ctor_get_uint8(v_options_1384_, sizeof(void*)*1);
if (v_hasTrace_1409_ == 0)
{
lean_object* v_fst_1410_; lean_object* v_fst_1411_; lean_object* v_snd_1412_; 
lean_dec_ref(v_inheritedTraceOptions_1397_);
lean_dec_ref(v_options_1384_);
v_fst_1410_ = lean_ctor_get(v_val_1407_, 0);
lean_inc(v_fst_1410_);
lean_dec(v_val_1407_);
v_fst_1411_ = lean_ctor_get(v_snd_1408_, 0);
lean_inc(v_fst_1411_);
v_snd_1412_ = lean_ctor_get(v_snd_1408_, 1);
lean_inc(v_snd_1412_);
lean_dec(v_snd_1408_);
v___y_1364_ = v_fst_1411_;
v___y_1365_ = v_snd_1412_;
v___y_1366_ = v_fst_1410_;
v___y_1367_ = v_a_1351_;
v___y_1368_ = v_a_1352_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v_a_1359_;
v___y_1376_ = v___x_1401_;
v___y_1377_ = v_a_1361_;
goto v___jp_1363_;
}
else
{
lean_object* v_fst_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1477_; 
v_fst_1413_ = lean_ctor_get(v_val_1407_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v_val_1407_);
if (v_isSharedCheck_1477_ == 0)
{
lean_object* v_unused_1478_; 
v_unused_1478_ = lean_ctor_get(v_val_1407_, 1);
lean_dec(v_unused_1478_);
v___x_1415_ = v_val_1407_;
v_isShared_1416_ = v_isSharedCheck_1477_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_fst_1413_);
lean_dec(v_val_1407_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1477_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v_fst_1417_; lean_object* v_snd_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1476_; 
v_fst_1417_ = lean_ctor_get(v_snd_1408_, 0);
v_snd_1418_ = lean_ctor_get(v_snd_1408_, 1);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_snd_1408_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1420_ = v_snd_1408_;
v_isShared_1421_ = v_isSharedCheck_1476_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_snd_1418_);
lean_inc(v_fst_1417_);
lean_dec(v_snd_1408_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1476_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1422_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_1423_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_1424_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1397_, v_options_1384_, v___x_1423_);
lean_dec_ref(v_options_1384_);
lean_dec_ref(v_inheritedTraceOptions_1397_);
if (v___x_1424_ == 0)
{
lean_del_object(v___x_1420_);
lean_del_object(v___x_1415_);
v___y_1364_ = v_fst_1417_;
v___y_1365_ = v_snd_1418_;
v___y_1366_ = v_fst_1413_;
v___y_1367_ = v_a_1351_;
v___y_1368_ = v_a_1352_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v_a_1359_;
v___y_1376_ = v___x_1401_;
v___y_1377_ = v_a_1361_;
goto v___jp_1363_;
}
else
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_1413_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v___x_1401_, v_a_1361_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1427_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref(v___x_1425_);
v___x_1427_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v___x_1401_, v_a_1361_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1429_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref(v___x_1427_);
v___x_1429_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_fst_1417_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v___x_1401_, v_a_1361_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1434_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref(v___x_1429_);
v___x_1431_ = l_Lean_MessageData_ofExpr(v_a_1426_);
v___x_1432_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_1421_ == 0)
{
lean_ctor_set_tag(v___x_1420_, 7);
lean_ctor_set(v___x_1420_, 1, v___x_1432_);
lean_ctor_set(v___x_1420_, 0, v___x_1431_);
v___x_1434_ = v___x_1420_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1435_ = l_Lean_MessageData_ofExpr(v_a_1428_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set_tag(v___x_1415_, 7);
lean_ctor_set(v___x_1415_, 1, v___x_1435_);
lean_ctor_set(v___x_1415_, 0, v___x_1434_);
v___x_1437_ = v___x_1415_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
lean_ctor_set(v___x_1438_, 1, v___x_1432_);
v___x_1439_ = l_Lean_MessageData_ofExpr(v_a_1430_);
v___x_1440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1438_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
v___x_1441_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_1422_, v___x_1440_, v_a_1358_, v_a_1359_, v___x_1401_, v_a_1361_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_dec_ref(v___x_1441_);
v___y_1364_ = v_fst_1417_;
v___y_1365_ = v_snd_1418_;
v___y_1366_ = v_fst_1413_;
v___y_1367_ = v_a_1351_;
v___y_1368_ = v_a_1352_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v_a_1359_;
v___y_1376_ = v___x_1401_;
v___y_1377_ = v_a_1361_;
goto v___jp_1363_;
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v_snd_1418_);
lean_dec(v_fst_1417_);
lean_dec(v_fst_1413_);
lean_dec_ref(v___x_1401_);
lean_dec_ref(v_c_1350_);
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1441_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1441_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec(v_a_1428_);
lean_dec(v_a_1426_);
lean_del_object(v___x_1420_);
lean_dec(v_snd_1418_);
lean_dec(v_fst_1417_);
lean_del_object(v___x_1415_);
lean_dec(v_fst_1413_);
lean_dec_ref(v___x_1401_);
lean_dec_ref(v_c_1350_);
v_a_1452_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1429_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1429_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
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
lean_dec(v_a_1426_);
lean_del_object(v___x_1420_);
lean_dec(v_snd_1418_);
lean_dec(v_fst_1417_);
lean_del_object(v___x_1415_);
lean_dec(v_fst_1413_);
lean_dec_ref(v___x_1401_);
lean_dec_ref(v_c_1350_);
v_a_1460_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1427_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1427_);
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
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_del_object(v___x_1420_);
lean_dec(v_snd_1418_);
lean_dec(v_fst_1417_);
lean_del_object(v___x_1415_);
lean_dec(v_fst_1413_);
lean_dec_ref(v___x_1401_);
lean_dec_ref(v_c_1350_);
v_a_1468_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1425_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1425_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
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
lean_object* v___x_1480_; 
lean_dec(v_a_1403_);
lean_dec_ref(v___x_1401_);
lean_dec_ref(v_inheritedTraceOptions_1397_);
lean_dec_ref(v_options_1384_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v_c_1350_);
v___x_1480_ = v___x_1405_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_c_1350_);
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
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec_ref(v___x_1401_);
lean_dec_ref(v_inheritedTraceOptions_1397_);
lean_dec_ref(v_options_1384_);
lean_dec_ref(v_c_1350_);
v_a_1483_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1402_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1402_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object* v_c_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
lean_dec(v_a_1506_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec(v_a_1496_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_ref_1515_; lean_object* v___x_1516_; lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1525_; 
v_ref_1515_ = lean_ctor_get(v___y_1512_, 5);
v___x_1516_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msg_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1519_ = v___x_1516_;
v_isShared_1520_ = v_isSharedCheck_1525_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1516_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1525_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
lean_inc(v_ref_1515_);
v___x_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1521_, 0, v_ref_1515_);
lean_ctor_set(v___x_1521_, 1, v_a_1517_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set_tag(v___x_1519_, 1);
lean_ctor_set(v___x_1519_, 0, v___x_1521_);
v___x_1523_ = v___x_1519_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1521_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
return v_res_1532_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0));
v___x_1535_ = l_Lean_stringToMessageData(v___x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1560_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1551_ = v___x_1548_;
v_isShared_1552_ = v_isSharedCheck_1560_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1548_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1560_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v_leFn_x3f_1553_; 
v_leFn_x3f_1553_ = lean_ctor_get(v_a_1549_, 20);
lean_inc(v_leFn_x3f_1553_);
lean_dec(v_a_1549_);
if (lean_obj_tag(v_leFn_x3f_1553_) == 1)
{
lean_object* v_val_1554_; lean_object* v___x_1556_; 
v_val_1554_ = lean_ctor_get(v_leFn_x3f_1553_, 0);
lean_inc(v_val_1554_);
lean_dec_ref(v_leFn_x3f_1553_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v_val_1554_);
v___x_1556_ = v___x_1551_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_val_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
lean_dec(v_leFn_x3f_1553_);
lean_del_object(v___x_1551_);
v___x_1558_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1);
v___x_1559_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1558_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
return v___x_1559_;
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
v_a_1561_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1548_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1548_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___boxed(lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec(v___y_1569_);
return v_res_1581_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0));
v___x_1584_ = l_Lean_stringToMessageData(v___x_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1609_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1609_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1609_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v_ltFn_x3f_1602_; 
v_ltFn_x3f_1602_ = lean_ctor_get(v_a_1598_, 21);
lean_inc(v_ltFn_x3f_1602_);
lean_dec(v_a_1598_);
if (lean_obj_tag(v_ltFn_x3f_1602_) == 1)
{
lean_object* v_val_1603_; lean_object* v___x_1605_; 
v_val_1603_ = lean_ctor_get(v_ltFn_x3f_1602_, 0);
lean_inc(v_val_1603_);
lean_dec_ref(v_ltFn_x3f_1602_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v_val_1603_);
v___x_1605_ = v___x_1600_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_val_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_dec(v_ltFn_x3f_1602_);
lean_del_object(v___x_1600_);
v___x_1607_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1);
v___x_1608_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1607_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
return v___x_1608_;
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
v_a_1610_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1597_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1597_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___boxed(lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec(v___y_1618_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(lean_object* v_p_1631_, uint8_t v_strict_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
if (v_strict_1632_ == 0)
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref(v___x_1645_);
v___x_1647_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1631_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1649_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref(v___x_1647_);
v___x_1649_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
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
else
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1670_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref(v___x_1668_);
v___x_1670_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1631_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1672_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref(v___x_1670_);
v___x_1672_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1682_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1682_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1682_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v_ofNatZero_1677_; lean_object* v___x_1678_; lean_object* v___x_1680_; 
v_ofNatZero_1677_ = lean_ctor_get(v_a_1673_, 18);
lean_inc_ref(v_ofNatZero_1677_);
lean_dec(v_a_1673_);
v___x_1678_ = l_Lean_mkAppB(v_a_1669_, v_a_1671_, v_ofNatZero_1677_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1678_);
v___x_1680_ = v___x_1675_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec(v_a_1671_);
lean_dec(v_a_1669_);
v_a_1683_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1672_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1672_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
else
{
lean_dec(v_a_1669_);
return v___x_1670_;
}
}
else
{
return v___x_1668_;
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(lean_object* v_c_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v_p_1720_; uint8_t v_strict_1721_; lean_object* v___x_1722_; 
v_p_1720_ = lean_ctor_get(v_c_1707_, 0);
v_strict_1721_ = lean_ctor_get_uint8(v_c_1707_, sizeof(void*)*2);
v___x_1722_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1720_, v_strict_1721_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0___boxed(lean_object* v_c_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v_c_1723_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object* v_a_1737_, lean_object* v_x_1738_, lean_object* v_c_u2081_1739_, lean_object* v_b_1740_, lean_object* v_c_u2082_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v_options_1754_; lean_object* v_p_1755_; lean_object* v_p_1756_; uint8_t v_strict_1757_; lean_object* v_inheritedTraceOptions_1758_; uint8_t v_hasTrace_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v_p_1764_; 
v_options_1754_ = lean_ctor_get(v_a_1751_, 2);
v_p_1755_ = lean_ctor_get(v_c_u2081_1739_, 0);
v_p_1756_ = lean_ctor_get(v_c_u2082_1741_, 0);
v_strict_1757_ = lean_ctor_get_uint8(v_c_u2082_1741_, sizeof(void*)*2);
v_inheritedTraceOptions_1758_ = lean_ctor_get(v_a_1751_, 13);
v_hasTrace_1759_ = lean_ctor_get_uint8(v_options_1754_, sizeof(void*)*1);
v___x_1760_ = lean_nat_to_int(v_a_1737_);
lean_inc(v_p_1756_);
v___x_1761_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1756_, v___x_1760_);
lean_dec(v___x_1760_);
v___x_1762_ = lean_int_neg(v_b_1740_);
lean_inc(v_p_1755_);
v___x_1763_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1755_, v___x_1762_);
lean_dec(v___x_1762_);
v_p_1764_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1761_, v___x_1763_);
if (v_hasTrace_1759_ == 0)
{
goto v___jp_1765_;
}
else
{
lean_object* v_cls_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v_cls_1769_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_1770_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2);
v___x_1771_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1758_, v_options_1754_, v___x_1770_);
if (v___x_1771_ == 0)
{
goto v___jp_1765_;
}
else
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1738_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref(v___x_1772_);
v___x_1774_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_1739_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1776_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref(v___x_1774_);
v___x_1776_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_u2082_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref(v___x_1776_);
v___x_1778_ = l_Lean_MessageData_ofExpr(v_a_1773_);
v___x_1779_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_1780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1778_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = l_Lean_MessageData_ofExpr(v_a_1775_);
v___x_1782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1780_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
lean_ctor_set(v___x_1783_, 1, v___x_1779_);
v___x_1784_ = l_Lean_MessageData_ofExpr(v_a_1777_);
v___x_1785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1783_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
v___x_1786_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_1769_, v___x_1785_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_dec_ref(v___x_1786_);
goto v___jp_1765_;
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec(v_p_1764_);
lean_dec_ref(v_c_u2082_1741_);
lean_dec_ref(v_c_u2081_1739_);
lean_dec(v_x_1738_);
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1786_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec(v_a_1775_);
lean_dec(v_a_1773_);
lean_dec(v_p_1764_);
lean_dec_ref(v_c_u2082_1741_);
lean_dec_ref(v_c_u2081_1739_);
lean_dec(v_x_1738_);
v_a_1795_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1776_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1776_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec(v_a_1773_);
lean_dec(v_p_1764_);
lean_dec_ref(v_c_u2082_1741_);
lean_dec_ref(v_c_u2081_1739_);
lean_dec(v_x_1738_);
v_a_1803_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1774_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1774_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
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
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec(v_p_1764_);
lean_dec_ref(v_c_u2082_1741_);
lean_dec_ref(v_c_u2081_1739_);
lean_dec(v_x_1738_);
v_a_1811_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1772_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1772_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
v___jp_1765_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = lean_alloc_ctor(13, 3, 0);
lean_ctor_set(v___x_1766_, 0, v_x_1738_);
lean_ctor_set(v___x_1766_, 1, v_c_u2081_1739_);
lean_ctor_set(v___x_1766_, 2, v_c_u2082_1741_);
v___x_1767_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1767_, 0, v_p_1764_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
lean_ctor_set_uint8(v___x_1767_, sizeof(void*)*2, v_strict_1757_);
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
return v___x_1768_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object** _args){
lean_object* v_a_1819_ = _args[0];
lean_object* v_x_1820_ = _args[1];
lean_object* v_c_u2081_1821_ = _args[2];
lean_object* v_b_1822_ = _args[3];
lean_object* v_c_u2082_1823_ = _args[4];
lean_object* v_a_1824_ = _args[5];
lean_object* v_a_1825_ = _args[6];
lean_object* v_a_1826_ = _args[7];
lean_object* v_a_1827_ = _args[8];
lean_object* v_a_1828_ = _args[9];
lean_object* v_a_1829_ = _args[10];
lean_object* v_a_1830_ = _args[11];
lean_object* v_a_1831_ = _args[12];
lean_object* v_a_1832_ = _args[13];
lean_object* v_a_1833_ = _args[14];
lean_object* v_a_1834_ = _args[15];
lean_object* v_a_1835_ = _args[16];
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1819_, v_x_1820_, v_c_u2081_1821_, v_b_1822_, v_c_u2082_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_a_1826_);
lean_dec(v_a_1825_);
lean_dec(v_a_1824_);
lean_dec(v_b_1822_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1837_, lean_object* v_msg_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1838_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1852_, lean_object* v_msg_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1852_, v_msg_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec(v___y_1854_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(lean_object* v_a_1875_, lean_object* v_x_1876_, lean_object* v_c_u2081_1877_, lean_object* v_as_1878_, size_t v_sz_1879_, size_t v_i_1880_, lean_object* v_b_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
uint8_t v___x_1894_; 
v___x_1894_ = lean_usize_dec_lt(v_i_1880_, v_sz_1879_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; 
lean_dec_ref(v_c_u2081_1877_);
lean_dec(v_x_1876_);
lean_dec(v_a_1875_);
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v_b_1881_);
return v___x_1895_;
}
else
{
lean_object* v_a_1896_; lean_object* v_fst_1897_; lean_object* v_snd_1898_; lean_object* v___x_1899_; 
lean_dec_ref(v_b_1881_);
v_a_1896_ = lean_array_uget_borrowed(v_as_1878_, v_i_1880_);
v_fst_1897_ = lean_ctor_get(v_a_1896_, 0);
v_snd_1898_ = lean_ctor_get(v_a_1896_, 1);
lean_inc(v_snd_1898_);
lean_inc_ref(v_c_u2081_1877_);
lean_inc(v_x_1876_);
lean_inc(v_a_1875_);
v___x_1899_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1875_, v_x_1876_, v_c_u2081_1877_, v_fst_1897_, v_snd_1898_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1901_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref(v___x_1899_);
v___x_1901_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_a_1900_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v___x_1902_; 
lean_dec_ref(v___x_1901_);
v___x_1902_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1916_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1905_ = v___x_1902_;
v_isShared_1906_ = v_isSharedCheck_1916_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1902_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1916_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
uint8_t v___x_1907_; 
v___x_1907_ = lean_unbox(v_a_1903_);
lean_dec(v_a_1903_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; size_t v___x_1909_; size_t v___x_1910_; 
lean_del_object(v___x_1905_);
v___x_1908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v___x_1909_ = ((size_t)1ULL);
v___x_1910_ = lean_usize_add(v_i_1880_, v___x_1909_);
v_i_1880_ = v___x_1910_;
v_b_1881_ = v___x_1908_;
goto _start;
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1914_; 
lean_dec_ref(v_c_u2081_1877_);
lean_dec(v_x_1876_);
lean_dec(v_a_1875_);
v___x_1912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 0, v___x_1912_);
v___x_1914_ = v___x_1905_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec_ref(v_c_u2081_1877_);
lean_dec(v_x_1876_);
lean_dec(v_a_1875_);
v_a_1917_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1902_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1902_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_dec_ref(v_c_u2081_1877_);
lean_dec(v_x_1876_);
lean_dec(v_a_1875_);
v_a_1925_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1901_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1901_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec_ref(v_c_u2081_1877_);
lean_dec(v_x_1876_);
lean_dec(v_a_1875_);
v_a_1933_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1899_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1899_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___boxed(lean_object** _args){
lean_object* v_a_1941_ = _args[0];
lean_object* v_x_1942_ = _args[1];
lean_object* v_c_u2081_1943_ = _args[2];
lean_object* v_as_1944_ = _args[3];
lean_object* v_sz_1945_ = _args[4];
lean_object* v_i_1946_ = _args[5];
lean_object* v_b_1947_ = _args[6];
lean_object* v___y_1948_ = _args[7];
lean_object* v___y_1949_ = _args[8];
lean_object* v___y_1950_ = _args[9];
lean_object* v___y_1951_ = _args[10];
lean_object* v___y_1952_ = _args[11];
lean_object* v___y_1953_ = _args[12];
lean_object* v___y_1954_ = _args[13];
lean_object* v___y_1955_ = _args[14];
lean_object* v___y_1956_ = _args[15];
lean_object* v___y_1957_ = _args[16];
lean_object* v___y_1958_ = _args[17];
lean_object* v___y_1959_ = _args[18];
_start:
{
size_t v_sz_boxed_1960_; size_t v_i_boxed_1961_; lean_object* v_res_1962_; 
v_sz_boxed_1960_ = lean_unbox_usize(v_sz_1945_);
lean_dec(v_sz_1945_);
v_i_boxed_1961_ = lean_unbox_usize(v_i_1946_);
lean_dec(v_i_1946_);
v_res_1962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1941_, v_x_1942_, v_c_u2081_1943_, v_as_1944_, v_sz_boxed_1960_, v_i_boxed_1961_, v_b_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v_as_1944_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(lean_object* v_a_1963_, lean_object* v_x_1964_, lean_object* v_c_u2081_1965_, lean_object* v_todo_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; size_t v_sz_1981_; size_t v___x_1982_; lean_object* v___x_1983_; 
v___x_1979_ = lean_box(0);
v___x_1980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_1981_ = lean_array_size(v_todo_1966_);
v___x_1982_ = ((size_t)0ULL);
v___x_1983_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1963_, v_x_1964_, v_c_u2081_1965_, v_todo_1966_, v_sz_1981_, v___x_1982_, v___x_1980_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1996_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_1996_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1996_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v_fst_1988_; 
v_fst_1988_ = lean_ctor_get(v_a_1984_, 0);
lean_inc(v_fst_1988_);
lean_dec(v_a_1984_);
if (lean_obj_tag(v_fst_1988_) == 0)
{
lean_object* v___x_1990_; 
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_1979_);
v___x_1990_ = v___x_1986_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1979_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
else
{
lean_object* v_val_1992_; lean_object* v___x_1994_; 
v_val_1992_ = lean_ctor_get(v_fst_1988_, 0);
lean_inc(v_val_1992_);
lean_dec_ref(v_fst_1988_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v_val_1992_);
v___x_1994_ = v___x_1986_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_val_1992_);
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
v_a_1997_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1983_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1983_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object* v_a_2005_, lean_object* v_x_2006_, lean_object* v_c_u2081_2007_, lean_object* v_todo_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2005_, v_x_2006_, v_c_u2081_2007_, v_todo_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_todo_2008_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_2022_, lean_object* v_as_2023_, size_t v_sz_2024_, size_t v_i_2025_, lean_object* v_b_2026_){
_start:
{
uint8_t v___x_2027_; 
v___x_2027_ = lean_usize_dec_lt(v_i_2025_, v_sz_2024_);
if (v___x_2027_ == 0)
{
return v_b_2026_;
}
else
{
lean_object* v_snd_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2061_; 
v_snd_2028_ = lean_ctor_get(v_b_2026_, 1);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_b_2026_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v_b_2026_, 0);
lean_dec(v_unused_2062_);
v___x_2030_ = v_b_2026_;
v_isShared_2031_ = v_isSharedCheck_2061_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_snd_2028_);
lean_dec(v_b_2026_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2061_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v_fst_2032_; lean_object* v_snd_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2060_; 
v_fst_2032_ = lean_ctor_get(v_snd_2028_, 0);
v_snd_2033_ = lean_ctor_get(v_snd_2028_, 1);
v_isSharedCheck_2060_ = !lean_is_exclusive(v_snd_2028_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2035_ = v_snd_2028_;
v_isShared_2036_ = v_isSharedCheck_2060_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_snd_2033_);
lean_inc(v_fst_2032_);
lean_dec(v_snd_2028_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2060_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v_a_2037_; lean_object* v_p_2038_; lean_object* v___x_2039_; lean_object* v_a_2041_; lean_object* v_b_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; 
v_a_2037_ = lean_array_uget_borrowed(v_as_2023_, v_i_2025_);
v_p_2038_ = lean_ctor_get(v_a_2037_, 0);
v___x_2039_ = lean_box(0);
v_b_2048_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2038_, v_x_2022_);
v___x_2049_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2050_ = lean_int_dec_eq(v_b_2048_, v___x_2049_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2052_; 
lean_inc(v_a_2037_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 1, v_a_2037_);
lean_ctor_set(v___x_2030_, 0, v_b_2048_);
v___x_2052_ = v___x_2030_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_b_2048_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_a_2037_);
v___x_2052_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
lean_object* v_todo_2053_; lean_object* v___x_2054_; 
v_todo_2053_ = lean_array_push(v_snd_2033_, v___x_2052_);
v___x_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2054_, 0, v_fst_2032_);
lean_ctor_set(v___x_2054_, 1, v_todo_2053_);
v_a_2041_ = v___x_2054_;
goto v___jp_2040_;
}
}
else
{
lean_object* v_cs_x27_2056_; lean_object* v___x_2058_; 
lean_dec(v_b_2048_);
lean_inc(v_a_2037_);
v_cs_x27_2056_ = l_Lean_PersistentArray_push___redArg(v_fst_2032_, v_a_2037_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 1, v_snd_2033_);
lean_ctor_set(v___x_2030_, 0, v_cs_x27_2056_);
v___x_2058_ = v___x_2030_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_cs_x27_2056_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_snd_2033_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
v_a_2041_ = v___x_2058_;
goto v___jp_2040_;
}
}
v___jp_2040_:
{
lean_object* v___x_2043_; 
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 1, v_a_2041_);
lean_ctor_set(v___x_2035_, 0, v___x_2039_);
v___x_2043_ = v___x_2035_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_a_2041_);
v___x_2043_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
size_t v___x_2044_; size_t v___x_2045_; 
v___x_2044_ = ((size_t)1ULL);
v___x_2045_ = lean_usize_add(v_i_2025_, v___x_2044_);
v_i_2025_ = v___x_2045_;
v_b_2026_ = v___x_2043_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_2063_, lean_object* v_as_2064_, lean_object* v_sz_2065_, lean_object* v_i_2066_, lean_object* v_b_2067_){
_start:
{
size_t v_sz_boxed_2068_; size_t v_i_boxed_2069_; lean_object* v_res_2070_; 
v_sz_boxed_2068_ = lean_unbox_usize(v_sz_2065_);
lean_dec(v_sz_2065_);
v_i_boxed_2069_ = lean_unbox_usize(v_i_2066_);
lean_dec(v_i_2066_);
v_res_2070_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2063_, v_as_2064_, v_sz_boxed_2068_, v_i_boxed_2069_, v_b_2067_);
lean_dec_ref(v_as_2064_);
lean_dec(v_x_2063_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(lean_object* v_x_2071_, lean_object* v_as_2072_, size_t v_sz_2073_, size_t v_i_2074_, lean_object* v_b_2075_){
_start:
{
uint8_t v___x_2076_; 
v___x_2076_ = lean_usize_dec_lt(v_i_2074_, v_sz_2073_);
if (v___x_2076_ == 0)
{
return v_b_2075_;
}
else
{
lean_object* v_snd_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2110_; 
v_snd_2077_ = lean_ctor_get(v_b_2075_, 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_b_2075_);
if (v_isSharedCheck_2110_ == 0)
{
lean_object* v_unused_2111_; 
v_unused_2111_ = lean_ctor_get(v_b_2075_, 0);
lean_dec(v_unused_2111_);
v___x_2079_ = v_b_2075_;
v_isShared_2080_ = v_isSharedCheck_2110_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_snd_2077_);
lean_dec(v_b_2075_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2110_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v_fst_2081_; lean_object* v_snd_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2109_; 
v_fst_2081_ = lean_ctor_get(v_snd_2077_, 0);
v_snd_2082_ = lean_ctor_get(v_snd_2077_, 1);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_snd_2077_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2084_ = v_snd_2077_;
v_isShared_2085_ = v_isSharedCheck_2109_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_snd_2082_);
lean_inc(v_fst_2081_);
lean_dec(v_snd_2077_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2109_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v_a_2086_; lean_object* v_p_2087_; lean_object* v___x_2088_; lean_object* v_a_2090_; lean_object* v_b_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v_a_2086_ = lean_array_uget_borrowed(v_as_2072_, v_i_2074_);
v_p_2087_ = lean_ctor_get(v_a_2086_, 0);
v___x_2088_ = lean_box(0);
v_b_2097_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2087_, v_x_2071_);
v___x_2098_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2099_ = lean_int_dec_eq(v_b_2097_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2101_; 
lean_inc(v_a_2086_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 1, v_a_2086_);
lean_ctor_set(v___x_2079_, 0, v_b_2097_);
v___x_2101_ = v___x_2079_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_b_2097_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_a_2086_);
v___x_2101_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v_todo_2102_; lean_object* v___x_2103_; 
v_todo_2102_ = lean_array_push(v_snd_2082_, v___x_2101_);
v___x_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2103_, 0, v_fst_2081_);
lean_ctor_set(v___x_2103_, 1, v_todo_2102_);
v_a_2090_ = v___x_2103_;
goto v___jp_2089_;
}
}
else
{
lean_object* v_cs_x27_2105_; lean_object* v___x_2107_; 
lean_dec(v_b_2097_);
lean_inc(v_a_2086_);
v_cs_x27_2105_ = l_Lean_PersistentArray_push___redArg(v_fst_2081_, v_a_2086_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 1, v_snd_2082_);
lean_ctor_set(v___x_2079_, 0, v_cs_x27_2105_);
v___x_2107_ = v___x_2079_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_cs_x27_2105_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_snd_2082_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
v_a_2090_ = v___x_2107_;
goto v___jp_2089_;
}
}
v___jp_2089_:
{
lean_object* v___x_2092_; 
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 1, v_a_2090_);
lean_ctor_set(v___x_2084_, 0, v___x_2088_);
v___x_2092_ = v___x_2084_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_a_2090_);
v___x_2092_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
size_t v___x_2093_; size_t v___x_2094_; lean_object* v___x_2095_; 
v___x_2093_ = ((size_t)1ULL);
v___x_2094_ = lean_usize_add(v_i_2074_, v___x_2093_);
v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2071_, v_as_2072_, v_sz_2073_, v___x_2094_, v___x_2092_);
return v___x_2095_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2112_, lean_object* v_as_2113_, lean_object* v_sz_2114_, lean_object* v_i_2115_, lean_object* v_b_2116_){
_start:
{
size_t v_sz_boxed_2117_; size_t v_i_boxed_2118_; lean_object* v_res_2119_; 
v_sz_boxed_2117_ = lean_unbox_usize(v_sz_2114_);
lean_dec(v_sz_2114_);
v_i_boxed_2118_ = lean_unbox_usize(v_i_2115_);
lean_dec(v_i_2115_);
v_res_2119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2112_, v_as_2113_, v_sz_boxed_2117_, v_i_boxed_2118_, v_b_2116_);
lean_dec_ref(v_as_2113_);
lean_dec(v_x_2112_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_2120_, lean_object* v_as_2121_, size_t v_sz_2122_, size_t v_i_2123_, lean_object* v_b_2124_){
_start:
{
uint8_t v___x_2125_; 
v___x_2125_ = lean_usize_dec_lt(v_i_2123_, v_sz_2122_);
if (v___x_2125_ == 0)
{
return v_b_2124_;
}
else
{
lean_object* v_snd_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2159_; 
v_snd_2126_ = lean_ctor_get(v_b_2124_, 1);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_b_2124_);
if (v_isSharedCheck_2159_ == 0)
{
lean_object* v_unused_2160_; 
v_unused_2160_ = lean_ctor_get(v_b_2124_, 0);
lean_dec(v_unused_2160_);
v___x_2128_ = v_b_2124_;
v_isShared_2129_ = v_isSharedCheck_2159_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_snd_2126_);
lean_dec(v_b_2124_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2159_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v_fst_2130_; lean_object* v_snd_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2158_; 
v_fst_2130_ = lean_ctor_get(v_snd_2126_, 0);
v_snd_2131_ = lean_ctor_get(v_snd_2126_, 1);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_snd_2126_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2133_ = v_snd_2126_;
v_isShared_2134_ = v_isSharedCheck_2158_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_snd_2131_);
lean_inc(v_fst_2130_);
lean_dec(v_snd_2126_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2158_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v_a_2135_; lean_object* v_p_2136_; lean_object* v___x_2137_; lean_object* v_a_2139_; lean_object* v_b_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; 
v_a_2135_ = lean_array_uget_borrowed(v_as_2121_, v_i_2123_);
v_p_2136_ = lean_ctor_get(v_a_2135_, 0);
v___x_2137_ = lean_box(0);
v_b_2146_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2136_, v_x_2120_);
v___x_2147_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2148_ = lean_int_dec_eq(v_b_2146_, v___x_2147_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2150_; 
lean_inc(v_a_2135_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 1, v_a_2135_);
lean_ctor_set(v___x_2128_, 0, v_b_2146_);
v___x_2150_ = v___x_2128_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_b_2146_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_a_2135_);
v___x_2150_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v_todo_2151_; lean_object* v___x_2152_; 
v_todo_2151_ = lean_array_push(v_snd_2131_, v___x_2150_);
v___x_2152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2152_, 0, v_fst_2130_);
lean_ctor_set(v___x_2152_, 1, v_todo_2151_);
v_a_2139_ = v___x_2152_;
goto v___jp_2138_;
}
}
else
{
lean_object* v_cs_x27_2154_; lean_object* v___x_2156_; 
lean_dec(v_b_2146_);
lean_inc(v_a_2135_);
v_cs_x27_2154_ = l_Lean_PersistentArray_push___redArg(v_fst_2130_, v_a_2135_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 1, v_snd_2131_);
lean_ctor_set(v___x_2128_, 0, v_cs_x27_2154_);
v___x_2156_ = v___x_2128_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_cs_x27_2154_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_snd_2131_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
v_a_2139_ = v___x_2156_;
goto v___jp_2138_;
}
}
v___jp_2138_:
{
lean_object* v___x_2141_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 1, v_a_2139_);
lean_ctor_set(v___x_2133_, 0, v___x_2137_);
v___x_2141_ = v___x_2133_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_a_2139_);
v___x_2141_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
size_t v___x_2142_; size_t v___x_2143_; 
v___x_2142_ = ((size_t)1ULL);
v___x_2143_ = lean_usize_add(v_i_2123_, v___x_2142_);
v_i_2123_ = v___x_2143_;
v_b_2124_ = v___x_2141_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_2161_, lean_object* v_as_2162_, lean_object* v_sz_2163_, lean_object* v_i_2164_, lean_object* v_b_2165_){
_start:
{
size_t v_sz_boxed_2166_; size_t v_i_boxed_2167_; lean_object* v_res_2168_; 
v_sz_boxed_2166_ = lean_unbox_usize(v_sz_2163_);
lean_dec(v_sz_2163_);
v_i_boxed_2167_ = lean_unbox_usize(v_i_2164_);
lean_dec(v_i_2164_);
v_res_2168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2161_, v_as_2162_, v_sz_boxed_2166_, v_i_boxed_2167_, v_b_2165_);
lean_dec_ref(v_as_2162_);
lean_dec(v_x_2161_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2169_, lean_object* v_as_2170_, size_t v_sz_2171_, size_t v_i_2172_, lean_object* v_b_2173_){
_start:
{
uint8_t v___x_2174_; 
v___x_2174_ = lean_usize_dec_lt(v_i_2172_, v_sz_2171_);
if (v___x_2174_ == 0)
{
return v_b_2173_;
}
else
{
lean_object* v_snd_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2208_; 
v_snd_2175_ = lean_ctor_get(v_b_2173_, 1);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_b_2173_);
if (v_isSharedCheck_2208_ == 0)
{
lean_object* v_unused_2209_; 
v_unused_2209_ = lean_ctor_get(v_b_2173_, 0);
lean_dec(v_unused_2209_);
v___x_2177_ = v_b_2173_;
v_isShared_2178_ = v_isSharedCheck_2208_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_snd_2175_);
lean_dec(v_b_2173_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2208_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v_fst_2179_; lean_object* v_snd_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2207_; 
v_fst_2179_ = lean_ctor_get(v_snd_2175_, 0);
v_snd_2180_ = lean_ctor_get(v_snd_2175_, 1);
v_isSharedCheck_2207_ = !lean_is_exclusive(v_snd_2175_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2182_ = v_snd_2175_;
v_isShared_2183_ = v_isSharedCheck_2207_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_snd_2180_);
lean_inc(v_fst_2179_);
lean_dec(v_snd_2175_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2207_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v_a_2184_; lean_object* v_p_2185_; lean_object* v___x_2186_; lean_object* v_a_2188_; lean_object* v_b_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v_a_2184_ = lean_array_uget_borrowed(v_as_2170_, v_i_2172_);
v_p_2185_ = lean_ctor_get(v_a_2184_, 0);
v___x_2186_ = lean_box(0);
v_b_2195_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2185_, v_x_2169_);
v___x_2196_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2197_ = lean_int_dec_eq(v_b_2195_, v___x_2196_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2199_; 
lean_inc(v_a_2184_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 1, v_a_2184_);
lean_ctor_set(v___x_2177_, 0, v_b_2195_);
v___x_2199_ = v___x_2177_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_b_2195_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_a_2184_);
v___x_2199_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
lean_object* v_todo_2200_; lean_object* v___x_2201_; 
v_todo_2200_ = lean_array_push(v_snd_2180_, v___x_2199_);
v___x_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2201_, 0, v_fst_2179_);
lean_ctor_set(v___x_2201_, 1, v_todo_2200_);
v_a_2188_ = v___x_2201_;
goto v___jp_2187_;
}
}
else
{
lean_object* v_cs_x27_2203_; lean_object* v___x_2205_; 
lean_dec(v_b_2195_);
lean_inc(v_a_2184_);
v_cs_x27_2203_ = l_Lean_PersistentArray_push___redArg(v_fst_2179_, v_a_2184_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 1, v_snd_2180_);
lean_ctor_set(v___x_2177_, 0, v_cs_x27_2203_);
v___x_2205_ = v___x_2177_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_cs_x27_2203_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_snd_2180_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
v_a_2188_ = v___x_2205_;
goto v___jp_2187_;
}
}
v___jp_2187_:
{
lean_object* v___x_2190_; 
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 1, v_a_2188_);
lean_ctor_set(v___x_2182_, 0, v___x_2186_);
v___x_2190_ = v___x_2182_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2186_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_a_2188_);
v___x_2190_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
size_t v___x_2191_; size_t v___x_2192_; lean_object* v___x_2193_; 
v___x_2191_ = ((size_t)1ULL);
v___x_2192_ = lean_usize_add(v_i_2172_, v___x_2191_);
v___x_2193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2169_, v_as_2170_, v_sz_2171_, v___x_2192_, v___x_2190_);
return v___x_2193_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_2210_, lean_object* v_as_2211_, lean_object* v_sz_2212_, lean_object* v_i_2213_, lean_object* v_b_2214_){
_start:
{
size_t v_sz_boxed_2215_; size_t v_i_boxed_2216_; lean_object* v_res_2217_; 
v_sz_boxed_2215_ = lean_unbox_usize(v_sz_2212_);
lean_dec(v_sz_2212_);
v_i_boxed_2216_ = lean_unbox_usize(v_i_2213_);
lean_dec(v_i_2213_);
v_res_2217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2210_, v_as_2211_, v_sz_boxed_2215_, v_i_boxed_2216_, v_b_2214_);
lean_dec_ref(v_as_2211_);
lean_dec(v_x_2210_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(lean_object* v_init_2218_, lean_object* v_x_2219_, lean_object* v_n_2220_, lean_object* v_b_2221_){
_start:
{
if (lean_obj_tag(v_n_2220_) == 0)
{
lean_object* v_cs_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; size_t v_sz_2225_; size_t v___x_2226_; lean_object* v___x_2227_; lean_object* v_fst_2228_; 
v_cs_2222_ = lean_ctor_get(v_n_2220_, 0);
v___x_2223_ = lean_box(0);
v___x_2224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
lean_ctor_set(v___x_2224_, 1, v_b_2221_);
v_sz_2225_ = lean_array_size(v_cs_2222_);
v___x_2226_ = ((size_t)0ULL);
v___x_2227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2218_, v_x_2219_, v_cs_2222_, v_sz_2225_, v___x_2226_, v___x_2224_);
v_fst_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_fst_2228_);
if (lean_obj_tag(v_fst_2228_) == 0)
{
lean_object* v_snd_2229_; lean_object* v___x_2230_; 
v_snd_2229_ = lean_ctor_get(v___x_2227_, 1);
lean_inc(v_snd_2229_);
lean_dec_ref(v___x_2227_);
v___x_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2230_, 0, v_snd_2229_);
return v___x_2230_;
}
else
{
lean_object* v_val_2231_; 
lean_dec_ref(v___x_2227_);
v_val_2231_ = lean_ctor_get(v_fst_2228_, 0);
lean_inc(v_val_2231_);
lean_dec_ref(v_fst_2228_);
return v_val_2231_;
}
}
else
{
lean_object* v_vs_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; size_t v_sz_2235_; size_t v___x_2236_; lean_object* v___x_2237_; lean_object* v_fst_2238_; 
v_vs_2232_ = lean_ctor_get(v_n_2220_, 0);
v___x_2233_ = lean_box(0);
v___x_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
lean_ctor_set(v___x_2234_, 1, v_b_2221_);
v_sz_2235_ = lean_array_size(v_vs_2232_);
v___x_2236_ = ((size_t)0ULL);
v___x_2237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2219_, v_vs_2232_, v_sz_2235_, v___x_2236_, v___x_2234_);
v_fst_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_fst_2238_);
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
lean_dec_ref(v___x_2237_);
v_val_2241_ = lean_ctor_get(v_fst_2238_, 0);
lean_inc(v_val_2241_);
lean_dec_ref(v_fst_2238_);
return v_val_2241_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_2242_, lean_object* v_x_2243_, lean_object* v_as_2244_, size_t v_sz_2245_, size_t v_i_2246_, lean_object* v_b_2247_){
_start:
{
uint8_t v___x_2248_; 
v___x_2248_ = lean_usize_dec_lt(v_i_2246_, v_sz_2245_);
if (v___x_2248_ == 0)
{
return v_b_2247_;
}
else
{
lean_object* v_snd_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2267_; 
v_snd_2249_ = lean_ctor_get(v_b_2247_, 1);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_b_2247_);
if (v_isSharedCheck_2267_ == 0)
{
lean_object* v_unused_2268_; 
v_unused_2268_ = lean_ctor_get(v_b_2247_, 0);
lean_dec(v_unused_2268_);
v___x_2251_ = v_b_2247_;
v_isShared_2252_ = v_isSharedCheck_2267_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_snd_2249_);
lean_dec(v_b_2247_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2267_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v_a_2253_; lean_object* v___x_2254_; 
v_a_2253_ = lean_array_uget_borrowed(v_as_2244_, v_i_2246_);
lean_inc(v_snd_2249_);
v___x_2254_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2242_, v_x_2243_, v_a_2253_, v_snd_2249_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v___x_2255_; lean_object* v___x_2257_; 
v___x_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2255_);
v___x_2257_ = v___x_2251_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2255_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_snd_2249_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
lean_dec(v_snd_2249_);
v_a_2259_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2259_);
lean_dec_ref(v___x_2254_);
v___x_2260_ = lean_box(0);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 1, v_a_2259_);
lean_ctor_set(v___x_2251_, 0, v___x_2260_);
v___x_2262_ = v___x_2251_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2260_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v_a_2259_);
v___x_2262_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
size_t v___x_2263_; size_t v___x_2264_; 
v___x_2263_ = ((size_t)1ULL);
v___x_2264_ = lean_usize_add(v_i_2246_, v___x_2263_);
v_i_2246_ = v___x_2264_;
v_b_2247_ = v___x_2262_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_2269_, lean_object* v_x_2270_, lean_object* v_as_2271_, lean_object* v_sz_2272_, lean_object* v_i_2273_, lean_object* v_b_2274_){
_start:
{
size_t v_sz_boxed_2275_; size_t v_i_boxed_2276_; lean_object* v_res_2277_; 
v_sz_boxed_2275_ = lean_unbox_usize(v_sz_2272_);
lean_dec(v_sz_2272_);
v_i_boxed_2276_ = lean_unbox_usize(v_i_2273_);
lean_dec(v_i_2273_);
v_res_2277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2269_, v_x_2270_, v_as_2271_, v_sz_boxed_2275_, v_i_boxed_2276_, v_b_2274_);
lean_dec_ref(v_as_2271_);
lean_dec(v_x_2270_);
lean_dec_ref(v_init_2269_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_2278_, lean_object* v_x_2279_, lean_object* v_n_2280_, lean_object* v_b_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2278_, v_x_2279_, v_n_2280_, v_b_2281_);
lean_dec_ref(v_n_2280_);
lean_dec(v_x_2279_);
lean_dec_ref(v_init_2278_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(lean_object* v_x_2283_, lean_object* v_t_2284_, lean_object* v_init_2285_){
_start:
{
lean_object* v_root_2286_; lean_object* v_tail_2287_; lean_object* v___x_2288_; 
v_root_2286_ = lean_ctor_get(v_t_2284_, 0);
v_tail_2287_ = lean_ctor_get(v_t_2284_, 1);
lean_inc_ref(v_init_2285_);
v___x_2288_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2285_, v_x_2283_, v_root_2286_, v_init_2285_);
lean_dec_ref(v_init_2285_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2289_);
lean_dec_ref(v___x_2288_);
return v_a_2289_;
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; size_t v_sz_2293_; size_t v___x_2294_; lean_object* v___x_2295_; lean_object* v_fst_2296_; 
v_a_2290_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2290_);
lean_dec_ref(v___x_2288_);
v___x_2291_ = lean_box(0);
v___x_2292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
lean_ctor_set(v___x_2292_, 1, v_a_2290_);
v_sz_2293_ = lean_array_size(v_tail_2287_);
v___x_2294_ = ((size_t)0ULL);
v___x_2295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2283_, v_tail_2287_, v_sz_2293_, v___x_2294_, v___x_2292_);
v_fst_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_fst_2296_);
if (lean_obj_tag(v_fst_2296_) == 0)
{
lean_object* v_snd_2297_; 
v_snd_2297_ = lean_ctor_get(v___x_2295_, 1);
lean_inc(v_snd_2297_);
lean_dec_ref(v___x_2295_);
return v_snd_2297_;
}
else
{
lean_object* v_val_2298_; 
lean_dec_ref(v___x_2295_);
v_val_2298_ = lean_ctor_get(v_fst_2296_, 0);
lean_inc(v_val_2298_);
lean_dec_ref(v_fst_2296_);
return v_val_2298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0___boxed(lean_object* v_x_2299_, lean_object* v_t_2300_, lean_object* v_init_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2299_, v_t_2300_, v_init_2301_);
lean_dec_ref(v_t_2300_);
lean_dec(v_x_2299_);
return v_res_2302_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2303_ = lean_unsigned_to_nat(32u);
v___x_2304_ = lean_mk_empty_array_with_capacity(v___x_2303_);
v___x_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
return v___x_2305_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1(void){
_start:
{
size_t v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v_cs_x27_2311_; 
v___x_2306_ = ((size_t)5ULL);
v___x_2307_ = lean_unsigned_to_nat(0u);
v___x_2308_ = lean_unsigned_to_nat(32u);
v___x_2309_ = lean_mk_empty_array_with_capacity(v___x_2308_);
v___x_2310_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0);
v_cs_x27_2311_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_2311_, 0, v___x_2310_);
lean_ctor_set(v_cs_x27_2311_, 1, v___x_2309_);
lean_ctor_set(v_cs_x27_2311_, 2, v___x_2307_);
lean_ctor_set(v_cs_x27_2311_, 3, v___x_2307_);
lean_ctor_set_usize(v_cs_x27_2311_, 4, v___x_2306_);
return v_cs_x27_2311_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_2314_; lean_object* v_cs_x27_2315_; lean_object* v___x_2316_; 
v_todo_2314_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2));
v_cs_x27_2315_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1);
v___x_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2316_, 0, v_cs_x27_2315_);
lean_ctor_set(v___x_2316_, 1, v_todo_2314_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(lean_object* v_x_2317_, lean_object* v_cs_2318_){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v_fst_2321_; lean_object* v_snd_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
v___x_2319_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3);
v___x_2320_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2317_, v_cs_2318_, v___x_2319_);
v_fst_2321_ = lean_ctor_get(v___x_2320_, 0);
v_snd_2322_ = lean_ctor_get(v___x_2320_, 1);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2320_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_snd_2322_);
lean_inc(v_fst_2321_);
lean_dec(v___x_2320_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_fst_2321_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_snd_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___boxed(lean_object* v_x_2330_, lean_object* v_cs_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2330_, v_cs_2331_);
lean_dec_ref(v_cs_2331_);
lean_dec(v_x_2330_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object* v_x_2333_, lean_object* v_cs_2334_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2333_, v_cs_2334_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___boxed(lean_object* v_x_2336_, lean_object* v_cs_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(v_x_2336_, v_cs_2337_);
lean_dec_ref(v_cs_2337_);
lean_dec(v_x_2336_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(lean_object* v_a_2339_, lean_object* v_y_2340_, lean_object* v_fst_2341_, lean_object* v_s_2342_){
_start:
{
lean_object* v_structs_2343_; lean_object* v_typeIdOf_2344_; lean_object* v_exprToStructId_2345_; lean_object* v_exprToStructIdEntries_2346_; lean_object* v_forbiddenNatModules_2347_; lean_object* v_natStructs_2348_; lean_object* v_natTypeIdOf_2349_; lean_object* v_exprToNatStructId_2350_; lean_object* v___x_2351_; uint8_t v___x_2352_; 
v_structs_2343_ = lean_ctor_get(v_s_2342_, 0);
v_typeIdOf_2344_ = lean_ctor_get(v_s_2342_, 1);
v_exprToStructId_2345_ = lean_ctor_get(v_s_2342_, 2);
v_exprToStructIdEntries_2346_ = lean_ctor_get(v_s_2342_, 3);
v_forbiddenNatModules_2347_ = lean_ctor_get(v_s_2342_, 4);
v_natStructs_2348_ = lean_ctor_get(v_s_2342_, 5);
v_natTypeIdOf_2349_ = lean_ctor_get(v_s_2342_, 6);
v_exprToNatStructId_2350_ = lean_ctor_get(v_s_2342_, 7);
v___x_2351_ = lean_array_get_size(v_structs_2343_);
v___x_2352_ = lean_nat_dec_lt(v_a_2339_, v___x_2351_);
if (v___x_2352_ == 0)
{
lean_dec_ref(v_fst_2341_);
return v_s_2342_;
}
else
{
lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2414_; 
lean_inc_ref(v_exprToNatStructId_2350_);
lean_inc_ref(v_natTypeIdOf_2349_);
lean_inc_ref(v_natStructs_2348_);
lean_inc_ref(v_forbiddenNatModules_2347_);
lean_inc_ref(v_exprToStructIdEntries_2346_);
lean_inc_ref(v_exprToStructId_2345_);
lean_inc_ref(v_typeIdOf_2344_);
lean_inc_ref(v_structs_2343_);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_s_2342_);
if (v_isSharedCheck_2414_ == 0)
{
lean_object* v_unused_2415_; lean_object* v_unused_2416_; lean_object* v_unused_2417_; lean_object* v_unused_2418_; lean_object* v_unused_2419_; lean_object* v_unused_2420_; lean_object* v_unused_2421_; lean_object* v_unused_2422_; 
v_unused_2415_ = lean_ctor_get(v_s_2342_, 7);
lean_dec(v_unused_2415_);
v_unused_2416_ = lean_ctor_get(v_s_2342_, 6);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v_s_2342_, 5);
lean_dec(v_unused_2417_);
v_unused_2418_ = lean_ctor_get(v_s_2342_, 4);
lean_dec(v_unused_2418_);
v_unused_2419_ = lean_ctor_get(v_s_2342_, 3);
lean_dec(v_unused_2419_);
v_unused_2420_ = lean_ctor_get(v_s_2342_, 2);
lean_dec(v_unused_2420_);
v_unused_2421_ = lean_ctor_get(v_s_2342_, 1);
lean_dec(v_unused_2421_);
v_unused_2422_ = lean_ctor_get(v_s_2342_, 0);
lean_dec(v_unused_2422_);
v___x_2354_ = v_s_2342_;
v_isShared_2355_ = v_isSharedCheck_2414_;
goto v_resetjp_2353_;
}
else
{
lean_dec(v_s_2342_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2414_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v_v_2356_; lean_object* v_id_2357_; lean_object* v_ringId_x3f_2358_; lean_object* v_type_2359_; lean_object* v_u_2360_; lean_object* v_intModuleInst_2361_; lean_object* v_leInst_x3f_2362_; lean_object* v_ltInst_x3f_2363_; lean_object* v_lawfulOrderLTInst_x3f_2364_; lean_object* v_isPreorderInst_x3f_2365_; lean_object* v_orderedAddInst_x3f_2366_; lean_object* v_isLinearInst_x3f_2367_; lean_object* v_noNatDivInst_x3f_2368_; lean_object* v_ringInst_x3f_2369_; lean_object* v_commRingInst_x3f_2370_; lean_object* v_orderedRingInst_x3f_2371_; lean_object* v_fieldInst_x3f_2372_; lean_object* v_charInst_x3f_2373_; lean_object* v_zero_2374_; lean_object* v_ofNatZero_2375_; lean_object* v_one_x3f_2376_; lean_object* v_leFn_x3f_2377_; lean_object* v_ltFn_x3f_2378_; lean_object* v_addFn_2379_; lean_object* v_zsmulFn_2380_; lean_object* v_nsmulFn_2381_; lean_object* v_zsmulFn_x3f_2382_; lean_object* v_nsmulFn_x3f_2383_; lean_object* v_homomulFn_x3f_2384_; lean_object* v_subFn_2385_; lean_object* v_negFn_2386_; lean_object* v_vars_2387_; lean_object* v_varMap_2388_; lean_object* v_lowers_2389_; lean_object* v_uppers_2390_; lean_object* v_diseqs_2391_; lean_object* v_assignment_2392_; uint8_t v_caseSplits_2393_; lean_object* v_conflict_x3f_2394_; lean_object* v_diseqSplits_2395_; lean_object* v_elimEqs_2396_; lean_object* v_elimStack_2397_; lean_object* v_occurs_2398_; lean_object* v_ignored_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2413_; 
v_v_2356_ = lean_array_fget(v_structs_2343_, v_a_2339_);
v_id_2357_ = lean_ctor_get(v_v_2356_, 0);
v_ringId_x3f_2358_ = lean_ctor_get(v_v_2356_, 1);
v_type_2359_ = lean_ctor_get(v_v_2356_, 2);
v_u_2360_ = lean_ctor_get(v_v_2356_, 3);
v_intModuleInst_2361_ = lean_ctor_get(v_v_2356_, 4);
v_leInst_x3f_2362_ = lean_ctor_get(v_v_2356_, 5);
v_ltInst_x3f_2363_ = lean_ctor_get(v_v_2356_, 6);
v_lawfulOrderLTInst_x3f_2364_ = lean_ctor_get(v_v_2356_, 7);
v_isPreorderInst_x3f_2365_ = lean_ctor_get(v_v_2356_, 8);
v_orderedAddInst_x3f_2366_ = lean_ctor_get(v_v_2356_, 9);
v_isLinearInst_x3f_2367_ = lean_ctor_get(v_v_2356_, 10);
v_noNatDivInst_x3f_2368_ = lean_ctor_get(v_v_2356_, 11);
v_ringInst_x3f_2369_ = lean_ctor_get(v_v_2356_, 12);
v_commRingInst_x3f_2370_ = lean_ctor_get(v_v_2356_, 13);
v_orderedRingInst_x3f_2371_ = lean_ctor_get(v_v_2356_, 14);
v_fieldInst_x3f_2372_ = lean_ctor_get(v_v_2356_, 15);
v_charInst_x3f_2373_ = lean_ctor_get(v_v_2356_, 16);
v_zero_2374_ = lean_ctor_get(v_v_2356_, 17);
v_ofNatZero_2375_ = lean_ctor_get(v_v_2356_, 18);
v_one_x3f_2376_ = lean_ctor_get(v_v_2356_, 19);
v_leFn_x3f_2377_ = lean_ctor_get(v_v_2356_, 20);
v_ltFn_x3f_2378_ = lean_ctor_get(v_v_2356_, 21);
v_addFn_2379_ = lean_ctor_get(v_v_2356_, 22);
v_zsmulFn_2380_ = lean_ctor_get(v_v_2356_, 23);
v_nsmulFn_2381_ = lean_ctor_get(v_v_2356_, 24);
v_zsmulFn_x3f_2382_ = lean_ctor_get(v_v_2356_, 25);
v_nsmulFn_x3f_2383_ = lean_ctor_get(v_v_2356_, 26);
v_homomulFn_x3f_2384_ = lean_ctor_get(v_v_2356_, 27);
v_subFn_2385_ = lean_ctor_get(v_v_2356_, 28);
v_negFn_2386_ = lean_ctor_get(v_v_2356_, 29);
v_vars_2387_ = lean_ctor_get(v_v_2356_, 30);
v_varMap_2388_ = lean_ctor_get(v_v_2356_, 31);
v_lowers_2389_ = lean_ctor_get(v_v_2356_, 32);
v_uppers_2390_ = lean_ctor_get(v_v_2356_, 33);
v_diseqs_2391_ = lean_ctor_get(v_v_2356_, 34);
v_assignment_2392_ = lean_ctor_get(v_v_2356_, 35);
v_caseSplits_2393_ = lean_ctor_get_uint8(v_v_2356_, sizeof(void*)*42);
v_conflict_x3f_2394_ = lean_ctor_get(v_v_2356_, 36);
v_diseqSplits_2395_ = lean_ctor_get(v_v_2356_, 37);
v_elimEqs_2396_ = lean_ctor_get(v_v_2356_, 38);
v_elimStack_2397_ = lean_ctor_get(v_v_2356_, 39);
v_occurs_2398_ = lean_ctor_get(v_v_2356_, 40);
v_ignored_2399_ = lean_ctor_get(v_v_2356_, 41);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_v_2356_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2401_ = v_v_2356_;
v_isShared_2402_ = v_isSharedCheck_2413_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_ignored_2399_);
lean_inc(v_occurs_2398_);
lean_inc(v_elimStack_2397_);
lean_inc(v_elimEqs_2396_);
lean_inc(v_diseqSplits_2395_);
lean_inc(v_conflict_x3f_2394_);
lean_inc(v_assignment_2392_);
lean_inc(v_diseqs_2391_);
lean_inc(v_uppers_2390_);
lean_inc(v_lowers_2389_);
lean_inc(v_varMap_2388_);
lean_inc(v_vars_2387_);
lean_inc(v_negFn_2386_);
lean_inc(v_subFn_2385_);
lean_inc(v_homomulFn_x3f_2384_);
lean_inc(v_nsmulFn_x3f_2383_);
lean_inc(v_zsmulFn_x3f_2382_);
lean_inc(v_nsmulFn_2381_);
lean_inc(v_zsmulFn_2380_);
lean_inc(v_addFn_2379_);
lean_inc(v_ltFn_x3f_2378_);
lean_inc(v_leFn_x3f_2377_);
lean_inc(v_one_x3f_2376_);
lean_inc(v_ofNatZero_2375_);
lean_inc(v_zero_2374_);
lean_inc(v_charInst_x3f_2373_);
lean_inc(v_fieldInst_x3f_2372_);
lean_inc(v_orderedRingInst_x3f_2371_);
lean_inc(v_commRingInst_x3f_2370_);
lean_inc(v_ringInst_x3f_2369_);
lean_inc(v_noNatDivInst_x3f_2368_);
lean_inc(v_isLinearInst_x3f_2367_);
lean_inc(v_orderedAddInst_x3f_2366_);
lean_inc(v_isPreorderInst_x3f_2365_);
lean_inc(v_lawfulOrderLTInst_x3f_2364_);
lean_inc(v_ltInst_x3f_2363_);
lean_inc(v_leInst_x3f_2362_);
lean_inc(v_intModuleInst_2361_);
lean_inc(v_u_2360_);
lean_inc(v_type_2359_);
lean_inc(v_ringId_x3f_2358_);
lean_inc(v_id_2357_);
lean_dec(v_v_2356_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2413_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2403_; lean_object* v_xs_x27_2404_; lean_object* v___x_2405_; lean_object* v___x_2407_; 
v___x_2403_ = lean_box(0);
v_xs_x27_2404_ = lean_array_fset(v_structs_2343_, v_a_2339_, v___x_2403_);
v___x_2405_ = l_Lean_PersistentArray_set___redArg(v_lowers_2389_, v_y_2340_, v_fst_2341_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 32, v___x_2405_);
v___x_2407_ = v___x_2401_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_id_2357_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v_ringId_x3f_2358_);
lean_ctor_set(v_reuseFailAlloc_2412_, 2, v_type_2359_);
lean_ctor_set(v_reuseFailAlloc_2412_, 3, v_u_2360_);
lean_ctor_set(v_reuseFailAlloc_2412_, 4, v_intModuleInst_2361_);
lean_ctor_set(v_reuseFailAlloc_2412_, 5, v_leInst_x3f_2362_);
lean_ctor_set(v_reuseFailAlloc_2412_, 6, v_ltInst_x3f_2363_);
lean_ctor_set(v_reuseFailAlloc_2412_, 7, v_lawfulOrderLTInst_x3f_2364_);
lean_ctor_set(v_reuseFailAlloc_2412_, 8, v_isPreorderInst_x3f_2365_);
lean_ctor_set(v_reuseFailAlloc_2412_, 9, v_orderedAddInst_x3f_2366_);
lean_ctor_set(v_reuseFailAlloc_2412_, 10, v_isLinearInst_x3f_2367_);
lean_ctor_set(v_reuseFailAlloc_2412_, 11, v_noNatDivInst_x3f_2368_);
lean_ctor_set(v_reuseFailAlloc_2412_, 12, v_ringInst_x3f_2369_);
lean_ctor_set(v_reuseFailAlloc_2412_, 13, v_commRingInst_x3f_2370_);
lean_ctor_set(v_reuseFailAlloc_2412_, 14, v_orderedRingInst_x3f_2371_);
lean_ctor_set(v_reuseFailAlloc_2412_, 15, v_fieldInst_x3f_2372_);
lean_ctor_set(v_reuseFailAlloc_2412_, 16, v_charInst_x3f_2373_);
lean_ctor_set(v_reuseFailAlloc_2412_, 17, v_zero_2374_);
lean_ctor_set(v_reuseFailAlloc_2412_, 18, v_ofNatZero_2375_);
lean_ctor_set(v_reuseFailAlloc_2412_, 19, v_one_x3f_2376_);
lean_ctor_set(v_reuseFailAlloc_2412_, 20, v_leFn_x3f_2377_);
lean_ctor_set(v_reuseFailAlloc_2412_, 21, v_ltFn_x3f_2378_);
lean_ctor_set(v_reuseFailAlloc_2412_, 22, v_addFn_2379_);
lean_ctor_set(v_reuseFailAlloc_2412_, 23, v_zsmulFn_2380_);
lean_ctor_set(v_reuseFailAlloc_2412_, 24, v_nsmulFn_2381_);
lean_ctor_set(v_reuseFailAlloc_2412_, 25, v_zsmulFn_x3f_2382_);
lean_ctor_set(v_reuseFailAlloc_2412_, 26, v_nsmulFn_x3f_2383_);
lean_ctor_set(v_reuseFailAlloc_2412_, 27, v_homomulFn_x3f_2384_);
lean_ctor_set(v_reuseFailAlloc_2412_, 28, v_subFn_2385_);
lean_ctor_set(v_reuseFailAlloc_2412_, 29, v_negFn_2386_);
lean_ctor_set(v_reuseFailAlloc_2412_, 30, v_vars_2387_);
lean_ctor_set(v_reuseFailAlloc_2412_, 31, v_varMap_2388_);
lean_ctor_set(v_reuseFailAlloc_2412_, 32, v___x_2405_);
lean_ctor_set(v_reuseFailAlloc_2412_, 33, v_uppers_2390_);
lean_ctor_set(v_reuseFailAlloc_2412_, 34, v_diseqs_2391_);
lean_ctor_set(v_reuseFailAlloc_2412_, 35, v_assignment_2392_);
lean_ctor_set(v_reuseFailAlloc_2412_, 36, v_conflict_x3f_2394_);
lean_ctor_set(v_reuseFailAlloc_2412_, 37, v_diseqSplits_2395_);
lean_ctor_set(v_reuseFailAlloc_2412_, 38, v_elimEqs_2396_);
lean_ctor_set(v_reuseFailAlloc_2412_, 39, v_elimStack_2397_);
lean_ctor_set(v_reuseFailAlloc_2412_, 40, v_occurs_2398_);
lean_ctor_set(v_reuseFailAlloc_2412_, 41, v_ignored_2399_);
lean_ctor_set_uint8(v_reuseFailAlloc_2412_, sizeof(void*)*42, v_caseSplits_2393_);
v___x_2407_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
lean_object* v___x_2408_; lean_object* v___x_2410_; 
v___x_2408_ = lean_array_fset(v_xs_x27_2404_, v_a_2339_, v___x_2407_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2408_);
v___x_2410_ = v___x_2354_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2408_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v_typeIdOf_2344_);
lean_ctor_set(v_reuseFailAlloc_2411_, 2, v_exprToStructId_2345_);
lean_ctor_set(v_reuseFailAlloc_2411_, 3, v_exprToStructIdEntries_2346_);
lean_ctor_set(v_reuseFailAlloc_2411_, 4, v_forbiddenNatModules_2347_);
lean_ctor_set(v_reuseFailAlloc_2411_, 5, v_natStructs_2348_);
lean_ctor_set(v_reuseFailAlloc_2411_, 6, v_natTypeIdOf_2349_);
lean_ctor_set(v_reuseFailAlloc_2411_, 7, v_exprToNatStructId_2350_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed(lean_object* v_a_2423_, lean_object* v_y_2424_, lean_object* v_fst_2425_, lean_object* v_s_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(v_a_2423_, v_y_2424_, v_fst_2425_, v_s_2426_);
lean_dec(v_y_2424_);
lean_dec(v_a_2423_);
return v_res_2427_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0(void){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object* v_a_2429_, lean_object* v_x_2430_, lean_object* v_c_2431_, lean_object* v_y_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_){
_start:
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2480_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2448_ = v___x_2445_;
v_isShared_2449_ = v_isSharedCheck_2480_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2445_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2480_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
uint8_t v___x_2450_; 
v___x_2450_ = lean_unbox(v_a_2446_);
lean_dec(v_a_2446_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2451_; 
lean_del_object(v___x_2448_);
v___x_2451_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; lean_object* v___y_2454_; lean_object* v_lowers_2462_; lean_object* v_size_2463_; lean_object* v___x_2464_; uint8_t v___x_2465_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2452_);
lean_dec_ref(v___x_2451_);
v_lowers_2462_ = lean_ctor_get(v_a_2452_, 32);
lean_inc_ref(v_lowers_2462_);
lean_dec(v_a_2452_);
v_size_2463_ = lean_ctor_get(v_lowers_2462_, 2);
v___x_2464_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2465_ = lean_nat_dec_lt(v_y_2432_, v_size_2463_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; 
lean_dec_ref(v_lowers_2462_);
v___x_2466_ = l_outOfBounds___redArg(v___x_2464_);
v___y_2454_ = v___x_2466_;
goto v___jp_2453_;
}
else
{
lean_object* v___x_2467_; 
v___x_2467_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2464_, v_lowers_2462_, v_y_2432_);
lean_dec_ref(v_lowers_2462_);
v___y_2454_ = v___x_2467_;
goto v___jp_2453_;
}
v___jp_2453_:
{
lean_object* v___x_2455_; lean_object* v_fst_2456_; lean_object* v_snd_2457_; lean_object* v___f_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2455_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2430_, v___y_2454_);
lean_dec_ref(v___y_2454_);
v_fst_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_fst_2456_);
v_snd_2457_ = lean_ctor_get(v___x_2455_, 1);
lean_inc(v_snd_2457_);
lean_dec_ref(v___x_2455_);
lean_inc(v_a_2433_);
v___f_2458_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2458_, 0, v_a_2433_);
lean_closure_set(v___f_2458_, 1, v_y_2432_);
lean_closure_set(v___f_2458_, 2, v_fst_2456_);
v___x_2459_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2460_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2459_, v___f_2458_, v_a_2434_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v___x_2461_; 
lean_dec_ref(v___x_2460_);
v___x_2461_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2429_, v_x_2430_, v_c_2431_, v_snd_2457_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
lean_dec(v_snd_2457_);
return v___x_2461_;
}
else
{
lean_dec(v_snd_2457_);
lean_dec_ref(v_c_2431_);
lean_dec(v_x_2430_);
lean_dec(v_a_2429_);
return v___x_2460_;
}
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec(v_y_2432_);
lean_dec_ref(v_c_2431_);
lean_dec(v_x_2430_);
lean_dec(v_a_2429_);
v_a_2468_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2451_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2451_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
else
{
lean_object* v___x_2476_; lean_object* v___x_2478_; 
lean_dec(v_y_2432_);
lean_dec_ref(v_c_2431_);
lean_dec(v_x_2430_);
lean_dec(v_a_2429_);
v___x_2476_ = lean_box(0);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v___x_2476_);
v___x_2478_ = v___x_2448_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec(v_y_2432_);
lean_dec_ref(v_c_2431_);
lean_dec(v_x_2430_);
lean_dec(v_a_2429_);
v_a_2481_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2445_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2445_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object* v_a_2489_, lean_object* v_x_2490_, lean_object* v_c_2491_, lean_object* v_y_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_2489_, v_x_2490_, v_c_2491_, v_y_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
lean_dec(v_a_2503_);
lean_dec_ref(v_a_2502_);
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec(v_a_2494_);
lean_dec(v_a_2493_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(lean_object* v_a_2506_, lean_object* v_y_2507_, lean_object* v_fst_2508_, lean_object* v_s_2509_){
_start:
{
lean_object* v_structs_2510_; lean_object* v_typeIdOf_2511_; lean_object* v_exprToStructId_2512_; lean_object* v_exprToStructIdEntries_2513_; lean_object* v_forbiddenNatModules_2514_; lean_object* v_natStructs_2515_; lean_object* v_natTypeIdOf_2516_; lean_object* v_exprToNatStructId_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v_structs_2510_ = lean_ctor_get(v_s_2509_, 0);
v_typeIdOf_2511_ = lean_ctor_get(v_s_2509_, 1);
v_exprToStructId_2512_ = lean_ctor_get(v_s_2509_, 2);
v_exprToStructIdEntries_2513_ = lean_ctor_get(v_s_2509_, 3);
v_forbiddenNatModules_2514_ = lean_ctor_get(v_s_2509_, 4);
v_natStructs_2515_ = lean_ctor_get(v_s_2509_, 5);
v_natTypeIdOf_2516_ = lean_ctor_get(v_s_2509_, 6);
v_exprToNatStructId_2517_ = lean_ctor_get(v_s_2509_, 7);
v___x_2518_ = lean_array_get_size(v_structs_2510_);
v___x_2519_ = lean_nat_dec_lt(v_a_2506_, v___x_2518_);
if (v___x_2519_ == 0)
{
lean_dec_ref(v_fst_2508_);
return v_s_2509_;
}
else
{
lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2581_; 
lean_inc_ref(v_exprToNatStructId_2517_);
lean_inc_ref(v_natTypeIdOf_2516_);
lean_inc_ref(v_natStructs_2515_);
lean_inc_ref(v_forbiddenNatModules_2514_);
lean_inc_ref(v_exprToStructIdEntries_2513_);
lean_inc_ref(v_exprToStructId_2512_);
lean_inc_ref(v_typeIdOf_2511_);
lean_inc_ref(v_structs_2510_);
v_isSharedCheck_2581_ = !lean_is_exclusive(v_s_2509_);
if (v_isSharedCheck_2581_ == 0)
{
lean_object* v_unused_2582_; lean_object* v_unused_2583_; lean_object* v_unused_2584_; lean_object* v_unused_2585_; lean_object* v_unused_2586_; lean_object* v_unused_2587_; lean_object* v_unused_2588_; lean_object* v_unused_2589_; 
v_unused_2582_ = lean_ctor_get(v_s_2509_, 7);
lean_dec(v_unused_2582_);
v_unused_2583_ = lean_ctor_get(v_s_2509_, 6);
lean_dec(v_unused_2583_);
v_unused_2584_ = lean_ctor_get(v_s_2509_, 5);
lean_dec(v_unused_2584_);
v_unused_2585_ = lean_ctor_get(v_s_2509_, 4);
lean_dec(v_unused_2585_);
v_unused_2586_ = lean_ctor_get(v_s_2509_, 3);
lean_dec(v_unused_2586_);
v_unused_2587_ = lean_ctor_get(v_s_2509_, 2);
lean_dec(v_unused_2587_);
v_unused_2588_ = lean_ctor_get(v_s_2509_, 1);
lean_dec(v_unused_2588_);
v_unused_2589_ = lean_ctor_get(v_s_2509_, 0);
lean_dec(v_unused_2589_);
v___x_2521_ = v_s_2509_;
v_isShared_2522_ = v_isSharedCheck_2581_;
goto v_resetjp_2520_;
}
else
{
lean_dec(v_s_2509_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2581_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v_v_2523_; lean_object* v_id_2524_; lean_object* v_ringId_x3f_2525_; lean_object* v_type_2526_; lean_object* v_u_2527_; lean_object* v_intModuleInst_2528_; lean_object* v_leInst_x3f_2529_; lean_object* v_ltInst_x3f_2530_; lean_object* v_lawfulOrderLTInst_x3f_2531_; lean_object* v_isPreorderInst_x3f_2532_; lean_object* v_orderedAddInst_x3f_2533_; lean_object* v_isLinearInst_x3f_2534_; lean_object* v_noNatDivInst_x3f_2535_; lean_object* v_ringInst_x3f_2536_; lean_object* v_commRingInst_x3f_2537_; lean_object* v_orderedRingInst_x3f_2538_; lean_object* v_fieldInst_x3f_2539_; lean_object* v_charInst_x3f_2540_; lean_object* v_zero_2541_; lean_object* v_ofNatZero_2542_; lean_object* v_one_x3f_2543_; lean_object* v_leFn_x3f_2544_; lean_object* v_ltFn_x3f_2545_; lean_object* v_addFn_2546_; lean_object* v_zsmulFn_2547_; lean_object* v_nsmulFn_2548_; lean_object* v_zsmulFn_x3f_2549_; lean_object* v_nsmulFn_x3f_2550_; lean_object* v_homomulFn_x3f_2551_; lean_object* v_subFn_2552_; lean_object* v_negFn_2553_; lean_object* v_vars_2554_; lean_object* v_varMap_2555_; lean_object* v_lowers_2556_; lean_object* v_uppers_2557_; lean_object* v_diseqs_2558_; lean_object* v_assignment_2559_; uint8_t v_caseSplits_2560_; lean_object* v_conflict_x3f_2561_; lean_object* v_diseqSplits_2562_; lean_object* v_elimEqs_2563_; lean_object* v_elimStack_2564_; lean_object* v_occurs_2565_; lean_object* v_ignored_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2580_; 
v_v_2523_ = lean_array_fget(v_structs_2510_, v_a_2506_);
v_id_2524_ = lean_ctor_get(v_v_2523_, 0);
v_ringId_x3f_2525_ = lean_ctor_get(v_v_2523_, 1);
v_type_2526_ = lean_ctor_get(v_v_2523_, 2);
v_u_2527_ = lean_ctor_get(v_v_2523_, 3);
v_intModuleInst_2528_ = lean_ctor_get(v_v_2523_, 4);
v_leInst_x3f_2529_ = lean_ctor_get(v_v_2523_, 5);
v_ltInst_x3f_2530_ = lean_ctor_get(v_v_2523_, 6);
v_lawfulOrderLTInst_x3f_2531_ = lean_ctor_get(v_v_2523_, 7);
v_isPreorderInst_x3f_2532_ = lean_ctor_get(v_v_2523_, 8);
v_orderedAddInst_x3f_2533_ = lean_ctor_get(v_v_2523_, 9);
v_isLinearInst_x3f_2534_ = lean_ctor_get(v_v_2523_, 10);
v_noNatDivInst_x3f_2535_ = lean_ctor_get(v_v_2523_, 11);
v_ringInst_x3f_2536_ = lean_ctor_get(v_v_2523_, 12);
v_commRingInst_x3f_2537_ = lean_ctor_get(v_v_2523_, 13);
v_orderedRingInst_x3f_2538_ = lean_ctor_get(v_v_2523_, 14);
v_fieldInst_x3f_2539_ = lean_ctor_get(v_v_2523_, 15);
v_charInst_x3f_2540_ = lean_ctor_get(v_v_2523_, 16);
v_zero_2541_ = lean_ctor_get(v_v_2523_, 17);
v_ofNatZero_2542_ = lean_ctor_get(v_v_2523_, 18);
v_one_x3f_2543_ = lean_ctor_get(v_v_2523_, 19);
v_leFn_x3f_2544_ = lean_ctor_get(v_v_2523_, 20);
v_ltFn_x3f_2545_ = lean_ctor_get(v_v_2523_, 21);
v_addFn_2546_ = lean_ctor_get(v_v_2523_, 22);
v_zsmulFn_2547_ = lean_ctor_get(v_v_2523_, 23);
v_nsmulFn_2548_ = lean_ctor_get(v_v_2523_, 24);
v_zsmulFn_x3f_2549_ = lean_ctor_get(v_v_2523_, 25);
v_nsmulFn_x3f_2550_ = lean_ctor_get(v_v_2523_, 26);
v_homomulFn_x3f_2551_ = lean_ctor_get(v_v_2523_, 27);
v_subFn_2552_ = lean_ctor_get(v_v_2523_, 28);
v_negFn_2553_ = lean_ctor_get(v_v_2523_, 29);
v_vars_2554_ = lean_ctor_get(v_v_2523_, 30);
v_varMap_2555_ = lean_ctor_get(v_v_2523_, 31);
v_lowers_2556_ = lean_ctor_get(v_v_2523_, 32);
v_uppers_2557_ = lean_ctor_get(v_v_2523_, 33);
v_diseqs_2558_ = lean_ctor_get(v_v_2523_, 34);
v_assignment_2559_ = lean_ctor_get(v_v_2523_, 35);
v_caseSplits_2560_ = lean_ctor_get_uint8(v_v_2523_, sizeof(void*)*42);
v_conflict_x3f_2561_ = lean_ctor_get(v_v_2523_, 36);
v_diseqSplits_2562_ = lean_ctor_get(v_v_2523_, 37);
v_elimEqs_2563_ = lean_ctor_get(v_v_2523_, 38);
v_elimStack_2564_ = lean_ctor_get(v_v_2523_, 39);
v_occurs_2565_ = lean_ctor_get(v_v_2523_, 40);
v_ignored_2566_ = lean_ctor_get(v_v_2523_, 41);
v_isSharedCheck_2580_ = !lean_is_exclusive(v_v_2523_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2568_ = v_v_2523_;
v_isShared_2569_ = v_isSharedCheck_2580_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_ignored_2566_);
lean_inc(v_occurs_2565_);
lean_inc(v_elimStack_2564_);
lean_inc(v_elimEqs_2563_);
lean_inc(v_diseqSplits_2562_);
lean_inc(v_conflict_x3f_2561_);
lean_inc(v_assignment_2559_);
lean_inc(v_diseqs_2558_);
lean_inc(v_uppers_2557_);
lean_inc(v_lowers_2556_);
lean_inc(v_varMap_2555_);
lean_inc(v_vars_2554_);
lean_inc(v_negFn_2553_);
lean_inc(v_subFn_2552_);
lean_inc(v_homomulFn_x3f_2551_);
lean_inc(v_nsmulFn_x3f_2550_);
lean_inc(v_zsmulFn_x3f_2549_);
lean_inc(v_nsmulFn_2548_);
lean_inc(v_zsmulFn_2547_);
lean_inc(v_addFn_2546_);
lean_inc(v_ltFn_x3f_2545_);
lean_inc(v_leFn_x3f_2544_);
lean_inc(v_one_x3f_2543_);
lean_inc(v_ofNatZero_2542_);
lean_inc(v_zero_2541_);
lean_inc(v_charInst_x3f_2540_);
lean_inc(v_fieldInst_x3f_2539_);
lean_inc(v_orderedRingInst_x3f_2538_);
lean_inc(v_commRingInst_x3f_2537_);
lean_inc(v_ringInst_x3f_2536_);
lean_inc(v_noNatDivInst_x3f_2535_);
lean_inc(v_isLinearInst_x3f_2534_);
lean_inc(v_orderedAddInst_x3f_2533_);
lean_inc(v_isPreorderInst_x3f_2532_);
lean_inc(v_lawfulOrderLTInst_x3f_2531_);
lean_inc(v_ltInst_x3f_2530_);
lean_inc(v_leInst_x3f_2529_);
lean_inc(v_intModuleInst_2528_);
lean_inc(v_u_2527_);
lean_inc(v_type_2526_);
lean_inc(v_ringId_x3f_2525_);
lean_inc(v_id_2524_);
lean_dec(v_v_2523_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2580_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2570_; lean_object* v_xs_x27_2571_; lean_object* v___x_2572_; lean_object* v___x_2574_; 
v___x_2570_ = lean_box(0);
v_xs_x27_2571_ = lean_array_fset(v_structs_2510_, v_a_2506_, v___x_2570_);
v___x_2572_ = l_Lean_PersistentArray_set___redArg(v_uppers_2557_, v_y_2507_, v_fst_2508_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 33, v___x_2572_);
v___x_2574_ = v___x_2568_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_id_2524_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v_ringId_x3f_2525_);
lean_ctor_set(v_reuseFailAlloc_2579_, 2, v_type_2526_);
lean_ctor_set(v_reuseFailAlloc_2579_, 3, v_u_2527_);
lean_ctor_set(v_reuseFailAlloc_2579_, 4, v_intModuleInst_2528_);
lean_ctor_set(v_reuseFailAlloc_2579_, 5, v_leInst_x3f_2529_);
lean_ctor_set(v_reuseFailAlloc_2579_, 6, v_ltInst_x3f_2530_);
lean_ctor_set(v_reuseFailAlloc_2579_, 7, v_lawfulOrderLTInst_x3f_2531_);
lean_ctor_set(v_reuseFailAlloc_2579_, 8, v_isPreorderInst_x3f_2532_);
lean_ctor_set(v_reuseFailAlloc_2579_, 9, v_orderedAddInst_x3f_2533_);
lean_ctor_set(v_reuseFailAlloc_2579_, 10, v_isLinearInst_x3f_2534_);
lean_ctor_set(v_reuseFailAlloc_2579_, 11, v_noNatDivInst_x3f_2535_);
lean_ctor_set(v_reuseFailAlloc_2579_, 12, v_ringInst_x3f_2536_);
lean_ctor_set(v_reuseFailAlloc_2579_, 13, v_commRingInst_x3f_2537_);
lean_ctor_set(v_reuseFailAlloc_2579_, 14, v_orderedRingInst_x3f_2538_);
lean_ctor_set(v_reuseFailAlloc_2579_, 15, v_fieldInst_x3f_2539_);
lean_ctor_set(v_reuseFailAlloc_2579_, 16, v_charInst_x3f_2540_);
lean_ctor_set(v_reuseFailAlloc_2579_, 17, v_zero_2541_);
lean_ctor_set(v_reuseFailAlloc_2579_, 18, v_ofNatZero_2542_);
lean_ctor_set(v_reuseFailAlloc_2579_, 19, v_one_x3f_2543_);
lean_ctor_set(v_reuseFailAlloc_2579_, 20, v_leFn_x3f_2544_);
lean_ctor_set(v_reuseFailAlloc_2579_, 21, v_ltFn_x3f_2545_);
lean_ctor_set(v_reuseFailAlloc_2579_, 22, v_addFn_2546_);
lean_ctor_set(v_reuseFailAlloc_2579_, 23, v_zsmulFn_2547_);
lean_ctor_set(v_reuseFailAlloc_2579_, 24, v_nsmulFn_2548_);
lean_ctor_set(v_reuseFailAlloc_2579_, 25, v_zsmulFn_x3f_2549_);
lean_ctor_set(v_reuseFailAlloc_2579_, 26, v_nsmulFn_x3f_2550_);
lean_ctor_set(v_reuseFailAlloc_2579_, 27, v_homomulFn_x3f_2551_);
lean_ctor_set(v_reuseFailAlloc_2579_, 28, v_subFn_2552_);
lean_ctor_set(v_reuseFailAlloc_2579_, 29, v_negFn_2553_);
lean_ctor_set(v_reuseFailAlloc_2579_, 30, v_vars_2554_);
lean_ctor_set(v_reuseFailAlloc_2579_, 31, v_varMap_2555_);
lean_ctor_set(v_reuseFailAlloc_2579_, 32, v_lowers_2556_);
lean_ctor_set(v_reuseFailAlloc_2579_, 33, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2579_, 34, v_diseqs_2558_);
lean_ctor_set(v_reuseFailAlloc_2579_, 35, v_assignment_2559_);
lean_ctor_set(v_reuseFailAlloc_2579_, 36, v_conflict_x3f_2561_);
lean_ctor_set(v_reuseFailAlloc_2579_, 37, v_diseqSplits_2562_);
lean_ctor_set(v_reuseFailAlloc_2579_, 38, v_elimEqs_2563_);
lean_ctor_set(v_reuseFailAlloc_2579_, 39, v_elimStack_2564_);
lean_ctor_set(v_reuseFailAlloc_2579_, 40, v_occurs_2565_);
lean_ctor_set(v_reuseFailAlloc_2579_, 41, v_ignored_2566_);
lean_ctor_set_uint8(v_reuseFailAlloc_2579_, sizeof(void*)*42, v_caseSplits_2560_);
v___x_2574_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2575_ = lean_array_fset(v_xs_x27_2571_, v_a_2506_, v___x_2574_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v___x_2575_);
v___x_2577_ = v___x_2521_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_typeIdOf_2511_);
lean_ctor_set(v_reuseFailAlloc_2578_, 2, v_exprToStructId_2512_);
lean_ctor_set(v_reuseFailAlloc_2578_, 3, v_exprToStructIdEntries_2513_);
lean_ctor_set(v_reuseFailAlloc_2578_, 4, v_forbiddenNatModules_2514_);
lean_ctor_set(v_reuseFailAlloc_2578_, 5, v_natStructs_2515_);
lean_ctor_set(v_reuseFailAlloc_2578_, 6, v_natTypeIdOf_2516_);
lean_ctor_set(v_reuseFailAlloc_2578_, 7, v_exprToNatStructId_2517_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed(lean_object* v_a_2590_, lean_object* v_y_2591_, lean_object* v_fst_2592_, lean_object* v_s_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(v_a_2590_, v_y_2591_, v_fst_2592_, v_s_2593_);
lean_dec(v_y_2591_);
lean_dec(v_a_2590_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object* v_a_2595_, lean_object* v_x_2596_, lean_object* v_c_2597_, lean_object* v_y_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2646_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2614_ = v___x_2611_;
v_isShared_2615_ = v_isSharedCheck_2646_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2611_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2646_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
uint8_t v___x_2616_; 
v___x_2616_ = lean_unbox(v_a_2612_);
lean_dec(v_a_2612_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; 
lean_del_object(v___x_2614_);
v___x_2617_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___y_2620_; lean_object* v_uppers_2628_; lean_object* v_size_2629_; lean_object* v___x_2630_; uint8_t v___x_2631_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
lean_dec_ref(v___x_2617_);
v_uppers_2628_ = lean_ctor_get(v_a_2618_, 33);
lean_inc_ref(v_uppers_2628_);
lean_dec(v_a_2618_);
v_size_2629_ = lean_ctor_get(v_uppers_2628_, 2);
v___x_2630_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2631_ = lean_nat_dec_lt(v_y_2598_, v_size_2629_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; 
lean_dec_ref(v_uppers_2628_);
v___x_2632_ = l_outOfBounds___redArg(v___x_2630_);
v___y_2620_ = v___x_2632_;
goto v___jp_2619_;
}
else
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2630_, v_uppers_2628_, v_y_2598_);
lean_dec_ref(v_uppers_2628_);
v___y_2620_ = v___x_2633_;
goto v___jp_2619_;
}
v___jp_2619_:
{
lean_object* v___x_2621_; lean_object* v_fst_2622_; lean_object* v_snd_2623_; lean_object* v___f_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2621_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2596_, v___y_2620_);
lean_dec_ref(v___y_2620_);
v_fst_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_fst_2622_);
v_snd_2623_ = lean_ctor_get(v___x_2621_, 1);
lean_inc(v_snd_2623_);
lean_dec_ref(v___x_2621_);
lean_inc(v_a_2599_);
v___f_2624_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2624_, 0, v_a_2599_);
lean_closure_set(v___f_2624_, 1, v_y_2598_);
lean_closure_set(v___f_2624_, 2, v_fst_2622_);
v___x_2625_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2626_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2625_, v___f_2624_, v_a_2600_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v___x_2627_; 
lean_dec_ref(v___x_2626_);
v___x_2627_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2595_, v_x_2596_, v_c_2597_, v_snd_2623_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
lean_dec(v_snd_2623_);
return v___x_2627_;
}
else
{
lean_dec(v_snd_2623_);
lean_dec_ref(v_c_2597_);
lean_dec(v_x_2596_);
lean_dec(v_a_2595_);
return v___x_2626_;
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_dec(v_y_2598_);
lean_dec_ref(v_c_2597_);
lean_dec(v_x_2596_);
lean_dec(v_a_2595_);
v_a_2634_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2617_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2617_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
else
{
lean_object* v___x_2642_; lean_object* v___x_2644_; 
lean_dec(v_y_2598_);
lean_dec_ref(v_c_2597_);
lean_dec(v_x_2596_);
lean_dec(v_a_2595_);
v___x_2642_ = lean_box(0);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v___x_2642_);
v___x_2644_ = v___x_2614_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2642_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_dec(v_y_2598_);
lean_dec_ref(v_c_2597_);
lean_dec(v_x_2596_);
lean_dec(v_a_2595_);
v_a_2647_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2611_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2611_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object* v_a_2655_, lean_object* v_x_2656_, lean_object* v_c_2657_, lean_object* v_y_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_2655_, v_x_2656_, v_c_2657_, v_y_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec(v_a_2659_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(lean_object* v___y_2672_, lean_object* v_a_2673_, lean_object* v_s_2674_){
_start:
{
lean_object* v_structs_2675_; lean_object* v_typeIdOf_2676_; lean_object* v_exprToStructId_2677_; lean_object* v_exprToStructIdEntries_2678_; lean_object* v_forbiddenNatModules_2679_; lean_object* v_natStructs_2680_; lean_object* v_natTypeIdOf_2681_; lean_object* v_exprToNatStructId_2682_; lean_object* v___x_2683_; uint8_t v___x_2684_; 
v_structs_2675_ = lean_ctor_get(v_s_2674_, 0);
v_typeIdOf_2676_ = lean_ctor_get(v_s_2674_, 1);
v_exprToStructId_2677_ = lean_ctor_get(v_s_2674_, 2);
v_exprToStructIdEntries_2678_ = lean_ctor_get(v_s_2674_, 3);
v_forbiddenNatModules_2679_ = lean_ctor_get(v_s_2674_, 4);
v_natStructs_2680_ = lean_ctor_get(v_s_2674_, 5);
v_natTypeIdOf_2681_ = lean_ctor_get(v_s_2674_, 6);
v_exprToNatStructId_2682_ = lean_ctor_get(v_s_2674_, 7);
v___x_2683_ = lean_array_get_size(v_structs_2675_);
v___x_2684_ = lean_nat_dec_lt(v___y_2672_, v___x_2683_);
if (v___x_2684_ == 0)
{
lean_dec_ref(v_a_2673_);
return v_s_2674_;
}
else
{
lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2746_; 
lean_inc_ref(v_exprToNatStructId_2682_);
lean_inc_ref(v_natTypeIdOf_2681_);
lean_inc_ref(v_natStructs_2680_);
lean_inc_ref(v_forbiddenNatModules_2679_);
lean_inc_ref(v_exprToStructIdEntries_2678_);
lean_inc_ref(v_exprToStructId_2677_);
lean_inc_ref(v_typeIdOf_2676_);
lean_inc_ref(v_structs_2675_);
v_isSharedCheck_2746_ = !lean_is_exclusive(v_s_2674_);
if (v_isSharedCheck_2746_ == 0)
{
lean_object* v_unused_2747_; lean_object* v_unused_2748_; lean_object* v_unused_2749_; lean_object* v_unused_2750_; lean_object* v_unused_2751_; lean_object* v_unused_2752_; lean_object* v_unused_2753_; lean_object* v_unused_2754_; 
v_unused_2747_ = lean_ctor_get(v_s_2674_, 7);
lean_dec(v_unused_2747_);
v_unused_2748_ = lean_ctor_get(v_s_2674_, 6);
lean_dec(v_unused_2748_);
v_unused_2749_ = lean_ctor_get(v_s_2674_, 5);
lean_dec(v_unused_2749_);
v_unused_2750_ = lean_ctor_get(v_s_2674_, 4);
lean_dec(v_unused_2750_);
v_unused_2751_ = lean_ctor_get(v_s_2674_, 3);
lean_dec(v_unused_2751_);
v_unused_2752_ = lean_ctor_get(v_s_2674_, 2);
lean_dec(v_unused_2752_);
v_unused_2753_ = lean_ctor_get(v_s_2674_, 1);
lean_dec(v_unused_2753_);
v_unused_2754_ = lean_ctor_get(v_s_2674_, 0);
lean_dec(v_unused_2754_);
v___x_2686_ = v_s_2674_;
v_isShared_2687_ = v_isSharedCheck_2746_;
goto v_resetjp_2685_;
}
else
{
lean_dec(v_s_2674_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2746_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v_v_2688_; lean_object* v_id_2689_; lean_object* v_ringId_x3f_2690_; lean_object* v_type_2691_; lean_object* v_u_2692_; lean_object* v_intModuleInst_2693_; lean_object* v_leInst_x3f_2694_; lean_object* v_ltInst_x3f_2695_; lean_object* v_lawfulOrderLTInst_x3f_2696_; lean_object* v_isPreorderInst_x3f_2697_; lean_object* v_orderedAddInst_x3f_2698_; lean_object* v_isLinearInst_x3f_2699_; lean_object* v_noNatDivInst_x3f_2700_; lean_object* v_ringInst_x3f_2701_; lean_object* v_commRingInst_x3f_2702_; lean_object* v_orderedRingInst_x3f_2703_; lean_object* v_fieldInst_x3f_2704_; lean_object* v_charInst_x3f_2705_; lean_object* v_zero_2706_; lean_object* v_ofNatZero_2707_; lean_object* v_one_x3f_2708_; lean_object* v_leFn_x3f_2709_; lean_object* v_ltFn_x3f_2710_; lean_object* v_addFn_2711_; lean_object* v_zsmulFn_2712_; lean_object* v_nsmulFn_2713_; lean_object* v_zsmulFn_x3f_2714_; lean_object* v_nsmulFn_x3f_2715_; lean_object* v_homomulFn_x3f_2716_; lean_object* v_subFn_2717_; lean_object* v_negFn_2718_; lean_object* v_vars_2719_; lean_object* v_varMap_2720_; lean_object* v_lowers_2721_; lean_object* v_uppers_2722_; lean_object* v_diseqs_2723_; lean_object* v_assignment_2724_; uint8_t v_caseSplits_2725_; lean_object* v_conflict_x3f_2726_; lean_object* v_diseqSplits_2727_; lean_object* v_elimEqs_2728_; lean_object* v_elimStack_2729_; lean_object* v_occurs_2730_; lean_object* v_ignored_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2745_; 
v_v_2688_ = lean_array_fget(v_structs_2675_, v___y_2672_);
v_id_2689_ = lean_ctor_get(v_v_2688_, 0);
v_ringId_x3f_2690_ = lean_ctor_get(v_v_2688_, 1);
v_type_2691_ = lean_ctor_get(v_v_2688_, 2);
v_u_2692_ = lean_ctor_get(v_v_2688_, 3);
v_intModuleInst_2693_ = lean_ctor_get(v_v_2688_, 4);
v_leInst_x3f_2694_ = lean_ctor_get(v_v_2688_, 5);
v_ltInst_x3f_2695_ = lean_ctor_get(v_v_2688_, 6);
v_lawfulOrderLTInst_x3f_2696_ = lean_ctor_get(v_v_2688_, 7);
v_isPreorderInst_x3f_2697_ = lean_ctor_get(v_v_2688_, 8);
v_orderedAddInst_x3f_2698_ = lean_ctor_get(v_v_2688_, 9);
v_isLinearInst_x3f_2699_ = lean_ctor_get(v_v_2688_, 10);
v_noNatDivInst_x3f_2700_ = lean_ctor_get(v_v_2688_, 11);
v_ringInst_x3f_2701_ = lean_ctor_get(v_v_2688_, 12);
v_commRingInst_x3f_2702_ = lean_ctor_get(v_v_2688_, 13);
v_orderedRingInst_x3f_2703_ = lean_ctor_get(v_v_2688_, 14);
v_fieldInst_x3f_2704_ = lean_ctor_get(v_v_2688_, 15);
v_charInst_x3f_2705_ = lean_ctor_get(v_v_2688_, 16);
v_zero_2706_ = lean_ctor_get(v_v_2688_, 17);
v_ofNatZero_2707_ = lean_ctor_get(v_v_2688_, 18);
v_one_x3f_2708_ = lean_ctor_get(v_v_2688_, 19);
v_leFn_x3f_2709_ = lean_ctor_get(v_v_2688_, 20);
v_ltFn_x3f_2710_ = lean_ctor_get(v_v_2688_, 21);
v_addFn_2711_ = lean_ctor_get(v_v_2688_, 22);
v_zsmulFn_2712_ = lean_ctor_get(v_v_2688_, 23);
v_nsmulFn_2713_ = lean_ctor_get(v_v_2688_, 24);
v_zsmulFn_x3f_2714_ = lean_ctor_get(v_v_2688_, 25);
v_nsmulFn_x3f_2715_ = lean_ctor_get(v_v_2688_, 26);
v_homomulFn_x3f_2716_ = lean_ctor_get(v_v_2688_, 27);
v_subFn_2717_ = lean_ctor_get(v_v_2688_, 28);
v_negFn_2718_ = lean_ctor_get(v_v_2688_, 29);
v_vars_2719_ = lean_ctor_get(v_v_2688_, 30);
v_varMap_2720_ = lean_ctor_get(v_v_2688_, 31);
v_lowers_2721_ = lean_ctor_get(v_v_2688_, 32);
v_uppers_2722_ = lean_ctor_get(v_v_2688_, 33);
v_diseqs_2723_ = lean_ctor_get(v_v_2688_, 34);
v_assignment_2724_ = lean_ctor_get(v_v_2688_, 35);
v_caseSplits_2725_ = lean_ctor_get_uint8(v_v_2688_, sizeof(void*)*42);
v_conflict_x3f_2726_ = lean_ctor_get(v_v_2688_, 36);
v_diseqSplits_2727_ = lean_ctor_get(v_v_2688_, 37);
v_elimEqs_2728_ = lean_ctor_get(v_v_2688_, 38);
v_elimStack_2729_ = lean_ctor_get(v_v_2688_, 39);
v_occurs_2730_ = lean_ctor_get(v_v_2688_, 40);
v_ignored_2731_ = lean_ctor_get(v_v_2688_, 41);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_v_2688_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2733_ = v_v_2688_;
v_isShared_2734_ = v_isSharedCheck_2745_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_ignored_2731_);
lean_inc(v_occurs_2730_);
lean_inc(v_elimStack_2729_);
lean_inc(v_elimEqs_2728_);
lean_inc(v_diseqSplits_2727_);
lean_inc(v_conflict_x3f_2726_);
lean_inc(v_assignment_2724_);
lean_inc(v_diseqs_2723_);
lean_inc(v_uppers_2722_);
lean_inc(v_lowers_2721_);
lean_inc(v_varMap_2720_);
lean_inc(v_vars_2719_);
lean_inc(v_negFn_2718_);
lean_inc(v_subFn_2717_);
lean_inc(v_homomulFn_x3f_2716_);
lean_inc(v_nsmulFn_x3f_2715_);
lean_inc(v_zsmulFn_x3f_2714_);
lean_inc(v_nsmulFn_2713_);
lean_inc(v_zsmulFn_2712_);
lean_inc(v_addFn_2711_);
lean_inc(v_ltFn_x3f_2710_);
lean_inc(v_leFn_x3f_2709_);
lean_inc(v_one_x3f_2708_);
lean_inc(v_ofNatZero_2707_);
lean_inc(v_zero_2706_);
lean_inc(v_charInst_x3f_2705_);
lean_inc(v_fieldInst_x3f_2704_);
lean_inc(v_orderedRingInst_x3f_2703_);
lean_inc(v_commRingInst_x3f_2702_);
lean_inc(v_ringInst_x3f_2701_);
lean_inc(v_noNatDivInst_x3f_2700_);
lean_inc(v_isLinearInst_x3f_2699_);
lean_inc(v_orderedAddInst_x3f_2698_);
lean_inc(v_isPreorderInst_x3f_2697_);
lean_inc(v_lawfulOrderLTInst_x3f_2696_);
lean_inc(v_ltInst_x3f_2695_);
lean_inc(v_leInst_x3f_2694_);
lean_inc(v_intModuleInst_2693_);
lean_inc(v_u_2692_);
lean_inc(v_type_2691_);
lean_inc(v_ringId_x3f_2690_);
lean_inc(v_id_2689_);
lean_dec(v_v_2688_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2745_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; lean_object* v_xs_x27_2736_; lean_object* v___x_2737_; lean_object* v___x_2739_; 
v___x_2735_ = lean_box(0);
v_xs_x27_2736_ = lean_array_fset(v_structs_2675_, v___y_2672_, v___x_2735_);
v___x_2737_ = l_Lean_PersistentArray_push___redArg(v_ignored_2731_, v_a_2673_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 41, v___x_2737_);
v___x_2739_ = v___x_2733_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_id_2689_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_ringId_x3f_2690_);
lean_ctor_set(v_reuseFailAlloc_2744_, 2, v_type_2691_);
lean_ctor_set(v_reuseFailAlloc_2744_, 3, v_u_2692_);
lean_ctor_set(v_reuseFailAlloc_2744_, 4, v_intModuleInst_2693_);
lean_ctor_set(v_reuseFailAlloc_2744_, 5, v_leInst_x3f_2694_);
lean_ctor_set(v_reuseFailAlloc_2744_, 6, v_ltInst_x3f_2695_);
lean_ctor_set(v_reuseFailAlloc_2744_, 7, v_lawfulOrderLTInst_x3f_2696_);
lean_ctor_set(v_reuseFailAlloc_2744_, 8, v_isPreorderInst_x3f_2697_);
lean_ctor_set(v_reuseFailAlloc_2744_, 9, v_orderedAddInst_x3f_2698_);
lean_ctor_set(v_reuseFailAlloc_2744_, 10, v_isLinearInst_x3f_2699_);
lean_ctor_set(v_reuseFailAlloc_2744_, 11, v_noNatDivInst_x3f_2700_);
lean_ctor_set(v_reuseFailAlloc_2744_, 12, v_ringInst_x3f_2701_);
lean_ctor_set(v_reuseFailAlloc_2744_, 13, v_commRingInst_x3f_2702_);
lean_ctor_set(v_reuseFailAlloc_2744_, 14, v_orderedRingInst_x3f_2703_);
lean_ctor_set(v_reuseFailAlloc_2744_, 15, v_fieldInst_x3f_2704_);
lean_ctor_set(v_reuseFailAlloc_2744_, 16, v_charInst_x3f_2705_);
lean_ctor_set(v_reuseFailAlloc_2744_, 17, v_zero_2706_);
lean_ctor_set(v_reuseFailAlloc_2744_, 18, v_ofNatZero_2707_);
lean_ctor_set(v_reuseFailAlloc_2744_, 19, v_one_x3f_2708_);
lean_ctor_set(v_reuseFailAlloc_2744_, 20, v_leFn_x3f_2709_);
lean_ctor_set(v_reuseFailAlloc_2744_, 21, v_ltFn_x3f_2710_);
lean_ctor_set(v_reuseFailAlloc_2744_, 22, v_addFn_2711_);
lean_ctor_set(v_reuseFailAlloc_2744_, 23, v_zsmulFn_2712_);
lean_ctor_set(v_reuseFailAlloc_2744_, 24, v_nsmulFn_2713_);
lean_ctor_set(v_reuseFailAlloc_2744_, 25, v_zsmulFn_x3f_2714_);
lean_ctor_set(v_reuseFailAlloc_2744_, 26, v_nsmulFn_x3f_2715_);
lean_ctor_set(v_reuseFailAlloc_2744_, 27, v_homomulFn_x3f_2716_);
lean_ctor_set(v_reuseFailAlloc_2744_, 28, v_subFn_2717_);
lean_ctor_set(v_reuseFailAlloc_2744_, 29, v_negFn_2718_);
lean_ctor_set(v_reuseFailAlloc_2744_, 30, v_vars_2719_);
lean_ctor_set(v_reuseFailAlloc_2744_, 31, v_varMap_2720_);
lean_ctor_set(v_reuseFailAlloc_2744_, 32, v_lowers_2721_);
lean_ctor_set(v_reuseFailAlloc_2744_, 33, v_uppers_2722_);
lean_ctor_set(v_reuseFailAlloc_2744_, 34, v_diseqs_2723_);
lean_ctor_set(v_reuseFailAlloc_2744_, 35, v_assignment_2724_);
lean_ctor_set(v_reuseFailAlloc_2744_, 36, v_conflict_x3f_2726_);
lean_ctor_set(v_reuseFailAlloc_2744_, 37, v_diseqSplits_2727_);
lean_ctor_set(v_reuseFailAlloc_2744_, 38, v_elimEqs_2728_);
lean_ctor_set(v_reuseFailAlloc_2744_, 39, v_elimStack_2729_);
lean_ctor_set(v_reuseFailAlloc_2744_, 40, v_occurs_2730_);
lean_ctor_set(v_reuseFailAlloc_2744_, 41, v___x_2737_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, sizeof(void*)*42, v_caseSplits_2725_);
v___x_2739_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2740_ = lean_array_fset(v_xs_x27_2736_, v___y_2672_, v___x_2739_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v___x_2740_);
v___x_2742_ = v___x_2686_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2740_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_typeIdOf_2676_);
lean_ctor_set(v_reuseFailAlloc_2743_, 2, v_exprToStructId_2677_);
lean_ctor_set(v_reuseFailAlloc_2743_, 3, v_exprToStructIdEntries_2678_);
lean_ctor_set(v_reuseFailAlloc_2743_, 4, v_forbiddenNatModules_2679_);
lean_ctor_set(v_reuseFailAlloc_2743_, 5, v_natStructs_2680_);
lean_ctor_set(v_reuseFailAlloc_2743_, 6, v_natTypeIdOf_2681_);
lean_ctor_set(v_reuseFailAlloc_2743_, 7, v_exprToNatStructId_2682_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed(lean_object* v___y_2755_, lean_object* v_a_2756_, lean_object* v_s_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(v___y_2755_, v_a_2756_, v_s_2757_);
lean_dec(v___y_2755_);
return v_res_2758_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3(void){
_start:
{
lean_object* v_cls_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v_cls_2766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_2768_ = l_Lean_Name_append(v___x_2767_, v_cls_2766_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object* v_c_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v_options_2807_; uint8_t v_hasTrace_2808_; 
v_options_2807_ = lean_ctor_get(v_a_2779_, 2);
v_hasTrace_2808_ = lean_ctor_get_uint8(v_options_2807_, sizeof(void*)*1);
if (v_hasTrace_2808_ == 0)
{
v___y_2783_ = v_a_2770_;
v___y_2784_ = v_a_2771_;
v___y_2785_ = v_a_2772_;
v___y_2786_ = v_a_2773_;
v___y_2787_ = v_a_2774_;
v___y_2788_ = v_a_2775_;
v___y_2789_ = v_a_2776_;
v___y_2790_ = v_a_2777_;
v___y_2791_ = v_a_2778_;
v___y_2792_ = v_a_2779_;
v___y_2793_ = v_a_2780_;
goto v___jp_2782_;
}
else
{
lean_object* v_inheritedTraceOptions_2809_; lean_object* v_cls_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; 
v_inheritedTraceOptions_2809_ = lean_ctor_get(v_a_2779_, 13);
v_cls_2810_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2811_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3);
v___x_2812_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2809_, v_options_2807_, v___x_2811_);
if (v___x_2812_ == 0)
{
v___y_2783_ = v_a_2770_;
v___y_2784_ = v_a_2771_;
v___y_2785_ = v_a_2772_;
v___y_2786_ = v_a_2773_;
v___y_2787_ = v_a_2774_;
v___y_2788_ = v_a_2775_;
v___y_2789_ = v_a_2776_;
v___y_2790_ = v_a_2777_;
v___y_2791_ = v_a_2778_;
v___y_2792_ = v_a_2779_;
v___y_2793_ = v_a_2780_;
goto v___jp_2782_;
}
else
{
lean_object* v___x_2813_; 
v___x_2813_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref(v___x_2813_);
v___x_2815_ = l_Lean_MessageData_ofExpr(v_a_2814_);
v___x_2816_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_2810_, v___x_2815_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_dec_ref(v___x_2816_);
v___y_2783_ = v_a_2770_;
v___y_2784_ = v_a_2771_;
v___y_2785_ = v_a_2772_;
v___y_2786_ = v_a_2773_;
v___y_2787_ = v_a_2774_;
v___y_2788_ = v_a_2775_;
v___y_2789_ = v_a_2776_;
v___y_2790_ = v_a_2777_;
v___y_2791_ = v_a_2778_;
v___y_2792_ = v_a_2779_;
v___y_2793_ = v_a_2780_;
goto v___jp_2782_;
}
else
{
return v___x_2816_;
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
v_a_2817_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2813_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2813_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
}
v___jp_2782_:
{
lean_object* v___x_2794_; 
v___x_2794_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2769_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___f_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
lean_dec_ref(v___x_2794_);
lean_inc(v___y_2783_);
v___f_2796_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2796_, 0, v___y_2783_);
lean_closure_set(v___f_2796_, 1, v_a_2795_);
v___x_2797_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2798_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2797_, v___f_2796_, v___y_2784_);
return v___x_2798_;
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
v_a_2799_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2794_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2794_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object* v_c_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
lean_dec(v_a_2836_);
lean_dec_ref(v_a_2835_);
lean_dec(v_a_2834_);
lean_dec_ref(v_a_2833_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
lean_dec(v_a_2828_);
lean_dec(v_a_2827_);
lean_dec(v_a_2826_);
lean_dec_ref(v_c_2825_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object* v_c_u2082_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v_p_2852_; lean_object* v_fileName_2853_; lean_object* v_fileMap_2854_; lean_object* v_options_2855_; lean_object* v_currRecDepth_2856_; lean_object* v_maxRecDepth_2857_; lean_object* v_ref_2858_; lean_object* v_currNamespace_2859_; lean_object* v_openDecls_2860_; lean_object* v_initHeartbeats_2861_; lean_object* v_maxHeartbeats_2862_; lean_object* v_quotContext_2863_; lean_object* v_currMacroScope_2864_; uint8_t v_diag_2865_; lean_object* v_cancelTk_x3f_2866_; uint8_t v_suppressElabErrors_2867_; lean_object* v_inheritedTraceOptions_2868_; lean_object* v___x_2920_; uint8_t v___x_2921_; 
v_p_2852_ = lean_ctor_get(v_c_u2082_2839_, 0);
v_fileName_2853_ = lean_ctor_get(v_a_2849_, 0);
lean_inc_ref(v_fileName_2853_);
v_fileMap_2854_ = lean_ctor_get(v_a_2849_, 1);
lean_inc_ref(v_fileMap_2854_);
v_options_2855_ = lean_ctor_get(v_a_2849_, 2);
lean_inc_ref(v_options_2855_);
v_currRecDepth_2856_ = lean_ctor_get(v_a_2849_, 3);
lean_inc(v_currRecDepth_2856_);
v_maxRecDepth_2857_ = lean_ctor_get(v_a_2849_, 4);
lean_inc(v_maxRecDepth_2857_);
v_ref_2858_ = lean_ctor_get(v_a_2849_, 5);
lean_inc(v_ref_2858_);
v_currNamespace_2859_ = lean_ctor_get(v_a_2849_, 6);
lean_inc(v_currNamespace_2859_);
v_openDecls_2860_ = lean_ctor_get(v_a_2849_, 7);
lean_inc(v_openDecls_2860_);
v_initHeartbeats_2861_ = lean_ctor_get(v_a_2849_, 8);
lean_inc(v_initHeartbeats_2861_);
v_maxHeartbeats_2862_ = lean_ctor_get(v_a_2849_, 9);
lean_inc(v_maxHeartbeats_2862_);
v_quotContext_2863_ = lean_ctor_get(v_a_2849_, 10);
lean_inc(v_quotContext_2863_);
v_currMacroScope_2864_ = lean_ctor_get(v_a_2849_, 11);
lean_inc(v_currMacroScope_2864_);
v_diag_2865_ = lean_ctor_get_uint8(v_a_2849_, sizeof(void*)*14);
v_cancelTk_x3f_2866_ = lean_ctor_get(v_a_2849_, 12);
lean_inc(v_cancelTk_x3f_2866_);
v_suppressElabErrors_2867_ = lean_ctor_get_uint8(v_a_2849_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2868_ = lean_ctor_get(v_a_2849_, 13);
lean_inc_ref(v_inheritedTraceOptions_2868_);
lean_dec_ref(v_a_2849_);
v___x_2920_ = lean_unsigned_to_nat(0u);
v___x_2921_ = lean_nat_dec_eq(v_maxRecDepth_2857_, v___x_2920_);
if (v___x_2921_ == 0)
{
uint8_t v___x_2922_; 
v___x_2922_ = lean_nat_dec_eq(v_currRecDepth_2856_, v_maxRecDepth_2857_);
if (v___x_2922_ == 0)
{
goto v___jp_2869_;
}
else
{
lean_object* v___x_2923_; 
lean_dec_ref(v_inheritedTraceOptions_2868_);
lean_dec(v_cancelTk_x3f_2866_);
lean_dec(v_currMacroScope_2864_);
lean_dec(v_quotContext_2863_);
lean_dec(v_maxHeartbeats_2862_);
lean_dec(v_initHeartbeats_2861_);
lean_dec(v_openDecls_2860_);
lean_dec(v_currNamespace_2859_);
lean_dec(v_maxRecDepth_2857_);
lean_dec(v_currRecDepth_2856_);
lean_dec_ref(v_options_2855_);
lean_dec_ref(v_fileMap_2854_);
lean_dec_ref(v_fileName_2853_);
lean_dec_ref(v_c_u2082_2839_);
v___x_2923_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_2858_);
return v___x_2923_;
}
}
else
{
goto v___jp_2869_;
}
v___jp_2869_:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2870_ = lean_unsigned_to_nat(1u);
v___x_2871_ = lean_nat_add(v_currRecDepth_2856_, v___x_2870_);
lean_dec(v_currRecDepth_2856_);
v___x_2872_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2872_, 0, v_fileName_2853_);
lean_ctor_set(v___x_2872_, 1, v_fileMap_2854_);
lean_ctor_set(v___x_2872_, 2, v_options_2855_);
lean_ctor_set(v___x_2872_, 3, v___x_2871_);
lean_ctor_set(v___x_2872_, 4, v_maxRecDepth_2857_);
lean_ctor_set(v___x_2872_, 5, v_ref_2858_);
lean_ctor_set(v___x_2872_, 6, v_currNamespace_2859_);
lean_ctor_set(v___x_2872_, 7, v_openDecls_2860_);
lean_ctor_set(v___x_2872_, 8, v_initHeartbeats_2861_);
lean_ctor_set(v___x_2872_, 9, v_maxHeartbeats_2862_);
lean_ctor_set(v___x_2872_, 10, v_quotContext_2863_);
lean_ctor_set(v___x_2872_, 11, v_currMacroScope_2864_);
lean_ctor_set(v___x_2872_, 12, v_cancelTk_x3f_2866_);
lean_ctor_set(v___x_2872_, 13, v_inheritedTraceOptions_2868_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*14, v_diag_2865_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*14 + 1, v_suppressElabErrors_2867_);
v___x_2873_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2852_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v___x_2872_, v_a_2850_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2911_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2876_ = v___x_2873_;
v_isShared_2877_ = v_isSharedCheck_2911_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2873_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2911_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
if (lean_obj_tag(v_a_2874_) == 1)
{
lean_object* v_val_2878_; lean_object* v_snd_2879_; lean_object* v_snd_2880_; lean_object* v_fst_2881_; lean_object* v_fst_2882_; lean_object* v_p_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
lean_del_object(v___x_2876_);
v_val_2878_ = lean_ctor_get(v_a_2874_, 0);
lean_inc(v_val_2878_);
lean_dec_ref(v_a_2874_);
v_snd_2879_ = lean_ctor_get(v_val_2878_, 1);
lean_inc(v_snd_2879_);
v_snd_2880_ = lean_ctor_get(v_snd_2879_, 1);
lean_inc(v_snd_2880_);
v_fst_2881_ = lean_ctor_get(v_val_2878_, 0);
lean_inc(v_fst_2881_);
lean_dec(v_val_2878_);
v_fst_2882_ = lean_ctor_get(v_snd_2879_, 0);
lean_inc(v_fst_2882_);
lean_dec(v_snd_2879_);
v_p_2883_ = lean_ctor_get(v_snd_2880_, 0);
v___x_2884_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2883_, v_fst_2882_);
lean_inc_ref(v_c_u2082_2839_);
v___x_2885_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v___x_2884_, v_fst_2882_, v_snd_2880_, v_fst_2881_, v_c_u2082_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v___x_2872_, v_a_2850_);
lean_dec(v_fst_2882_);
lean_dec(v___x_2884_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref(v___x_2885_);
if (lean_obj_tag(v_a_2886_) == 1)
{
lean_object* v_val_2887_; 
lean_dec_ref(v_c_u2082_2839_);
v_val_2887_ = lean_ctor_get(v_a_2886_, 0);
lean_inc(v_val_2887_);
lean_dec_ref(v_a_2886_);
v_c_u2082_2839_ = v_val_2887_;
v_a_2849_ = v___x_2872_;
goto _start;
}
else
{
lean_object* v___x_2889_; 
lean_dec(v_a_2886_);
v___x_2889_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_u2082_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v___x_2872_, v_a_2850_);
lean_dec_ref(v___x_2872_);
lean_dec_ref(v_c_u2082_2839_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2897_; 
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2897_ == 0)
{
lean_object* v_unused_2898_; 
v_unused_2898_ = lean_ctor_get(v___x_2889_, 0);
lean_dec(v_unused_2898_);
v___x_2891_ = v___x_2889_;
v_isShared_2892_ = v_isSharedCheck_2897_;
goto v_resetjp_2890_;
}
else
{
lean_dec(v___x_2889_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2897_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2893_; lean_object* v___x_2895_; 
v___x_2893_ = lean_box(0);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 0, v___x_2893_);
v___x_2895_ = v___x_2891_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
v_a_2899_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2889_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2889_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2872_);
lean_dec_ref(v_c_u2082_2839_);
return v___x_2885_;
}
}
else
{
lean_object* v___x_2907_; lean_object* v___x_2909_; 
lean_dec(v_a_2874_);
lean_dec_ref(v___x_2872_);
v___x_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2907_, 0, v_c_u2082_2839_);
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 0, v___x_2907_);
v___x_2909_ = v___x_2876_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2907_);
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
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec_ref(v___x_2872_);
lean_dec_ref(v_c_u2082_2839_);
v_a_2912_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2873_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2873_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object* v_c_u2082_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_u2082_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_);
lean_dec(v_a_2935_);
lean_dec(v_a_2933_);
lean_dec_ref(v_a_2932_);
lean_dec(v_a_2931_);
lean_dec_ref(v_a_2930_);
lean_dec(v_a_2929_);
lean_dec_ref(v_a_2928_);
lean_dec(v_a_2927_);
lean_dec(v_a_2926_);
lean_dec(v_a_2925_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object* v_val_2938_, lean_object* v_x_2939_, size_t v_x_2940_, size_t v_x_2941_){
_start:
{
if (lean_obj_tag(v_x_2939_) == 0)
{
lean_object* v_cs_2942_; size_t v_j_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; uint8_t v___x_2946_; 
v_cs_2942_ = lean_ctor_get(v_x_2939_, 0);
v_j_2943_ = lean_usize_shift_right(v_x_2940_, v_x_2941_);
v___x_2944_ = lean_usize_to_nat(v_j_2943_);
v___x_2945_ = lean_array_get_size(v_cs_2942_);
v___x_2946_ = lean_nat_dec_lt(v___x_2944_, v___x_2945_);
if (v___x_2946_ == 0)
{
lean_dec(v___x_2944_);
lean_dec_ref(v_val_2938_);
return v_x_2939_;
}
else
{
lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2964_; 
lean_inc_ref(v_cs_2942_);
v_isSharedCheck_2964_ = !lean_is_exclusive(v_x_2939_);
if (v_isSharedCheck_2964_ == 0)
{
lean_object* v_unused_2965_; 
v_unused_2965_ = lean_ctor_get(v_x_2939_, 0);
lean_dec(v_unused_2965_);
v___x_2948_ = v_x_2939_;
v_isShared_2949_ = v_isSharedCheck_2964_;
goto v_resetjp_2947_;
}
else
{
lean_dec(v_x_2939_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2964_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
size_t v___x_2950_; size_t v___x_2951_; size_t v___x_2952_; size_t v_i_2953_; size_t v___x_2954_; size_t v_shift_2955_; lean_object* v_v_2956_; lean_object* v___x_2957_; lean_object* v_xs_x27_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2962_; 
v___x_2950_ = ((size_t)1ULL);
v___x_2951_ = lean_usize_shift_left(v___x_2950_, v_x_2941_);
v___x_2952_ = lean_usize_sub(v___x_2951_, v___x_2950_);
v_i_2953_ = lean_usize_land(v_x_2940_, v___x_2952_);
v___x_2954_ = ((size_t)5ULL);
v_shift_2955_ = lean_usize_sub(v_x_2941_, v___x_2954_);
v_v_2956_ = lean_array_fget(v_cs_2942_, v___x_2944_);
v___x_2957_ = lean_box(0);
v_xs_x27_2958_ = lean_array_fset(v_cs_2942_, v___x_2944_, v___x_2957_);
v___x_2959_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2938_, v_v_2956_, v_i_2953_, v_shift_2955_);
v___x_2960_ = lean_array_fset(v_xs_x27_2958_, v___x_2944_, v___x_2959_);
lean_dec(v___x_2944_);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 0, v___x_2960_);
v___x_2962_ = v___x_2948_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2960_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
else
{
lean_object* v_vs_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; uint8_t v___x_2969_; 
v_vs_2966_ = lean_ctor_get(v_x_2939_, 0);
v___x_2967_ = lean_usize_to_nat(v_x_2940_);
v___x_2968_ = lean_array_get_size(v_vs_2966_);
v___x_2969_ = lean_nat_dec_lt(v___x_2967_, v___x_2968_);
if (v___x_2969_ == 0)
{
lean_dec(v___x_2967_);
lean_dec_ref(v_val_2938_);
return v_x_2939_;
}
else
{
lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2981_; 
lean_inc_ref(v_vs_2966_);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_x_2939_);
if (v_isSharedCheck_2981_ == 0)
{
lean_object* v_unused_2982_; 
v_unused_2982_ = lean_ctor_get(v_x_2939_, 0);
lean_dec(v_unused_2982_);
v___x_2971_ = v_x_2939_;
v_isShared_2972_ = v_isSharedCheck_2981_;
goto v_resetjp_2970_;
}
else
{
lean_dec(v_x_2939_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2981_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v_v_2973_; lean_object* v___x_2974_; lean_object* v_xs_x27_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2979_; 
v_v_2973_ = lean_array_fget(v_vs_2966_, v___x_2967_);
v___x_2974_ = lean_box(0);
v_xs_x27_2975_ = lean_array_fset(v_vs_2966_, v___x_2967_, v___x_2974_);
v___x_2976_ = l_Lean_PersistentArray_push___redArg(v_v_2973_, v_val_2938_);
v___x_2977_ = lean_array_fset(v_xs_x27_2975_, v___x_2967_, v___x_2976_);
lean_dec(v___x_2967_);
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 0, v___x_2977_);
v___x_2979_ = v___x_2971_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2977_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_val_2983_, lean_object* v_x_2984_, lean_object* v_x_2985_, lean_object* v_x_2986_){
_start:
{
size_t v_x_53650__boxed_2987_; size_t v_x_53651__boxed_2988_; lean_object* v_res_2989_; 
v_x_53650__boxed_2987_ = lean_unbox_usize(v_x_2985_);
lean_dec(v_x_2985_);
v_x_53651__boxed_2988_ = lean_unbox_usize(v_x_2986_);
lean_dec(v_x_2986_);
v_res_2989_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2983_, v_x_2984_, v_x_53650__boxed_2987_, v_x_53651__boxed_2988_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object* v_val_2990_, lean_object* v_t_2991_, lean_object* v_i_2992_){
_start:
{
lean_object* v_root_2993_; lean_object* v_tail_2994_; lean_object* v_size_2995_; size_t v_shift_2996_; lean_object* v_tailOff_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3021_; 
v_root_2993_ = lean_ctor_get(v_t_2991_, 0);
v_tail_2994_ = lean_ctor_get(v_t_2991_, 1);
v_size_2995_ = lean_ctor_get(v_t_2991_, 2);
v_shift_2996_ = lean_ctor_get_usize(v_t_2991_, 4);
v_tailOff_2997_ = lean_ctor_get(v_t_2991_, 3);
v_isSharedCheck_3021_ = !lean_is_exclusive(v_t_2991_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_2999_ = v_t_2991_;
v_isShared_3000_ = v_isSharedCheck_3021_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_tailOff_2997_);
lean_inc(v_size_2995_);
lean_inc(v_tail_2994_);
lean_inc(v_root_2993_);
lean_dec(v_t_2991_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3021_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
uint8_t v___x_3001_; 
v___x_3001_ = lean_nat_dec_le(v_tailOff_2997_, v_i_2992_);
if (v___x_3001_ == 0)
{
size_t v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3005_; 
v___x_3002_ = lean_usize_of_nat(v_i_2992_);
v___x_3003_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2990_, v_root_2993_, v___x_3002_, v_shift_2996_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 0, v___x_3003_);
v___x_3005_ = v___x_2999_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_3003_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v_tail_2994_);
lean_ctor_set(v_reuseFailAlloc_3006_, 2, v_size_2995_);
lean_ctor_set(v_reuseFailAlloc_3006_, 3, v_tailOff_2997_);
lean_ctor_set_usize(v_reuseFailAlloc_3006_, 4, v_shift_2996_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
else
{
lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_3007_ = lean_nat_sub(v_i_2992_, v_tailOff_2997_);
v___x_3008_ = lean_array_get_size(v_tail_2994_);
v___x_3009_ = lean_nat_dec_lt(v___x_3007_, v___x_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3011_; 
lean_dec(v___x_3007_);
lean_dec_ref(v_val_2990_);
if (v_isShared_3000_ == 0)
{
v___x_3011_ = v___x_2999_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_root_2993_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_tail_2994_);
lean_ctor_set(v_reuseFailAlloc_3012_, 2, v_size_2995_);
lean_ctor_set(v_reuseFailAlloc_3012_, 3, v_tailOff_2997_);
lean_ctor_set_usize(v_reuseFailAlloc_3012_, 4, v_shift_2996_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
else
{
lean_object* v_v_3013_; lean_object* v___x_3014_; lean_object* v_xs_x27_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3019_; 
v_v_3013_ = lean_array_fget(v_tail_2994_, v___x_3007_);
v___x_3014_ = lean_box(0);
v_xs_x27_3015_ = lean_array_fset(v_tail_2994_, v___x_3007_, v___x_3014_);
v___x_3016_ = l_Lean_PersistentArray_push___redArg(v_v_3013_, v_val_2990_);
v___x_3017_ = lean_array_fset(v_xs_x27_3015_, v___x_3007_, v___x_3016_);
lean_dec(v___x_3007_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 1, v___x_3017_);
v___x_3019_ = v___x_2999_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_root_2993_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v___x_3017_);
lean_ctor_set(v_reuseFailAlloc_3020_, 2, v_size_2995_);
lean_ctor_set(v_reuseFailAlloc_3020_, 3, v_tailOff_2997_);
lean_ctor_set_usize(v_reuseFailAlloc_3020_, 4, v_shift_2996_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object* v_val_3022_, lean_object* v_t_3023_, lean_object* v_i_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3022_, v_t_3023_, v_i_3024_);
lean_dec(v_i_3024_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(lean_object* v___y_3026_, lean_object* v_val_3027_, lean_object* v_v_3028_, lean_object* v_s_3029_){
_start:
{
lean_object* v_structs_3030_; lean_object* v_typeIdOf_3031_; lean_object* v_exprToStructId_3032_; lean_object* v_exprToStructIdEntries_3033_; lean_object* v_forbiddenNatModules_3034_; lean_object* v_natStructs_3035_; lean_object* v_natTypeIdOf_3036_; lean_object* v_exprToNatStructId_3037_; lean_object* v___x_3038_; uint8_t v___x_3039_; 
v_structs_3030_ = lean_ctor_get(v_s_3029_, 0);
v_typeIdOf_3031_ = lean_ctor_get(v_s_3029_, 1);
v_exprToStructId_3032_ = lean_ctor_get(v_s_3029_, 2);
v_exprToStructIdEntries_3033_ = lean_ctor_get(v_s_3029_, 3);
v_forbiddenNatModules_3034_ = lean_ctor_get(v_s_3029_, 4);
v_natStructs_3035_ = lean_ctor_get(v_s_3029_, 5);
v_natTypeIdOf_3036_ = lean_ctor_get(v_s_3029_, 6);
v_exprToNatStructId_3037_ = lean_ctor_get(v_s_3029_, 7);
v___x_3038_ = lean_array_get_size(v_structs_3030_);
v___x_3039_ = lean_nat_dec_lt(v___y_3026_, v___x_3038_);
if (v___x_3039_ == 0)
{
lean_dec_ref(v_val_3027_);
return v_s_3029_;
}
else
{
lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3101_; 
lean_inc_ref(v_exprToNatStructId_3037_);
lean_inc_ref(v_natTypeIdOf_3036_);
lean_inc_ref(v_natStructs_3035_);
lean_inc_ref(v_forbiddenNatModules_3034_);
lean_inc_ref(v_exprToStructIdEntries_3033_);
lean_inc_ref(v_exprToStructId_3032_);
lean_inc_ref(v_typeIdOf_3031_);
lean_inc_ref(v_structs_3030_);
v_isSharedCheck_3101_ = !lean_is_exclusive(v_s_3029_);
if (v_isSharedCheck_3101_ == 0)
{
lean_object* v_unused_3102_; lean_object* v_unused_3103_; lean_object* v_unused_3104_; lean_object* v_unused_3105_; lean_object* v_unused_3106_; lean_object* v_unused_3107_; lean_object* v_unused_3108_; lean_object* v_unused_3109_; 
v_unused_3102_ = lean_ctor_get(v_s_3029_, 7);
lean_dec(v_unused_3102_);
v_unused_3103_ = lean_ctor_get(v_s_3029_, 6);
lean_dec(v_unused_3103_);
v_unused_3104_ = lean_ctor_get(v_s_3029_, 5);
lean_dec(v_unused_3104_);
v_unused_3105_ = lean_ctor_get(v_s_3029_, 4);
lean_dec(v_unused_3105_);
v_unused_3106_ = lean_ctor_get(v_s_3029_, 3);
lean_dec(v_unused_3106_);
v_unused_3107_ = lean_ctor_get(v_s_3029_, 2);
lean_dec(v_unused_3107_);
v_unused_3108_ = lean_ctor_get(v_s_3029_, 1);
lean_dec(v_unused_3108_);
v_unused_3109_ = lean_ctor_get(v_s_3029_, 0);
lean_dec(v_unused_3109_);
v___x_3041_ = v_s_3029_;
v_isShared_3042_ = v_isSharedCheck_3101_;
goto v_resetjp_3040_;
}
else
{
lean_dec(v_s_3029_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3101_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v_v_3043_; lean_object* v_id_3044_; lean_object* v_ringId_x3f_3045_; lean_object* v_type_3046_; lean_object* v_u_3047_; lean_object* v_intModuleInst_3048_; lean_object* v_leInst_x3f_3049_; lean_object* v_ltInst_x3f_3050_; lean_object* v_lawfulOrderLTInst_x3f_3051_; lean_object* v_isPreorderInst_x3f_3052_; lean_object* v_orderedAddInst_x3f_3053_; lean_object* v_isLinearInst_x3f_3054_; lean_object* v_noNatDivInst_x3f_3055_; lean_object* v_ringInst_x3f_3056_; lean_object* v_commRingInst_x3f_3057_; lean_object* v_orderedRingInst_x3f_3058_; lean_object* v_fieldInst_x3f_3059_; lean_object* v_charInst_x3f_3060_; lean_object* v_zero_3061_; lean_object* v_ofNatZero_3062_; lean_object* v_one_x3f_3063_; lean_object* v_leFn_x3f_3064_; lean_object* v_ltFn_x3f_3065_; lean_object* v_addFn_3066_; lean_object* v_zsmulFn_3067_; lean_object* v_nsmulFn_3068_; lean_object* v_zsmulFn_x3f_3069_; lean_object* v_nsmulFn_x3f_3070_; lean_object* v_homomulFn_x3f_3071_; lean_object* v_subFn_3072_; lean_object* v_negFn_3073_; lean_object* v_vars_3074_; lean_object* v_varMap_3075_; lean_object* v_lowers_3076_; lean_object* v_uppers_3077_; lean_object* v_diseqs_3078_; lean_object* v_assignment_3079_; uint8_t v_caseSplits_3080_; lean_object* v_conflict_x3f_3081_; lean_object* v_diseqSplits_3082_; lean_object* v_elimEqs_3083_; lean_object* v_elimStack_3084_; lean_object* v_occurs_3085_; lean_object* v_ignored_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3100_; 
v_v_3043_ = lean_array_fget(v_structs_3030_, v___y_3026_);
v_id_3044_ = lean_ctor_get(v_v_3043_, 0);
v_ringId_x3f_3045_ = lean_ctor_get(v_v_3043_, 1);
v_type_3046_ = lean_ctor_get(v_v_3043_, 2);
v_u_3047_ = lean_ctor_get(v_v_3043_, 3);
v_intModuleInst_3048_ = lean_ctor_get(v_v_3043_, 4);
v_leInst_x3f_3049_ = lean_ctor_get(v_v_3043_, 5);
v_ltInst_x3f_3050_ = lean_ctor_get(v_v_3043_, 6);
v_lawfulOrderLTInst_x3f_3051_ = lean_ctor_get(v_v_3043_, 7);
v_isPreorderInst_x3f_3052_ = lean_ctor_get(v_v_3043_, 8);
v_orderedAddInst_x3f_3053_ = lean_ctor_get(v_v_3043_, 9);
v_isLinearInst_x3f_3054_ = lean_ctor_get(v_v_3043_, 10);
v_noNatDivInst_x3f_3055_ = lean_ctor_get(v_v_3043_, 11);
v_ringInst_x3f_3056_ = lean_ctor_get(v_v_3043_, 12);
v_commRingInst_x3f_3057_ = lean_ctor_get(v_v_3043_, 13);
v_orderedRingInst_x3f_3058_ = lean_ctor_get(v_v_3043_, 14);
v_fieldInst_x3f_3059_ = lean_ctor_get(v_v_3043_, 15);
v_charInst_x3f_3060_ = lean_ctor_get(v_v_3043_, 16);
v_zero_3061_ = lean_ctor_get(v_v_3043_, 17);
v_ofNatZero_3062_ = lean_ctor_get(v_v_3043_, 18);
v_one_x3f_3063_ = lean_ctor_get(v_v_3043_, 19);
v_leFn_x3f_3064_ = lean_ctor_get(v_v_3043_, 20);
v_ltFn_x3f_3065_ = lean_ctor_get(v_v_3043_, 21);
v_addFn_3066_ = lean_ctor_get(v_v_3043_, 22);
v_zsmulFn_3067_ = lean_ctor_get(v_v_3043_, 23);
v_nsmulFn_3068_ = lean_ctor_get(v_v_3043_, 24);
v_zsmulFn_x3f_3069_ = lean_ctor_get(v_v_3043_, 25);
v_nsmulFn_x3f_3070_ = lean_ctor_get(v_v_3043_, 26);
v_homomulFn_x3f_3071_ = lean_ctor_get(v_v_3043_, 27);
v_subFn_3072_ = lean_ctor_get(v_v_3043_, 28);
v_negFn_3073_ = lean_ctor_get(v_v_3043_, 29);
v_vars_3074_ = lean_ctor_get(v_v_3043_, 30);
v_varMap_3075_ = lean_ctor_get(v_v_3043_, 31);
v_lowers_3076_ = lean_ctor_get(v_v_3043_, 32);
v_uppers_3077_ = lean_ctor_get(v_v_3043_, 33);
v_diseqs_3078_ = lean_ctor_get(v_v_3043_, 34);
v_assignment_3079_ = lean_ctor_get(v_v_3043_, 35);
v_caseSplits_3080_ = lean_ctor_get_uint8(v_v_3043_, sizeof(void*)*42);
v_conflict_x3f_3081_ = lean_ctor_get(v_v_3043_, 36);
v_diseqSplits_3082_ = lean_ctor_get(v_v_3043_, 37);
v_elimEqs_3083_ = lean_ctor_get(v_v_3043_, 38);
v_elimStack_3084_ = lean_ctor_get(v_v_3043_, 39);
v_occurs_3085_ = lean_ctor_get(v_v_3043_, 40);
v_ignored_3086_ = lean_ctor_get(v_v_3043_, 41);
v_isSharedCheck_3100_ = !lean_is_exclusive(v_v_3043_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3088_ = v_v_3043_;
v_isShared_3089_ = v_isSharedCheck_3100_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_ignored_3086_);
lean_inc(v_occurs_3085_);
lean_inc(v_elimStack_3084_);
lean_inc(v_elimEqs_3083_);
lean_inc(v_diseqSplits_3082_);
lean_inc(v_conflict_x3f_3081_);
lean_inc(v_assignment_3079_);
lean_inc(v_diseqs_3078_);
lean_inc(v_uppers_3077_);
lean_inc(v_lowers_3076_);
lean_inc(v_varMap_3075_);
lean_inc(v_vars_3074_);
lean_inc(v_negFn_3073_);
lean_inc(v_subFn_3072_);
lean_inc(v_homomulFn_x3f_3071_);
lean_inc(v_nsmulFn_x3f_3070_);
lean_inc(v_zsmulFn_x3f_3069_);
lean_inc(v_nsmulFn_3068_);
lean_inc(v_zsmulFn_3067_);
lean_inc(v_addFn_3066_);
lean_inc(v_ltFn_x3f_3065_);
lean_inc(v_leFn_x3f_3064_);
lean_inc(v_one_x3f_3063_);
lean_inc(v_ofNatZero_3062_);
lean_inc(v_zero_3061_);
lean_inc(v_charInst_x3f_3060_);
lean_inc(v_fieldInst_x3f_3059_);
lean_inc(v_orderedRingInst_x3f_3058_);
lean_inc(v_commRingInst_x3f_3057_);
lean_inc(v_ringInst_x3f_3056_);
lean_inc(v_noNatDivInst_x3f_3055_);
lean_inc(v_isLinearInst_x3f_3054_);
lean_inc(v_orderedAddInst_x3f_3053_);
lean_inc(v_isPreorderInst_x3f_3052_);
lean_inc(v_lawfulOrderLTInst_x3f_3051_);
lean_inc(v_ltInst_x3f_3050_);
lean_inc(v_leInst_x3f_3049_);
lean_inc(v_intModuleInst_3048_);
lean_inc(v_u_3047_);
lean_inc(v_type_3046_);
lean_inc(v_ringId_x3f_3045_);
lean_inc(v_id_3044_);
lean_dec(v_v_3043_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3100_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3090_; lean_object* v_xs_x27_3091_; lean_object* v___x_3092_; lean_object* v___x_3094_; 
v___x_3090_ = lean_box(0);
v_xs_x27_3091_ = lean_array_fset(v_structs_3030_, v___y_3026_, v___x_3090_);
v___x_3092_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3027_, v_diseqs_3078_, v_v_3028_);
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 34, v___x_3092_);
v___x_3094_ = v___x_3088_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_id_3044_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v_ringId_x3f_3045_);
lean_ctor_set(v_reuseFailAlloc_3099_, 2, v_type_3046_);
lean_ctor_set(v_reuseFailAlloc_3099_, 3, v_u_3047_);
lean_ctor_set(v_reuseFailAlloc_3099_, 4, v_intModuleInst_3048_);
lean_ctor_set(v_reuseFailAlloc_3099_, 5, v_leInst_x3f_3049_);
lean_ctor_set(v_reuseFailAlloc_3099_, 6, v_ltInst_x3f_3050_);
lean_ctor_set(v_reuseFailAlloc_3099_, 7, v_lawfulOrderLTInst_x3f_3051_);
lean_ctor_set(v_reuseFailAlloc_3099_, 8, v_isPreorderInst_x3f_3052_);
lean_ctor_set(v_reuseFailAlloc_3099_, 9, v_orderedAddInst_x3f_3053_);
lean_ctor_set(v_reuseFailAlloc_3099_, 10, v_isLinearInst_x3f_3054_);
lean_ctor_set(v_reuseFailAlloc_3099_, 11, v_noNatDivInst_x3f_3055_);
lean_ctor_set(v_reuseFailAlloc_3099_, 12, v_ringInst_x3f_3056_);
lean_ctor_set(v_reuseFailAlloc_3099_, 13, v_commRingInst_x3f_3057_);
lean_ctor_set(v_reuseFailAlloc_3099_, 14, v_orderedRingInst_x3f_3058_);
lean_ctor_set(v_reuseFailAlloc_3099_, 15, v_fieldInst_x3f_3059_);
lean_ctor_set(v_reuseFailAlloc_3099_, 16, v_charInst_x3f_3060_);
lean_ctor_set(v_reuseFailAlloc_3099_, 17, v_zero_3061_);
lean_ctor_set(v_reuseFailAlloc_3099_, 18, v_ofNatZero_3062_);
lean_ctor_set(v_reuseFailAlloc_3099_, 19, v_one_x3f_3063_);
lean_ctor_set(v_reuseFailAlloc_3099_, 20, v_leFn_x3f_3064_);
lean_ctor_set(v_reuseFailAlloc_3099_, 21, v_ltFn_x3f_3065_);
lean_ctor_set(v_reuseFailAlloc_3099_, 22, v_addFn_3066_);
lean_ctor_set(v_reuseFailAlloc_3099_, 23, v_zsmulFn_3067_);
lean_ctor_set(v_reuseFailAlloc_3099_, 24, v_nsmulFn_3068_);
lean_ctor_set(v_reuseFailAlloc_3099_, 25, v_zsmulFn_x3f_3069_);
lean_ctor_set(v_reuseFailAlloc_3099_, 26, v_nsmulFn_x3f_3070_);
lean_ctor_set(v_reuseFailAlloc_3099_, 27, v_homomulFn_x3f_3071_);
lean_ctor_set(v_reuseFailAlloc_3099_, 28, v_subFn_3072_);
lean_ctor_set(v_reuseFailAlloc_3099_, 29, v_negFn_3073_);
lean_ctor_set(v_reuseFailAlloc_3099_, 30, v_vars_3074_);
lean_ctor_set(v_reuseFailAlloc_3099_, 31, v_varMap_3075_);
lean_ctor_set(v_reuseFailAlloc_3099_, 32, v_lowers_3076_);
lean_ctor_set(v_reuseFailAlloc_3099_, 33, v_uppers_3077_);
lean_ctor_set(v_reuseFailAlloc_3099_, 34, v___x_3092_);
lean_ctor_set(v_reuseFailAlloc_3099_, 35, v_assignment_3079_);
lean_ctor_set(v_reuseFailAlloc_3099_, 36, v_conflict_x3f_3081_);
lean_ctor_set(v_reuseFailAlloc_3099_, 37, v_diseqSplits_3082_);
lean_ctor_set(v_reuseFailAlloc_3099_, 38, v_elimEqs_3083_);
lean_ctor_set(v_reuseFailAlloc_3099_, 39, v_elimStack_3084_);
lean_ctor_set(v_reuseFailAlloc_3099_, 40, v_occurs_3085_);
lean_ctor_set(v_reuseFailAlloc_3099_, 41, v_ignored_3086_);
lean_ctor_set_uint8(v_reuseFailAlloc_3099_, sizeof(void*)*42, v_caseSplits_3080_);
v___x_3094_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
lean_object* v___x_3095_; lean_object* v___x_3097_; 
v___x_3095_ = lean_array_fset(v_xs_x27_3091_, v___y_3026_, v___x_3094_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 0, v___x_3095_);
v___x_3097_ = v___x_3041_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3095_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_typeIdOf_3031_);
lean_ctor_set(v_reuseFailAlloc_3098_, 2, v_exprToStructId_3032_);
lean_ctor_set(v_reuseFailAlloc_3098_, 3, v_exprToStructIdEntries_3033_);
lean_ctor_set(v_reuseFailAlloc_3098_, 4, v_forbiddenNatModules_3034_);
lean_ctor_set(v_reuseFailAlloc_3098_, 5, v_natStructs_3035_);
lean_ctor_set(v_reuseFailAlloc_3098_, 6, v_natTypeIdOf_3036_);
lean_ctor_set(v_reuseFailAlloc_3098_, 7, v_exprToNatStructId_3037_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed(lean_object* v___y_3110_, lean_object* v_val_3111_, lean_object* v_v_3112_, lean_object* v_s_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(v___y_3110_, v_val_3111_, v_v_3112_, v_s_3113_);
lean_dec(v_v_3112_);
lean_dec(v___y_3110_);
return v_res_3114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2(void){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3121_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3122_ = l_Lean_Name_append(v___x_3121_, v___x_3120_);
return v___x_3122_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3129_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3130_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3131_ = l_Lean_Name_append(v___x_3130_, v___x_3129_);
return v___x_3131_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7(void){
_start:
{
lean_object* v_cls_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v_cls_3136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3138_ = l_Lean_Name_append(v___x_3137_, v_cls_3136_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object* v_c_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v_options_3210_; lean_object* v_inheritedTraceOptions_3211_; uint8_t v_hasTrace_3212_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; 
v_options_3210_ = lean_ctor_get(v_a_3149_, 2);
v_inheritedTraceOptions_3211_ = lean_ctor_get(v_a_3149_, 13);
v_hasTrace_3212_ = lean_ctor_get_uint8(v_options_3210_, sizeof(void*)*1);
if (v_hasTrace_3212_ == 0)
{
v___y_3214_ = v_a_3140_;
v___y_3215_ = v_a_3141_;
v___y_3216_ = v_a_3142_;
v___y_3217_ = v_a_3143_;
v___y_3218_ = v_a_3144_;
v___y_3219_ = v_a_3145_;
v___y_3220_ = v_a_3146_;
v___y_3221_ = v_a_3147_;
v___y_3222_ = v_a_3148_;
v___y_3223_ = v_a_3149_;
v___y_3224_ = v_a_3150_;
goto v___jp_3213_;
}
else
{
lean_object* v_cls_3283_; lean_object* v___x_3284_; uint8_t v___x_3285_; 
v_cls_3283_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3284_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_3285_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3211_, v_options_3210_, v___x_3284_);
if (v___x_3285_ == 0)
{
v___y_3214_ = v_a_3140_;
v___y_3215_ = v_a_3141_;
v___y_3216_ = v_a_3142_;
v___y_3217_ = v_a_3143_;
v___y_3218_ = v_a_3144_;
v___y_3219_ = v_a_3145_;
v___y_3220_ = v_a_3146_;
v___y_3221_ = v_a_3147_;
v___y_3222_ = v_a_3148_;
v___y_3223_ = v_a_3149_;
v___y_3224_ = v_a_3150_;
goto v___jp_3213_;
}
else
{
lean_object* v___x_3286_; 
v___x_3286_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3287_);
lean_dec_ref(v___x_3286_);
v___x_3288_ = l_Lean_MessageData_ofExpr(v_a_3287_);
v___x_3289_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_3283_, v___x_3288_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_dec_ref(v___x_3289_);
v___y_3214_ = v_a_3140_;
v___y_3215_ = v_a_3141_;
v___y_3216_ = v_a_3142_;
v___y_3217_ = v_a_3143_;
v___y_3218_ = v_a_3144_;
v___y_3219_ = v_a_3145_;
v___y_3220_ = v_a_3146_;
v___y_3221_ = v_a_3147_;
v___y_3222_ = v_a_3148_;
v___y_3223_ = v_a_3149_;
v___y_3224_ = v_a_3150_;
goto v___jp_3213_;
}
else
{
lean_dec_ref(v_c_3139_);
return v___x_3289_;
}
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
lean_dec_ref(v_c_3139_);
v_a_3290_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3286_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3286_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
}
v___jp_3152_:
{
lean_object* v___x_3169_; 
v___x_3169_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_3155_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v___f_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
lean_dec_ref(v___x_3169_);
lean_inc(v___y_3158_);
v___f_3170_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3170_, 0, v___y_3158_);
lean_closure_set(v___f_3170_, 1, v___y_3154_);
lean_closure_set(v___f_3170_, 2, v___y_3153_);
v___x_3171_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3172_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3171_, v___f_3170_, v___y_3159_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v___x_3173_; 
lean_dec_ref(v___x_3172_);
v___x_3173_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3186_; 
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3176_ = v___x_3173_;
v_isShared_3177_ = v_isSharedCheck_3186_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3173_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3186_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
uint8_t v___x_3178_; uint8_t v___x_3179_; uint8_t v___x_3180_; 
v___x_3178_ = 0;
v___x_3179_ = lean_unbox(v_a_3174_);
lean_dec(v_a_3174_);
v___x_3180_ = l_Lean_instBEqLBool_beq(v___x_3179_, v___x_3178_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; lean_object* v___x_3183_; 
lean_dec(v___y_3156_);
v___x_3181_ = lean_box(0);
if (v_isShared_3177_ == 0)
{
lean_ctor_set(v___x_3176_, 0, v___x_3181_);
v___x_3183_ = v___x_3176_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3181_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
else
{
lean_object* v___x_3185_; 
lean_del_object(v___x_3176_);
v___x_3185_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_3156_, v___y_3158_, v___y_3159_);
return v___x_3185_;
}
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_dec(v___y_3156_);
v_a_3187_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3173_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3173_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
else
{
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
return v___x_3172_;
}
}
else
{
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
return v___x_3169_;
}
}
v___jp_3195_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3208_, 0, v___y_3196_);
v___x_3209_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(v___x_3208_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
return v___x_3209_;
}
v___jp_3213_:
{
lean_object* v___x_3225_; 
lean_inc_ref(v___y_3223_);
v___x_3225_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_3139_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3274_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3274_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3274_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
if (lean_obj_tag(v_a_3226_) == 1)
{
lean_object* v_val_3230_; lean_object* v_p_3231_; 
lean_del_object(v___x_3228_);
v_val_3230_ = lean_ctor_get(v_a_3226_, 0);
lean_inc(v_val_3230_);
lean_dec_ref(v_a_3226_);
v_p_3231_ = lean_ctor_get(v_val_3230_, 0);
if (lean_obj_tag(v_p_3231_) == 0)
{
lean_object* v_options_3232_; uint8_t v_hasTrace_3233_; 
v_options_3232_ = lean_ctor_get(v___y_3223_, 2);
v_hasTrace_3233_ = lean_ctor_get_uint8(v_options_3232_, sizeof(void*)*1);
if (v_hasTrace_3233_ == 0)
{
v___y_3196_ = v_val_3230_;
v___y_3197_ = v___y_3214_;
v___y_3198_ = v___y_3215_;
v___y_3199_ = v___y_3216_;
v___y_3200_ = v___y_3217_;
v___y_3201_ = v___y_3218_;
v___y_3202_ = v___y_3219_;
v___y_3203_ = v___y_3220_;
v___y_3204_ = v___y_3221_;
v___y_3205_ = v___y_3222_;
v___y_3206_ = v___y_3223_;
v___y_3207_ = v___y_3224_;
goto v___jp_3195_;
}
else
{
lean_object* v_inheritedTraceOptions_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; uint8_t v___x_3237_; 
v_inheritedTraceOptions_3234_ = lean_ctor_get(v___y_3223_, 13);
v___x_3235_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3236_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2);
v___x_3237_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3234_, v_options_3232_, v___x_3236_);
if (v___x_3237_ == 0)
{
v___y_3196_ = v_val_3230_;
v___y_3197_ = v___y_3214_;
v___y_3198_ = v___y_3215_;
v___y_3199_ = v___y_3216_;
v___y_3200_ = v___y_3217_;
v___y_3201_ = v___y_3218_;
v___y_3202_ = v___y_3219_;
v___y_3203_ = v___y_3220_;
v___y_3204_ = v___y_3221_;
v___y_3205_ = v___y_3222_;
v___y_3206_ = v___y_3223_;
v___y_3207_ = v___y_3224_;
goto v___jp_3195_;
}
else
{
lean_object* v___x_3238_; 
v___x_3238_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3230_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc(v_a_3239_);
lean_dec_ref(v___x_3238_);
v___x_3240_ = l_Lean_MessageData_ofExpr(v_a_3239_);
v___x_3241_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3235_, v___x_3240_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_dec_ref(v___x_3241_);
v___y_3196_ = v_val_3230_;
v___y_3197_ = v___y_3214_;
v___y_3198_ = v___y_3215_;
v___y_3199_ = v___y_3216_;
v___y_3200_ = v___y_3217_;
v___y_3201_ = v___y_3218_;
v___y_3202_ = v___y_3219_;
v___y_3203_ = v___y_3220_;
v___y_3204_ = v___y_3221_;
v___y_3205_ = v___y_3222_;
v___y_3206_ = v___y_3223_;
v___y_3207_ = v___y_3224_;
goto v___jp_3195_;
}
else
{
lean_dec(v_val_3230_);
return v___x_3241_;
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
lean_dec(v_val_3230_);
v_a_3242_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3238_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3238_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
}
}
else
{
lean_object* v_options_3250_; uint8_t v_hasTrace_3251_; 
lean_inc_ref(v_p_3231_);
v_options_3250_ = lean_ctor_get(v___y_3223_, 2);
v_hasTrace_3251_ = lean_ctor_get_uint8(v_options_3250_, sizeof(void*)*1);
if (v_hasTrace_3251_ == 0)
{
lean_object* v_v_3252_; 
v_v_3252_ = lean_ctor_get(v_p_3231_, 1);
lean_inc_n(v_v_3252_, 2);
lean_inc(v_val_3230_);
v___y_3153_ = v_v_3252_;
v___y_3154_ = v_val_3230_;
v___y_3155_ = v_p_3231_;
v___y_3156_ = v_v_3252_;
v___y_3157_ = v_val_3230_;
v___y_3158_ = v___y_3214_;
v___y_3159_ = v___y_3215_;
v___y_3160_ = v___y_3216_;
v___y_3161_ = v___y_3217_;
v___y_3162_ = v___y_3218_;
v___y_3163_ = v___y_3219_;
v___y_3164_ = v___y_3220_;
v___y_3165_ = v___y_3221_;
v___y_3166_ = v___y_3222_;
v___y_3167_ = v___y_3223_;
v___y_3168_ = v___y_3224_;
goto v___jp_3152_;
}
else
{
lean_object* v_v_3253_; lean_object* v_inheritedTraceOptions_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; uint8_t v___x_3257_; 
v_v_3253_ = lean_ctor_get(v_p_3231_, 1);
lean_inc(v_v_3253_);
v_inheritedTraceOptions_3254_ = lean_ctor_get(v___y_3223_, 13);
v___x_3255_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3256_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_3257_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3254_, v_options_3250_, v___x_3256_);
if (v___x_3257_ == 0)
{
lean_inc(v_val_3230_);
lean_inc(v_v_3253_);
v___y_3153_ = v_v_3253_;
v___y_3154_ = v_val_3230_;
v___y_3155_ = v_p_3231_;
v___y_3156_ = v_v_3253_;
v___y_3157_ = v_val_3230_;
v___y_3158_ = v___y_3214_;
v___y_3159_ = v___y_3215_;
v___y_3160_ = v___y_3216_;
v___y_3161_ = v___y_3217_;
v___y_3162_ = v___y_3218_;
v___y_3163_ = v___y_3219_;
v___y_3164_ = v___y_3220_;
v___y_3165_ = v___y_3221_;
v___y_3166_ = v___y_3222_;
v___y_3167_ = v___y_3223_;
v___y_3168_ = v___y_3224_;
goto v___jp_3152_;
}
else
{
lean_object* v___x_3258_; 
v___x_3258_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3230_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_a_3259_);
lean_dec_ref(v___x_3258_);
v___x_3260_ = l_Lean_MessageData_ofExpr(v_a_3259_);
v___x_3261_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3255_, v___x_3260_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_dec_ref(v___x_3261_);
lean_inc(v_val_3230_);
lean_inc(v_v_3253_);
v___y_3153_ = v_v_3253_;
v___y_3154_ = v_val_3230_;
v___y_3155_ = v_p_3231_;
v___y_3156_ = v_v_3253_;
v___y_3157_ = v_val_3230_;
v___y_3158_ = v___y_3214_;
v___y_3159_ = v___y_3215_;
v___y_3160_ = v___y_3216_;
v___y_3161_ = v___y_3217_;
v___y_3162_ = v___y_3218_;
v___y_3163_ = v___y_3219_;
v___y_3164_ = v___y_3220_;
v___y_3165_ = v___y_3221_;
v___y_3166_ = v___y_3222_;
v___y_3167_ = v___y_3223_;
v___y_3168_ = v___y_3224_;
goto v___jp_3152_;
}
else
{
lean_dec(v_v_3253_);
lean_dec_ref(v_p_3231_);
lean_dec(v_val_3230_);
return v___x_3261_;
}
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_dec(v_v_3253_);
lean_dec_ref(v_p_3231_);
lean_dec(v_val_3230_);
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
}
}
else
{
lean_object* v___x_3270_; lean_object* v___x_3272_; 
lean_dec(v_a_3226_);
v___x_3270_ = lean_box(0);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3270_);
v___x_3272_ = v___x_3228_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3270_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
v_a_3275_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3277_ = v___x_3225_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3225_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3280_; 
if (v_isShared_3278_ == 0)
{
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___boxed(lean_object* v_c_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_c_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
lean_dec(v_a_3309_);
lean_dec_ref(v_a_3308_);
lean_dec(v_a_3307_);
lean_dec_ref(v_a_3306_);
lean_dec(v_a_3305_);
lean_dec_ref(v_a_3304_);
lean_dec(v_a_3303_);
lean_dec_ref(v_a_3302_);
lean_dec(v_a_3301_);
lean_dec(v_a_3300_);
lean_dec(v_a_3299_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_3312_, lean_object* v_as_3313_, size_t v_sz_3314_, size_t v_i_3315_, lean_object* v_b_3316_){
_start:
{
uint8_t v___x_3317_; 
v___x_3317_ = lean_usize_dec_lt(v_i_3315_, v_sz_3314_);
if (v___x_3317_ == 0)
{
return v_b_3316_;
}
else
{
lean_object* v_snd_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3359_; 
v_snd_3318_ = lean_ctor_get(v_b_3316_, 1);
v_isSharedCheck_3359_ = !lean_is_exclusive(v_b_3316_);
if (v_isSharedCheck_3359_ == 0)
{
lean_object* v_unused_3360_; 
v_unused_3360_ = lean_ctor_get(v_b_3316_, 0);
lean_dec(v_unused_3360_);
v___x_3320_ = v_b_3316_;
v_isShared_3321_ = v_isSharedCheck_3359_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_snd_3318_);
lean_dec(v_b_3316_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3359_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v_fst_3322_; lean_object* v_snd_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3358_; 
v_fst_3322_ = lean_ctor_get(v_snd_3318_, 0);
v_snd_3323_ = lean_ctor_get(v_snd_3318_, 1);
v_isSharedCheck_3358_ = !lean_is_exclusive(v_snd_3318_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3325_ = v_snd_3318_;
v_isShared_3326_ = v_isSharedCheck_3358_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_snd_3323_);
lean_inc(v_fst_3322_);
lean_dec(v_snd_3318_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3358_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v_a_3327_; lean_object* v_p_3328_; lean_object* v___x_3329_; lean_object* v_a_3331_; lean_object* v_b_3338_; lean_object* v___x_3339_; uint8_t v___x_3340_; 
v_a_3327_ = lean_array_uget(v_as_3313_, v_i_3315_);
v_p_3328_ = lean_ctor_get(v_a_3327_, 0);
v___x_3329_ = lean_box(0);
v_b_3338_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3328_, v_x_3312_);
v___x_3339_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3340_ = lean_int_dec_eq(v_b_3338_, v___x_3339_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3342_; 
lean_inc(v_a_3327_);
if (v_isShared_3321_ == 0)
{
lean_ctor_set(v___x_3320_, 1, v_a_3327_);
lean_ctor_set(v___x_3320_, 0, v_b_3338_);
v___x_3342_ = v___x_3320_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_b_3338_);
lean_ctor_set(v_reuseFailAlloc_3353_, 1, v_a_3327_);
v___x_3342_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3350_; 
v_isSharedCheck_3350_ = !lean_is_exclusive(v_a_3327_);
if (v_isSharedCheck_3350_ == 0)
{
lean_object* v_unused_3351_; lean_object* v_unused_3352_; 
v_unused_3351_ = lean_ctor_get(v_a_3327_, 1);
lean_dec(v_unused_3351_);
v_unused_3352_ = lean_ctor_get(v_a_3327_, 0);
lean_dec(v_unused_3352_);
v___x_3344_ = v_a_3327_;
v_isShared_3345_ = v_isSharedCheck_3350_;
goto v_resetjp_3343_;
}
else
{
lean_dec(v_a_3327_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3350_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v_todo_3346_; lean_object* v___x_3348_; 
v_todo_3346_ = lean_array_push(v_snd_3323_, v___x_3342_);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 1, v_todo_3346_);
lean_ctor_set(v___x_3344_, 0, v_fst_3322_);
v___x_3348_ = v___x_3344_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_fst_3322_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_todo_3346_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
v_a_3331_ = v___x_3348_;
goto v___jp_3330_;
}
}
}
}
else
{
lean_object* v_cs_x27_3354_; lean_object* v___x_3356_; 
lean_dec(v_b_3338_);
v_cs_x27_3354_ = l_Lean_PersistentArray_push___redArg(v_fst_3322_, v_a_3327_);
if (v_isShared_3321_ == 0)
{
lean_ctor_set(v___x_3320_, 1, v_snd_3323_);
lean_ctor_set(v___x_3320_, 0, v_cs_x27_3354_);
v___x_3356_ = v___x_3320_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_cs_x27_3354_);
lean_ctor_set(v_reuseFailAlloc_3357_, 1, v_snd_3323_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
v_a_3331_ = v___x_3356_;
goto v___jp_3330_;
}
}
v___jp_3330_:
{
lean_object* v___x_3333_; 
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 1, v_a_3331_);
lean_ctor_set(v___x_3325_, 0, v___x_3329_);
v___x_3333_ = v___x_3325_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3329_);
lean_ctor_set(v_reuseFailAlloc_3337_, 1, v_a_3331_);
v___x_3333_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
size_t v___x_3334_; size_t v___x_3335_; 
v___x_3334_ = ((size_t)1ULL);
v___x_3335_ = lean_usize_add(v_i_3315_, v___x_3334_);
v_i_3315_ = v___x_3335_;
v_b_3316_ = v___x_3333_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_3361_, lean_object* v_as_3362_, lean_object* v_sz_3363_, lean_object* v_i_3364_, lean_object* v_b_3365_){
_start:
{
size_t v_sz_boxed_3366_; size_t v_i_boxed_3367_; lean_object* v_res_3368_; 
v_sz_boxed_3366_ = lean_unbox_usize(v_sz_3363_);
lean_dec(v_sz_3363_);
v_i_boxed_3367_ = lean_unbox_usize(v_i_3364_);
lean_dec(v_i_3364_);
v_res_3368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3361_, v_as_3362_, v_sz_boxed_3366_, v_i_boxed_3367_, v_b_3365_);
lean_dec_ref(v_as_3362_);
lean_dec(v_x_3361_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(lean_object* v_x_3369_, lean_object* v_as_3370_, size_t v_sz_3371_, size_t v_i_3372_, lean_object* v_b_3373_){
_start:
{
uint8_t v___x_3374_; 
v___x_3374_ = lean_usize_dec_lt(v_i_3372_, v_sz_3371_);
if (v___x_3374_ == 0)
{
return v_b_3373_;
}
else
{
lean_object* v_snd_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3416_; 
v_snd_3375_ = lean_ctor_get(v_b_3373_, 1);
v_isSharedCheck_3416_ = !lean_is_exclusive(v_b_3373_);
if (v_isSharedCheck_3416_ == 0)
{
lean_object* v_unused_3417_; 
v_unused_3417_ = lean_ctor_get(v_b_3373_, 0);
lean_dec(v_unused_3417_);
v___x_3377_ = v_b_3373_;
v_isShared_3378_ = v_isSharedCheck_3416_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_snd_3375_);
lean_dec(v_b_3373_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3416_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v_fst_3379_; lean_object* v_snd_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3415_; 
v_fst_3379_ = lean_ctor_get(v_snd_3375_, 0);
v_snd_3380_ = lean_ctor_get(v_snd_3375_, 1);
v_isSharedCheck_3415_ = !lean_is_exclusive(v_snd_3375_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3382_ = v_snd_3375_;
v_isShared_3383_ = v_isSharedCheck_3415_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_snd_3380_);
lean_inc(v_fst_3379_);
lean_dec(v_snd_3375_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3415_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v_a_3384_; lean_object* v_p_3385_; lean_object* v___x_3386_; lean_object* v_a_3388_; lean_object* v_b_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v_a_3384_ = lean_array_uget(v_as_3370_, v_i_3372_);
v_p_3385_ = lean_ctor_get(v_a_3384_, 0);
v___x_3386_ = lean_box(0);
v_b_3395_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3385_, v_x_3369_);
v___x_3396_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3397_ = lean_int_dec_eq(v_b_3395_, v___x_3396_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3399_; 
lean_inc(v_a_3384_);
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 1, v_a_3384_);
lean_ctor_set(v___x_3377_, 0, v_b_3395_);
v___x_3399_ = v___x_3377_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_b_3395_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v_a_3384_);
v___x_3399_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3407_; 
v_isSharedCheck_3407_ = !lean_is_exclusive(v_a_3384_);
if (v_isSharedCheck_3407_ == 0)
{
lean_object* v_unused_3408_; lean_object* v_unused_3409_; 
v_unused_3408_ = lean_ctor_get(v_a_3384_, 1);
lean_dec(v_unused_3408_);
v_unused_3409_ = lean_ctor_get(v_a_3384_, 0);
lean_dec(v_unused_3409_);
v___x_3401_ = v_a_3384_;
v_isShared_3402_ = v_isSharedCheck_3407_;
goto v_resetjp_3400_;
}
else
{
lean_dec(v_a_3384_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3407_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v_todo_3403_; lean_object* v___x_3405_; 
v_todo_3403_ = lean_array_push(v_snd_3380_, v___x_3399_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 1, v_todo_3403_);
lean_ctor_set(v___x_3401_, 0, v_fst_3379_);
v___x_3405_ = v___x_3401_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_fst_3379_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v_todo_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
v_a_3388_ = v___x_3405_;
goto v___jp_3387_;
}
}
}
}
else
{
lean_object* v_cs_x27_3411_; lean_object* v___x_3413_; 
lean_dec(v_b_3395_);
v_cs_x27_3411_ = l_Lean_PersistentArray_push___redArg(v_fst_3379_, v_a_3384_);
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 1, v_snd_3380_);
lean_ctor_set(v___x_3377_, 0, v_cs_x27_3411_);
v___x_3413_ = v___x_3377_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_cs_x27_3411_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_snd_3380_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
v_a_3388_ = v___x_3413_;
goto v___jp_3387_;
}
}
v___jp_3387_:
{
lean_object* v___x_3390_; 
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 1, v_a_3388_);
lean_ctor_set(v___x_3382_, 0, v___x_3386_);
v___x_3390_ = v___x_3382_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3386_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v_a_3388_);
v___x_3390_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
size_t v___x_3391_; size_t v___x_3392_; lean_object* v___x_3393_; 
v___x_3391_ = ((size_t)1ULL);
v___x_3392_ = lean_usize_add(v_i_3372_, v___x_3391_);
v___x_3393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3369_, v_as_3370_, v_sz_3371_, v___x_3392_, v___x_3390_);
return v___x_3393_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_3418_, lean_object* v_as_3419_, lean_object* v_sz_3420_, lean_object* v_i_3421_, lean_object* v_b_3422_){
_start:
{
size_t v_sz_boxed_3423_; size_t v_i_boxed_3424_; lean_object* v_res_3425_; 
v_sz_boxed_3423_ = lean_unbox_usize(v_sz_3420_);
lean_dec(v_sz_3420_);
v_i_boxed_3424_ = lean_unbox_usize(v_i_3421_);
lean_dec(v_i_3421_);
v_res_3425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3418_, v_as_3419_, v_sz_boxed_3423_, v_i_boxed_3424_, v_b_3422_);
lean_dec_ref(v_as_3419_);
lean_dec(v_x_3418_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_3426_, lean_object* v_as_3427_, size_t v_sz_3428_, size_t v_i_3429_, lean_object* v_b_3430_){
_start:
{
uint8_t v___x_3431_; 
v___x_3431_ = lean_usize_dec_lt(v_i_3429_, v_sz_3428_);
if (v___x_3431_ == 0)
{
return v_b_3430_;
}
else
{
lean_object* v_snd_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3473_; 
v_snd_3432_ = lean_ctor_get(v_b_3430_, 1);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_b_3430_);
if (v_isSharedCheck_3473_ == 0)
{
lean_object* v_unused_3474_; 
v_unused_3474_ = lean_ctor_get(v_b_3430_, 0);
lean_dec(v_unused_3474_);
v___x_3434_ = v_b_3430_;
v_isShared_3435_ = v_isSharedCheck_3473_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_snd_3432_);
lean_dec(v_b_3430_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3473_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v_fst_3436_; lean_object* v_snd_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3472_; 
v_fst_3436_ = lean_ctor_get(v_snd_3432_, 0);
v_snd_3437_ = lean_ctor_get(v_snd_3432_, 1);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_snd_3432_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3439_ = v_snd_3432_;
v_isShared_3440_ = v_isSharedCheck_3472_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_snd_3437_);
lean_inc(v_fst_3436_);
lean_dec(v_snd_3432_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3472_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v_a_3441_; lean_object* v_p_3442_; lean_object* v___x_3443_; lean_object* v_a_3445_; lean_object* v_b_3452_; lean_object* v___x_3453_; uint8_t v___x_3454_; 
v_a_3441_ = lean_array_uget(v_as_3427_, v_i_3429_);
v_p_3442_ = lean_ctor_get(v_a_3441_, 0);
v___x_3443_ = lean_box(0);
v_b_3452_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3442_, v_x_3426_);
v___x_3453_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3454_ = lean_int_dec_eq(v_b_3452_, v___x_3453_);
if (v___x_3454_ == 0)
{
lean_object* v___x_3456_; 
lean_inc(v_a_3441_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 1, v_a_3441_);
lean_ctor_set(v___x_3434_, 0, v_b_3452_);
v___x_3456_ = v___x_3434_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_b_3452_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_a_3441_);
v___x_3456_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3464_; 
v_isSharedCheck_3464_ = !lean_is_exclusive(v_a_3441_);
if (v_isSharedCheck_3464_ == 0)
{
lean_object* v_unused_3465_; lean_object* v_unused_3466_; 
v_unused_3465_ = lean_ctor_get(v_a_3441_, 1);
lean_dec(v_unused_3465_);
v_unused_3466_ = lean_ctor_get(v_a_3441_, 0);
lean_dec(v_unused_3466_);
v___x_3458_ = v_a_3441_;
v_isShared_3459_ = v_isSharedCheck_3464_;
goto v_resetjp_3457_;
}
else
{
lean_dec(v_a_3441_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3464_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v_todo_3460_; lean_object* v___x_3462_; 
v_todo_3460_ = lean_array_push(v_snd_3437_, v___x_3456_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 1, v_todo_3460_);
lean_ctor_set(v___x_3458_, 0, v_fst_3436_);
v___x_3462_ = v___x_3458_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_fst_3436_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_todo_3460_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
v_a_3445_ = v___x_3462_;
goto v___jp_3444_;
}
}
}
}
else
{
lean_object* v_cs_x27_3468_; lean_object* v___x_3470_; 
lean_dec(v_b_3452_);
v_cs_x27_3468_ = l_Lean_PersistentArray_push___redArg(v_fst_3436_, v_a_3441_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 1, v_snd_3437_);
lean_ctor_set(v___x_3434_, 0, v_cs_x27_3468_);
v___x_3470_ = v___x_3434_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_cs_x27_3468_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_snd_3437_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
v_a_3445_ = v___x_3470_;
goto v___jp_3444_;
}
}
v___jp_3444_:
{
lean_object* v___x_3447_; 
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 1, v_a_3445_);
lean_ctor_set(v___x_3439_, 0, v___x_3443_);
v___x_3447_ = v___x_3439_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3443_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_a_3445_);
v___x_3447_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
size_t v___x_3448_; size_t v___x_3449_; 
v___x_3448_ = ((size_t)1ULL);
v___x_3449_ = lean_usize_add(v_i_3429_, v___x_3448_);
v_i_3429_ = v___x_3449_;
v_b_3430_ = v___x_3447_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3475_, lean_object* v_as_3476_, lean_object* v_sz_3477_, lean_object* v_i_3478_, lean_object* v_b_3479_){
_start:
{
size_t v_sz_boxed_3480_; size_t v_i_boxed_3481_; lean_object* v_res_3482_; 
v_sz_boxed_3480_ = lean_unbox_usize(v_sz_3477_);
lean_dec(v_sz_3477_);
v_i_boxed_3481_ = lean_unbox_usize(v_i_3478_);
lean_dec(v_i_3478_);
v_res_3482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3475_, v_as_3476_, v_sz_boxed_3480_, v_i_boxed_3481_, v_b_3479_);
lean_dec_ref(v_as_3476_);
lean_dec(v_x_3475_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_3483_, lean_object* v_as_3484_, size_t v_sz_3485_, size_t v_i_3486_, lean_object* v_b_3487_){
_start:
{
uint8_t v___x_3488_; 
v___x_3488_ = lean_usize_dec_lt(v_i_3486_, v_sz_3485_);
if (v___x_3488_ == 0)
{
return v_b_3487_;
}
else
{
lean_object* v_snd_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3530_; 
v_snd_3489_ = lean_ctor_get(v_b_3487_, 1);
v_isSharedCheck_3530_ = !lean_is_exclusive(v_b_3487_);
if (v_isSharedCheck_3530_ == 0)
{
lean_object* v_unused_3531_; 
v_unused_3531_ = lean_ctor_get(v_b_3487_, 0);
lean_dec(v_unused_3531_);
v___x_3491_ = v_b_3487_;
v_isShared_3492_ = v_isSharedCheck_3530_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_snd_3489_);
lean_dec(v_b_3487_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3530_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v_fst_3493_; lean_object* v_snd_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3529_; 
v_fst_3493_ = lean_ctor_get(v_snd_3489_, 0);
v_snd_3494_ = lean_ctor_get(v_snd_3489_, 1);
v_isSharedCheck_3529_ = !lean_is_exclusive(v_snd_3489_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3496_ = v_snd_3489_;
v_isShared_3497_ = v_isSharedCheck_3529_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_snd_3494_);
lean_inc(v_fst_3493_);
lean_dec(v_snd_3489_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3529_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v_a_3498_; lean_object* v_p_3499_; lean_object* v___x_3500_; lean_object* v_a_3502_; lean_object* v_b_3509_; lean_object* v___x_3510_; uint8_t v___x_3511_; 
v_a_3498_ = lean_array_uget(v_as_3484_, v_i_3486_);
v_p_3499_ = lean_ctor_get(v_a_3498_, 0);
v___x_3500_ = lean_box(0);
v_b_3509_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3499_, v_x_3483_);
v___x_3510_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3511_ = lean_int_dec_eq(v_b_3509_, v___x_3510_);
if (v___x_3511_ == 0)
{
lean_object* v___x_3513_; 
lean_inc(v_a_3498_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 1, v_a_3498_);
lean_ctor_set(v___x_3491_, 0, v_b_3509_);
v___x_3513_ = v___x_3491_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_b_3509_);
lean_ctor_set(v_reuseFailAlloc_3524_, 1, v_a_3498_);
v___x_3513_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3521_; 
v_isSharedCheck_3521_ = !lean_is_exclusive(v_a_3498_);
if (v_isSharedCheck_3521_ == 0)
{
lean_object* v_unused_3522_; lean_object* v_unused_3523_; 
v_unused_3522_ = lean_ctor_get(v_a_3498_, 1);
lean_dec(v_unused_3522_);
v_unused_3523_ = lean_ctor_get(v_a_3498_, 0);
lean_dec(v_unused_3523_);
v___x_3515_ = v_a_3498_;
v_isShared_3516_ = v_isSharedCheck_3521_;
goto v_resetjp_3514_;
}
else
{
lean_dec(v_a_3498_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3521_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v_todo_3517_; lean_object* v___x_3519_; 
v_todo_3517_ = lean_array_push(v_snd_3494_, v___x_3513_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 1, v_todo_3517_);
lean_ctor_set(v___x_3515_, 0, v_fst_3493_);
v___x_3519_ = v___x_3515_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_fst_3493_);
lean_ctor_set(v_reuseFailAlloc_3520_, 1, v_todo_3517_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
v_a_3502_ = v___x_3519_;
goto v___jp_3501_;
}
}
}
}
else
{
lean_object* v_cs_x27_3525_; lean_object* v___x_3527_; 
lean_dec(v_b_3509_);
v_cs_x27_3525_ = l_Lean_PersistentArray_push___redArg(v_fst_3493_, v_a_3498_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 1, v_snd_3494_);
lean_ctor_set(v___x_3491_, 0, v_cs_x27_3525_);
v___x_3527_ = v___x_3491_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_cs_x27_3525_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v_snd_3494_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
v_a_3502_ = v___x_3527_;
goto v___jp_3501_;
}
}
v___jp_3501_:
{
lean_object* v___x_3504_; 
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 1, v_a_3502_);
lean_ctor_set(v___x_3496_, 0, v___x_3500_);
v___x_3504_ = v___x_3496_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3500_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v_a_3502_);
v___x_3504_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
size_t v___x_3505_; size_t v___x_3506_; lean_object* v___x_3507_; 
v___x_3505_ = ((size_t)1ULL);
v___x_3506_ = lean_usize_add(v_i_3486_, v___x_3505_);
v___x_3507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3483_, v_as_3484_, v_sz_3485_, v___x_3506_, v___x_3504_);
return v___x_3507_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_3532_, lean_object* v_as_3533_, lean_object* v_sz_3534_, lean_object* v_i_3535_, lean_object* v_b_3536_){
_start:
{
size_t v_sz_boxed_3537_; size_t v_i_boxed_3538_; lean_object* v_res_3539_; 
v_sz_boxed_3537_ = lean_unbox_usize(v_sz_3534_);
lean_dec(v_sz_3534_);
v_i_boxed_3538_ = lean_unbox_usize(v_i_3535_);
lean_dec(v_i_3535_);
v_res_3539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3532_, v_as_3533_, v_sz_boxed_3537_, v_i_boxed_3538_, v_b_3536_);
lean_dec_ref(v_as_3533_);
lean_dec(v_x_3532_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(lean_object* v_init_3540_, lean_object* v_x_3541_, lean_object* v_n_3542_, lean_object* v_b_3543_){
_start:
{
if (lean_obj_tag(v_n_3542_) == 0)
{
lean_object* v_cs_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; size_t v_sz_3547_; size_t v___x_3548_; lean_object* v___x_3549_; lean_object* v_fst_3550_; 
v_cs_3544_ = lean_ctor_get(v_n_3542_, 0);
v___x_3545_ = lean_box(0);
v___x_3546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
lean_ctor_set(v___x_3546_, 1, v_b_3543_);
v_sz_3547_ = lean_array_size(v_cs_3544_);
v___x_3548_ = ((size_t)0ULL);
v___x_3549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3540_, v_x_3541_, v_cs_3544_, v_sz_3547_, v___x_3548_, v___x_3546_);
v_fst_3550_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_fst_3550_);
if (lean_obj_tag(v_fst_3550_) == 0)
{
lean_object* v_snd_3551_; lean_object* v___x_3552_; 
v_snd_3551_ = lean_ctor_get(v___x_3549_, 1);
lean_inc(v_snd_3551_);
lean_dec_ref(v___x_3549_);
v___x_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3552_, 0, v_snd_3551_);
return v___x_3552_;
}
else
{
lean_object* v_val_3553_; 
lean_dec_ref(v___x_3549_);
v_val_3553_ = lean_ctor_get(v_fst_3550_, 0);
lean_inc(v_val_3553_);
lean_dec_ref(v_fst_3550_);
return v_val_3553_;
}
}
else
{
lean_object* v_vs_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; size_t v_sz_3557_; size_t v___x_3558_; lean_object* v___x_3559_; lean_object* v_fst_3560_; 
v_vs_3554_ = lean_ctor_get(v_n_3542_, 0);
v___x_3555_ = lean_box(0);
v___x_3556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3555_);
lean_ctor_set(v___x_3556_, 1, v_b_3543_);
v_sz_3557_ = lean_array_size(v_vs_3554_);
v___x_3558_ = ((size_t)0ULL);
v___x_3559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3541_, v_vs_3554_, v_sz_3557_, v___x_3558_, v___x_3556_);
v_fst_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_fst_3560_);
if (lean_obj_tag(v_fst_3560_) == 0)
{
lean_object* v_snd_3561_; lean_object* v___x_3562_; 
v_snd_3561_ = lean_ctor_get(v___x_3559_, 1);
lean_inc(v_snd_3561_);
lean_dec_ref(v___x_3559_);
v___x_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3562_, 0, v_snd_3561_);
return v___x_3562_;
}
else
{
lean_object* v_val_3563_; 
lean_dec_ref(v___x_3559_);
v_val_3563_ = lean_ctor_get(v_fst_3560_, 0);
lean_inc(v_val_3563_);
lean_dec_ref(v_fst_3560_);
return v_val_3563_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3564_, lean_object* v_x_3565_, lean_object* v_as_3566_, size_t v_sz_3567_, size_t v_i_3568_, lean_object* v_b_3569_){
_start:
{
uint8_t v___x_3570_; 
v___x_3570_ = lean_usize_dec_lt(v_i_3568_, v_sz_3567_);
if (v___x_3570_ == 0)
{
return v_b_3569_;
}
else
{
lean_object* v_snd_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3589_; 
v_snd_3571_ = lean_ctor_get(v_b_3569_, 1);
v_isSharedCheck_3589_ = !lean_is_exclusive(v_b_3569_);
if (v_isSharedCheck_3589_ == 0)
{
lean_object* v_unused_3590_; 
v_unused_3590_ = lean_ctor_get(v_b_3569_, 0);
lean_dec(v_unused_3590_);
v___x_3573_ = v_b_3569_;
v_isShared_3574_ = v_isSharedCheck_3589_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_snd_3571_);
lean_dec(v_b_3569_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3589_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v_a_3575_; lean_object* v___x_3576_; 
v_a_3575_ = lean_array_uget_borrowed(v_as_3566_, v_i_3568_);
lean_inc(v_snd_3571_);
v___x_3576_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3564_, v_x_3565_, v_a_3575_, v_snd_3571_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v___x_3577_; lean_object* v___x_3579_; 
v___x_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3576_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v___x_3577_);
v___x_3579_ = v___x_3573_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3577_);
lean_ctor_set(v_reuseFailAlloc_3580_, 1, v_snd_3571_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3582_; lean_object* v___x_3584_; 
lean_dec(v_snd_3571_);
v_a_3581_ = lean_ctor_get(v___x_3576_, 0);
lean_inc(v_a_3581_);
lean_dec_ref(v___x_3576_);
v___x_3582_ = lean_box(0);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 1, v_a_3581_);
lean_ctor_set(v___x_3573_, 0, v___x_3582_);
v___x_3584_ = v___x_3573_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_a_3581_);
v___x_3584_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
size_t v___x_3585_; size_t v___x_3586_; 
v___x_3585_ = ((size_t)1ULL);
v___x_3586_ = lean_usize_add(v_i_3568_, v___x_3585_);
v_i_3568_ = v___x_3586_;
v_b_3569_ = v___x_3584_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3591_, lean_object* v_x_3592_, lean_object* v_as_3593_, lean_object* v_sz_3594_, lean_object* v_i_3595_, lean_object* v_b_3596_){
_start:
{
size_t v_sz_boxed_3597_; size_t v_i_boxed_3598_; lean_object* v_res_3599_; 
v_sz_boxed_3597_ = lean_unbox_usize(v_sz_3594_);
lean_dec(v_sz_3594_);
v_i_boxed_3598_ = lean_unbox_usize(v_i_3595_);
lean_dec(v_i_3595_);
v_res_3599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3591_, v_x_3592_, v_as_3593_, v_sz_boxed_3597_, v_i_boxed_3598_, v_b_3596_);
lean_dec_ref(v_as_3593_);
lean_dec(v_x_3592_);
lean_dec_ref(v_init_3591_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3600_, lean_object* v_x_3601_, lean_object* v_n_3602_, lean_object* v_b_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3600_, v_x_3601_, v_n_3602_, v_b_3603_);
lean_dec_ref(v_n_3602_);
lean_dec(v_x_3601_);
lean_dec_ref(v_init_3600_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object* v_x_3605_, lean_object* v_t_3606_, lean_object* v_init_3607_){
_start:
{
lean_object* v_root_3608_; lean_object* v_tail_3609_; lean_object* v___x_3610_; 
v_root_3608_ = lean_ctor_get(v_t_3606_, 0);
v_tail_3609_ = lean_ctor_get(v_t_3606_, 1);
lean_inc_ref(v_init_3607_);
v___x_3610_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3607_, v_x_3605_, v_root_3608_, v_init_3607_);
lean_dec_ref(v_init_3607_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref(v___x_3610_);
return v_a_3611_;
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; size_t v_sz_3615_; size_t v___x_3616_; lean_object* v___x_3617_; lean_object* v_fst_3618_; 
v_a_3612_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3612_);
lean_dec_ref(v___x_3610_);
v___x_3613_ = lean_box(0);
v___x_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3613_);
lean_ctor_set(v___x_3614_, 1, v_a_3612_);
v_sz_3615_ = lean_array_size(v_tail_3609_);
v___x_3616_ = ((size_t)0ULL);
v___x_3617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3605_, v_tail_3609_, v_sz_3615_, v___x_3616_, v___x_3614_);
v_fst_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_fst_3618_);
if (lean_obj_tag(v_fst_3618_) == 0)
{
lean_object* v_snd_3619_; 
v_snd_3619_ = lean_ctor_get(v___x_3617_, 1);
lean_inc(v_snd_3619_);
lean_dec_ref(v___x_3617_);
return v_snd_3619_;
}
else
{
lean_object* v_val_3620_; 
lean_dec_ref(v___x_3617_);
v_val_3620_ = lean_ctor_get(v_fst_3618_, 0);
lean_inc(v_val_3620_);
lean_dec_ref(v_fst_3618_);
return v_val_3620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object* v_x_3621_, lean_object* v_t_3622_, lean_object* v_init_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3621_, v_t_3622_, v_init_3623_);
lean_dec_ref(v_t_3622_);
lean_dec(v_x_3621_);
return v_res_3624_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3625_ = lean_unsigned_to_nat(32u);
v___x_3626_ = lean_mk_empty_array_with_capacity(v___x_3625_);
v___x_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3626_);
return v___x_3627_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1(void){
_start:
{
size_t v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v_cs_x27_3633_; 
v___x_3628_ = ((size_t)5ULL);
v___x_3629_ = lean_unsigned_to_nat(0u);
v___x_3630_ = lean_unsigned_to_nat(32u);
v___x_3631_ = lean_mk_empty_array_with_capacity(v___x_3630_);
v___x_3632_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0);
v_cs_x27_3633_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_3633_, 0, v___x_3632_);
lean_ctor_set(v_cs_x27_3633_, 1, v___x_3631_);
lean_ctor_set(v_cs_x27_3633_, 2, v___x_3629_);
lean_ctor_set(v_cs_x27_3633_, 3, v___x_3629_);
lean_ctor_set_usize(v_cs_x27_3633_, 4, v___x_3628_);
return v_cs_x27_3633_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_3636_; lean_object* v_cs_x27_3637_; lean_object* v___x_3638_; 
v_todo_3636_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2));
v_cs_x27_3637_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1);
v___x_3638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3638_, 0, v_cs_x27_3637_);
lean_ctor_set(v___x_3638_, 1, v_todo_3636_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object* v_x_3639_, lean_object* v_cs_3640_){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v_fst_3643_; lean_object* v_snd_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
v___x_3641_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3);
v___x_3642_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3639_, v_cs_3640_, v___x_3641_);
v_fst_3643_ = lean_ctor_get(v___x_3642_, 0);
v_snd_3644_ = lean_ctor_get(v___x_3642_, 1);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3642_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_snd_3644_);
lean_inc(v_fst_3643_);
lean_dec(v___x_3642_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_fst_3643_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_snd_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object* v_x_3652_, lean_object* v_cs_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3652_, v_cs_3653_);
lean_dec_ref(v_cs_3653_);
lean_dec(v_x_3652_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object* v_x_3655_, lean_object* v_cs_3656_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3655_, v_cs_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object* v_x_3658_, lean_object* v_cs_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(v_x_3658_, v_cs_3659_);
lean_dec_ref(v_cs_3659_);
lean_dec(v_x_3658_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(lean_object* v_a_3661_, lean_object* v_y_3662_, lean_object* v_fst_3663_, lean_object* v_s_3664_){
_start:
{
lean_object* v_structs_3665_; lean_object* v_typeIdOf_3666_; lean_object* v_exprToStructId_3667_; lean_object* v_exprToStructIdEntries_3668_; lean_object* v_forbiddenNatModules_3669_; lean_object* v_natStructs_3670_; lean_object* v_natTypeIdOf_3671_; lean_object* v_exprToNatStructId_3672_; lean_object* v___x_3673_; uint8_t v___x_3674_; 
v_structs_3665_ = lean_ctor_get(v_s_3664_, 0);
v_typeIdOf_3666_ = lean_ctor_get(v_s_3664_, 1);
v_exprToStructId_3667_ = lean_ctor_get(v_s_3664_, 2);
v_exprToStructIdEntries_3668_ = lean_ctor_get(v_s_3664_, 3);
v_forbiddenNatModules_3669_ = lean_ctor_get(v_s_3664_, 4);
v_natStructs_3670_ = lean_ctor_get(v_s_3664_, 5);
v_natTypeIdOf_3671_ = lean_ctor_get(v_s_3664_, 6);
v_exprToNatStructId_3672_ = lean_ctor_get(v_s_3664_, 7);
v___x_3673_ = lean_array_get_size(v_structs_3665_);
v___x_3674_ = lean_nat_dec_lt(v_a_3661_, v___x_3673_);
if (v___x_3674_ == 0)
{
lean_dec_ref(v_fst_3663_);
return v_s_3664_;
}
else
{
lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3736_; 
lean_inc_ref(v_exprToNatStructId_3672_);
lean_inc_ref(v_natTypeIdOf_3671_);
lean_inc_ref(v_natStructs_3670_);
lean_inc_ref(v_forbiddenNatModules_3669_);
lean_inc_ref(v_exprToStructIdEntries_3668_);
lean_inc_ref(v_exprToStructId_3667_);
lean_inc_ref(v_typeIdOf_3666_);
lean_inc_ref(v_structs_3665_);
v_isSharedCheck_3736_ = !lean_is_exclusive(v_s_3664_);
if (v_isSharedCheck_3736_ == 0)
{
lean_object* v_unused_3737_; lean_object* v_unused_3738_; lean_object* v_unused_3739_; lean_object* v_unused_3740_; lean_object* v_unused_3741_; lean_object* v_unused_3742_; lean_object* v_unused_3743_; lean_object* v_unused_3744_; 
v_unused_3737_ = lean_ctor_get(v_s_3664_, 7);
lean_dec(v_unused_3737_);
v_unused_3738_ = lean_ctor_get(v_s_3664_, 6);
lean_dec(v_unused_3738_);
v_unused_3739_ = lean_ctor_get(v_s_3664_, 5);
lean_dec(v_unused_3739_);
v_unused_3740_ = lean_ctor_get(v_s_3664_, 4);
lean_dec(v_unused_3740_);
v_unused_3741_ = lean_ctor_get(v_s_3664_, 3);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v_s_3664_, 2);
lean_dec(v_unused_3742_);
v_unused_3743_ = lean_ctor_get(v_s_3664_, 1);
lean_dec(v_unused_3743_);
v_unused_3744_ = lean_ctor_get(v_s_3664_, 0);
lean_dec(v_unused_3744_);
v___x_3676_ = v_s_3664_;
v_isShared_3677_ = v_isSharedCheck_3736_;
goto v_resetjp_3675_;
}
else
{
lean_dec(v_s_3664_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3736_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v_v_3678_; lean_object* v_id_3679_; lean_object* v_ringId_x3f_3680_; lean_object* v_type_3681_; lean_object* v_u_3682_; lean_object* v_intModuleInst_3683_; lean_object* v_leInst_x3f_3684_; lean_object* v_ltInst_x3f_3685_; lean_object* v_lawfulOrderLTInst_x3f_3686_; lean_object* v_isPreorderInst_x3f_3687_; lean_object* v_orderedAddInst_x3f_3688_; lean_object* v_isLinearInst_x3f_3689_; lean_object* v_noNatDivInst_x3f_3690_; lean_object* v_ringInst_x3f_3691_; lean_object* v_commRingInst_x3f_3692_; lean_object* v_orderedRingInst_x3f_3693_; lean_object* v_fieldInst_x3f_3694_; lean_object* v_charInst_x3f_3695_; lean_object* v_zero_3696_; lean_object* v_ofNatZero_3697_; lean_object* v_one_x3f_3698_; lean_object* v_leFn_x3f_3699_; lean_object* v_ltFn_x3f_3700_; lean_object* v_addFn_3701_; lean_object* v_zsmulFn_3702_; lean_object* v_nsmulFn_3703_; lean_object* v_zsmulFn_x3f_3704_; lean_object* v_nsmulFn_x3f_3705_; lean_object* v_homomulFn_x3f_3706_; lean_object* v_subFn_3707_; lean_object* v_negFn_3708_; lean_object* v_vars_3709_; lean_object* v_varMap_3710_; lean_object* v_lowers_3711_; lean_object* v_uppers_3712_; lean_object* v_diseqs_3713_; lean_object* v_assignment_3714_; uint8_t v_caseSplits_3715_; lean_object* v_conflict_x3f_3716_; lean_object* v_diseqSplits_3717_; lean_object* v_elimEqs_3718_; lean_object* v_elimStack_3719_; lean_object* v_occurs_3720_; lean_object* v_ignored_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3735_; 
v_v_3678_ = lean_array_fget(v_structs_3665_, v_a_3661_);
v_id_3679_ = lean_ctor_get(v_v_3678_, 0);
v_ringId_x3f_3680_ = lean_ctor_get(v_v_3678_, 1);
v_type_3681_ = lean_ctor_get(v_v_3678_, 2);
v_u_3682_ = lean_ctor_get(v_v_3678_, 3);
v_intModuleInst_3683_ = lean_ctor_get(v_v_3678_, 4);
v_leInst_x3f_3684_ = lean_ctor_get(v_v_3678_, 5);
v_ltInst_x3f_3685_ = lean_ctor_get(v_v_3678_, 6);
v_lawfulOrderLTInst_x3f_3686_ = lean_ctor_get(v_v_3678_, 7);
v_isPreorderInst_x3f_3687_ = lean_ctor_get(v_v_3678_, 8);
v_orderedAddInst_x3f_3688_ = lean_ctor_get(v_v_3678_, 9);
v_isLinearInst_x3f_3689_ = lean_ctor_get(v_v_3678_, 10);
v_noNatDivInst_x3f_3690_ = lean_ctor_get(v_v_3678_, 11);
v_ringInst_x3f_3691_ = lean_ctor_get(v_v_3678_, 12);
v_commRingInst_x3f_3692_ = lean_ctor_get(v_v_3678_, 13);
v_orderedRingInst_x3f_3693_ = lean_ctor_get(v_v_3678_, 14);
v_fieldInst_x3f_3694_ = lean_ctor_get(v_v_3678_, 15);
v_charInst_x3f_3695_ = lean_ctor_get(v_v_3678_, 16);
v_zero_3696_ = lean_ctor_get(v_v_3678_, 17);
v_ofNatZero_3697_ = lean_ctor_get(v_v_3678_, 18);
v_one_x3f_3698_ = lean_ctor_get(v_v_3678_, 19);
v_leFn_x3f_3699_ = lean_ctor_get(v_v_3678_, 20);
v_ltFn_x3f_3700_ = lean_ctor_get(v_v_3678_, 21);
v_addFn_3701_ = lean_ctor_get(v_v_3678_, 22);
v_zsmulFn_3702_ = lean_ctor_get(v_v_3678_, 23);
v_nsmulFn_3703_ = lean_ctor_get(v_v_3678_, 24);
v_zsmulFn_x3f_3704_ = lean_ctor_get(v_v_3678_, 25);
v_nsmulFn_x3f_3705_ = lean_ctor_get(v_v_3678_, 26);
v_homomulFn_x3f_3706_ = lean_ctor_get(v_v_3678_, 27);
v_subFn_3707_ = lean_ctor_get(v_v_3678_, 28);
v_negFn_3708_ = lean_ctor_get(v_v_3678_, 29);
v_vars_3709_ = lean_ctor_get(v_v_3678_, 30);
v_varMap_3710_ = lean_ctor_get(v_v_3678_, 31);
v_lowers_3711_ = lean_ctor_get(v_v_3678_, 32);
v_uppers_3712_ = lean_ctor_get(v_v_3678_, 33);
v_diseqs_3713_ = lean_ctor_get(v_v_3678_, 34);
v_assignment_3714_ = lean_ctor_get(v_v_3678_, 35);
v_caseSplits_3715_ = lean_ctor_get_uint8(v_v_3678_, sizeof(void*)*42);
v_conflict_x3f_3716_ = lean_ctor_get(v_v_3678_, 36);
v_diseqSplits_3717_ = lean_ctor_get(v_v_3678_, 37);
v_elimEqs_3718_ = lean_ctor_get(v_v_3678_, 38);
v_elimStack_3719_ = lean_ctor_get(v_v_3678_, 39);
v_occurs_3720_ = lean_ctor_get(v_v_3678_, 40);
v_ignored_3721_ = lean_ctor_get(v_v_3678_, 41);
v_isSharedCheck_3735_ = !lean_is_exclusive(v_v_3678_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3723_ = v_v_3678_;
v_isShared_3724_ = v_isSharedCheck_3735_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_ignored_3721_);
lean_inc(v_occurs_3720_);
lean_inc(v_elimStack_3719_);
lean_inc(v_elimEqs_3718_);
lean_inc(v_diseqSplits_3717_);
lean_inc(v_conflict_x3f_3716_);
lean_inc(v_assignment_3714_);
lean_inc(v_diseqs_3713_);
lean_inc(v_uppers_3712_);
lean_inc(v_lowers_3711_);
lean_inc(v_varMap_3710_);
lean_inc(v_vars_3709_);
lean_inc(v_negFn_3708_);
lean_inc(v_subFn_3707_);
lean_inc(v_homomulFn_x3f_3706_);
lean_inc(v_nsmulFn_x3f_3705_);
lean_inc(v_zsmulFn_x3f_3704_);
lean_inc(v_nsmulFn_3703_);
lean_inc(v_zsmulFn_3702_);
lean_inc(v_addFn_3701_);
lean_inc(v_ltFn_x3f_3700_);
lean_inc(v_leFn_x3f_3699_);
lean_inc(v_one_x3f_3698_);
lean_inc(v_ofNatZero_3697_);
lean_inc(v_zero_3696_);
lean_inc(v_charInst_x3f_3695_);
lean_inc(v_fieldInst_x3f_3694_);
lean_inc(v_orderedRingInst_x3f_3693_);
lean_inc(v_commRingInst_x3f_3692_);
lean_inc(v_ringInst_x3f_3691_);
lean_inc(v_noNatDivInst_x3f_3690_);
lean_inc(v_isLinearInst_x3f_3689_);
lean_inc(v_orderedAddInst_x3f_3688_);
lean_inc(v_isPreorderInst_x3f_3687_);
lean_inc(v_lawfulOrderLTInst_x3f_3686_);
lean_inc(v_ltInst_x3f_3685_);
lean_inc(v_leInst_x3f_3684_);
lean_inc(v_intModuleInst_3683_);
lean_inc(v_u_3682_);
lean_inc(v_type_3681_);
lean_inc(v_ringId_x3f_3680_);
lean_inc(v_id_3679_);
lean_dec(v_v_3678_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3735_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3725_; lean_object* v_xs_x27_3726_; lean_object* v___x_3727_; lean_object* v___x_3729_; 
v___x_3725_ = lean_box(0);
v_xs_x27_3726_ = lean_array_fset(v_structs_3665_, v_a_3661_, v___x_3725_);
v___x_3727_ = l_Lean_PersistentArray_set___redArg(v_diseqs_3713_, v_y_3662_, v_fst_3663_);
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 34, v___x_3727_);
v___x_3729_ = v___x_3723_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_id_3679_);
lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_ringId_x3f_3680_);
lean_ctor_set(v_reuseFailAlloc_3734_, 2, v_type_3681_);
lean_ctor_set(v_reuseFailAlloc_3734_, 3, v_u_3682_);
lean_ctor_set(v_reuseFailAlloc_3734_, 4, v_intModuleInst_3683_);
lean_ctor_set(v_reuseFailAlloc_3734_, 5, v_leInst_x3f_3684_);
lean_ctor_set(v_reuseFailAlloc_3734_, 6, v_ltInst_x3f_3685_);
lean_ctor_set(v_reuseFailAlloc_3734_, 7, v_lawfulOrderLTInst_x3f_3686_);
lean_ctor_set(v_reuseFailAlloc_3734_, 8, v_isPreorderInst_x3f_3687_);
lean_ctor_set(v_reuseFailAlloc_3734_, 9, v_orderedAddInst_x3f_3688_);
lean_ctor_set(v_reuseFailAlloc_3734_, 10, v_isLinearInst_x3f_3689_);
lean_ctor_set(v_reuseFailAlloc_3734_, 11, v_noNatDivInst_x3f_3690_);
lean_ctor_set(v_reuseFailAlloc_3734_, 12, v_ringInst_x3f_3691_);
lean_ctor_set(v_reuseFailAlloc_3734_, 13, v_commRingInst_x3f_3692_);
lean_ctor_set(v_reuseFailAlloc_3734_, 14, v_orderedRingInst_x3f_3693_);
lean_ctor_set(v_reuseFailAlloc_3734_, 15, v_fieldInst_x3f_3694_);
lean_ctor_set(v_reuseFailAlloc_3734_, 16, v_charInst_x3f_3695_);
lean_ctor_set(v_reuseFailAlloc_3734_, 17, v_zero_3696_);
lean_ctor_set(v_reuseFailAlloc_3734_, 18, v_ofNatZero_3697_);
lean_ctor_set(v_reuseFailAlloc_3734_, 19, v_one_x3f_3698_);
lean_ctor_set(v_reuseFailAlloc_3734_, 20, v_leFn_x3f_3699_);
lean_ctor_set(v_reuseFailAlloc_3734_, 21, v_ltFn_x3f_3700_);
lean_ctor_set(v_reuseFailAlloc_3734_, 22, v_addFn_3701_);
lean_ctor_set(v_reuseFailAlloc_3734_, 23, v_zsmulFn_3702_);
lean_ctor_set(v_reuseFailAlloc_3734_, 24, v_nsmulFn_3703_);
lean_ctor_set(v_reuseFailAlloc_3734_, 25, v_zsmulFn_x3f_3704_);
lean_ctor_set(v_reuseFailAlloc_3734_, 26, v_nsmulFn_x3f_3705_);
lean_ctor_set(v_reuseFailAlloc_3734_, 27, v_homomulFn_x3f_3706_);
lean_ctor_set(v_reuseFailAlloc_3734_, 28, v_subFn_3707_);
lean_ctor_set(v_reuseFailAlloc_3734_, 29, v_negFn_3708_);
lean_ctor_set(v_reuseFailAlloc_3734_, 30, v_vars_3709_);
lean_ctor_set(v_reuseFailAlloc_3734_, 31, v_varMap_3710_);
lean_ctor_set(v_reuseFailAlloc_3734_, 32, v_lowers_3711_);
lean_ctor_set(v_reuseFailAlloc_3734_, 33, v_uppers_3712_);
lean_ctor_set(v_reuseFailAlloc_3734_, 34, v___x_3727_);
lean_ctor_set(v_reuseFailAlloc_3734_, 35, v_assignment_3714_);
lean_ctor_set(v_reuseFailAlloc_3734_, 36, v_conflict_x3f_3716_);
lean_ctor_set(v_reuseFailAlloc_3734_, 37, v_diseqSplits_3717_);
lean_ctor_set(v_reuseFailAlloc_3734_, 38, v_elimEqs_3718_);
lean_ctor_set(v_reuseFailAlloc_3734_, 39, v_elimStack_3719_);
lean_ctor_set(v_reuseFailAlloc_3734_, 40, v_occurs_3720_);
lean_ctor_set(v_reuseFailAlloc_3734_, 41, v_ignored_3721_);
lean_ctor_set_uint8(v_reuseFailAlloc_3734_, sizeof(void*)*42, v_caseSplits_3715_);
v___x_3729_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
lean_object* v___x_3730_; lean_object* v___x_3732_; 
v___x_3730_ = lean_array_fset(v_xs_x27_3726_, v_a_3661_, v___x_3729_);
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 0, v___x_3730_);
v___x_3732_ = v___x_3676_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3730_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_typeIdOf_3666_);
lean_ctor_set(v_reuseFailAlloc_3733_, 2, v_exprToStructId_3667_);
lean_ctor_set(v_reuseFailAlloc_3733_, 3, v_exprToStructIdEntries_3668_);
lean_ctor_set(v_reuseFailAlloc_3733_, 4, v_forbiddenNatModules_3669_);
lean_ctor_set(v_reuseFailAlloc_3733_, 5, v_natStructs_3670_);
lean_ctor_set(v_reuseFailAlloc_3733_, 6, v_natTypeIdOf_3671_);
lean_ctor_set(v_reuseFailAlloc_3733_, 7, v_exprToNatStructId_3672_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed(lean_object* v_a_3745_, lean_object* v_y_3746_, lean_object* v_fst_3747_, lean_object* v_s_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(v_a_3745_, v_y_3746_, v_fst_3747_, v_s_3748_);
lean_dec(v_y_3746_);
lean_dec(v_a_3745_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object* v_a_3750_, lean_object* v_x_3751_, lean_object* v_c_3752_, lean_object* v_as_3753_, size_t v_sz_3754_, size_t v_i_3755_, lean_object* v_b_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
lean_object* v_a_3770_; uint8_t v___x_3774_; 
v___x_3774_ = lean_usize_dec_lt(v_i_3755_, v_sz_3754_);
if (v___x_3774_ == 0)
{
lean_object* v___x_3775_; 
lean_dec_ref(v_c_3752_);
v___x_3775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3775_, 0, v_b_3756_);
return v___x_3775_;
}
else
{
lean_object* v_a_3776_; lean_object* v_fst_3777_; lean_object* v_snd_3778_; lean_object* v___x_3779_; 
lean_dec_ref(v_b_3756_);
v_a_3776_ = lean_array_uget_borrowed(v_as_3753_, v_i_3755_);
v_fst_3777_ = lean_ctor_get(v_a_3776_, 0);
v_snd_3778_ = lean_ctor_get(v_a_3776_, 1);
lean_inc(v_snd_3778_);
lean_inc(v_fst_3777_);
lean_inc_ref(v_c_3752_);
v___x_3779_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_3750_, v_x_3751_, v_c_3752_, v_fst_3777_, v_snd_3778_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; lean_object* v___x_3781_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
lean_dec_ref(v___x_3779_);
v___x_3781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
if (lean_obj_tag(v_a_3780_) == 1)
{
lean_object* v_val_3782_; lean_object* v___x_3783_; 
v_val_3782_ = lean_ctor_get(v_a_3780_, 0);
lean_inc(v_val_3782_);
lean_dec_ref(v_a_3780_);
v___x_3783_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_val_3782_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v___x_3784_; 
lean_dec_ref(v___x_3783_);
v___x_3784_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3794_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3787_ = v___x_3784_;
v_isShared_3788_ = v_isSharedCheck_3794_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3784_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3794_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
uint8_t v___x_3789_; 
v___x_3789_ = lean_unbox(v_a_3785_);
lean_dec(v_a_3785_);
if (v___x_3789_ == 0)
{
lean_del_object(v___x_3787_);
v_a_3770_ = v___x_3781_;
goto v___jp_3769_;
}
else
{
lean_object* v___x_3790_; lean_object* v___x_3792_; 
lean_dec_ref(v_c_3752_);
v___x_3790_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v___x_3790_);
v___x_3792_ = v___x_3787_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v___x_3790_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
else
{
lean_object* v_a_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3802_; 
lean_dec_ref(v_c_3752_);
v_a_3795_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3797_ = v___x_3784_;
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_a_3795_);
lean_dec(v___x_3784_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3800_; 
if (v_isShared_3798_ == 0)
{
v___x_3800_ = v___x_3797_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_a_3795_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
else
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3810_; 
lean_dec_ref(v_c_3752_);
v_a_3803_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3805_ = v___x_3783_;
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3783_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3808_; 
if (v_isShared_3806_ == 0)
{
v___x_3808_ = v___x_3805_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3803_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
else
{
lean_object* v___x_3811_; 
lean_dec(v_a_3780_);
v___x_3811_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_snd_3778_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
if (lean_obj_tag(v___x_3811_) == 0)
{
lean_dec_ref(v___x_3811_);
v_a_3770_ = v___x_3781_;
goto v___jp_3769_;
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_dec_ref(v_c_3752_);
v_a_3812_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3811_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3811_);
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
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
lean_dec_ref(v_c_3752_);
v_a_3820_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3779_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3779_);
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
v___jp_3769_:
{
size_t v___x_3771_; size_t v___x_3772_; 
v___x_3771_ = ((size_t)1ULL);
v___x_3772_ = lean_usize_add(v_i_3755_, v___x_3771_);
lean_inc_ref(v_a_3770_);
v_i_3755_ = v___x_3772_;
v_b_3756_ = v_a_3770_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object** _args){
lean_object* v_a_3828_ = _args[0];
lean_object* v_x_3829_ = _args[1];
lean_object* v_c_3830_ = _args[2];
lean_object* v_as_3831_ = _args[3];
lean_object* v_sz_3832_ = _args[4];
lean_object* v_i_3833_ = _args[5];
lean_object* v_b_3834_ = _args[6];
lean_object* v___y_3835_ = _args[7];
lean_object* v___y_3836_ = _args[8];
lean_object* v___y_3837_ = _args[9];
lean_object* v___y_3838_ = _args[10];
lean_object* v___y_3839_ = _args[11];
lean_object* v___y_3840_ = _args[12];
lean_object* v___y_3841_ = _args[13];
lean_object* v___y_3842_ = _args[14];
lean_object* v___y_3843_ = _args[15];
lean_object* v___y_3844_ = _args[16];
lean_object* v___y_3845_ = _args[17];
lean_object* v___y_3846_ = _args[18];
_start:
{
size_t v_sz_boxed_3847_; size_t v_i_boxed_3848_; lean_object* v_res_3849_; 
v_sz_boxed_3847_ = lean_unbox_usize(v_sz_3832_);
lean_dec(v_sz_3832_);
v_i_boxed_3848_ = lean_unbox_usize(v_i_3833_);
lean_dec(v_i_3833_);
v_res_3849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3828_, v_x_3829_, v_c_3830_, v_as_3831_, v_sz_boxed_3847_, v_i_boxed_3848_, v_b_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec(v___y_3835_);
lean_dec_ref(v_as_3831_);
lean_dec(v_x_3829_);
lean_dec(v_a_3828_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object* v_a_3850_, lean_object* v_x_3851_, lean_object* v_c_3852_, lean_object* v_y_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_){
_start:
{
lean_object* v___x_3866_; 
v___x_3866_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3926_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3869_ = v___x_3866_;
v_isShared_3870_ = v_isSharedCheck_3926_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3866_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3926_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
uint8_t v___x_3871_; 
v___x_3871_ = lean_unbox(v_a_3867_);
lean_dec(v_a_3867_);
if (v___x_3871_ == 0)
{
lean_object* v___x_3872_; 
lean_del_object(v___x_3869_);
v___x_3872_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; lean_object* v___y_3875_; lean_object* v_diseqs_3908_; lean_object* v_size_3909_; lean_object* v___x_3910_; uint8_t v___x_3911_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_a_3873_);
lean_dec_ref(v___x_3872_);
v_diseqs_3908_ = lean_ctor_get(v_a_3873_, 34);
lean_inc_ref(v_diseqs_3908_);
lean_dec(v_a_3873_);
v_size_3909_ = lean_ctor_get(v_diseqs_3908_, 2);
v___x_3910_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_3911_ = lean_nat_dec_lt(v_y_3853_, v_size_3909_);
if (v___x_3911_ == 0)
{
lean_object* v___x_3912_; 
lean_dec_ref(v_diseqs_3908_);
v___x_3912_ = l_outOfBounds___redArg(v___x_3910_);
v___y_3875_ = v___x_3912_;
goto v___jp_3874_;
}
else
{
lean_object* v___x_3913_; 
v___x_3913_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3910_, v_diseqs_3908_, v_y_3853_);
lean_dec_ref(v_diseqs_3908_);
v___y_3875_ = v___x_3913_;
goto v___jp_3874_;
}
v___jp_3874_:
{
lean_object* v___x_3876_; lean_object* v_fst_3877_; lean_object* v_snd_3878_; lean_object* v___f_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3876_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3851_, v___y_3875_);
lean_dec_ref(v___y_3875_);
v_fst_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_fst_3877_);
v_snd_3878_ = lean_ctor_get(v___x_3876_, 1);
lean_inc(v_snd_3878_);
lean_dec_ref(v___x_3876_);
lean_inc(v_a_3854_);
v___f_3879_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3879_, 0, v_a_3854_);
lean_closure_set(v___f_3879_, 1, v_y_3853_);
lean_closure_set(v___f_3879_, 2, v_fst_3877_);
v___x_3880_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3881_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3880_, v___f_3879_, v_a_3855_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v___x_3882_; lean_object* v___x_3883_; size_t v_sz_3884_; size_t v___x_3885_; lean_object* v___x_3886_; 
lean_dec_ref(v___x_3881_);
v___x_3882_ = lean_box(0);
v___x_3883_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_3884_ = lean_array_size(v_snd_3878_);
v___x_3885_ = ((size_t)0ULL);
v___x_3886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3850_, v_x_3851_, v_c_3852_, v_snd_3878_, v_sz_3884_, v___x_3885_, v___x_3883_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_);
lean_dec(v_snd_3878_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3899_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3889_ = v___x_3886_;
v_isShared_3890_ = v_isSharedCheck_3899_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3886_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3899_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v_fst_3891_; 
v_fst_3891_ = lean_ctor_get(v_a_3887_, 0);
lean_inc(v_fst_3891_);
lean_dec(v_a_3887_);
if (lean_obj_tag(v_fst_3891_) == 0)
{
lean_object* v___x_3893_; 
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 0, v___x_3882_);
v___x_3893_ = v___x_3889_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3882_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
else
{
lean_object* v_val_3895_; lean_object* v___x_3897_; 
v_val_3895_ = lean_ctor_get(v_fst_3891_, 0);
lean_inc(v_val_3895_);
lean_dec_ref(v_fst_3891_);
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 0, v_val_3895_);
v___x_3897_ = v___x_3889_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_val_3895_);
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
v_a_3900_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v___x_3886_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3886_);
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
lean_dec(v_snd_3878_);
lean_dec_ref(v_c_3852_);
return v___x_3881_;
}
}
}
else
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
lean_dec(v_y_3853_);
lean_dec_ref(v_c_3852_);
v_a_3914_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3872_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3872_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
else
{
lean_object* v___x_3922_; lean_object* v___x_3924_; 
lean_dec(v_y_3853_);
lean_dec_ref(v_c_3852_);
v___x_3922_ = lean_box(0);
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 0, v___x_3922_);
v___x_3924_ = v___x_3869_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3922_);
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
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_dec(v_y_3853_);
lean_dec_ref(v_c_3852_);
v_a_3927_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___x_3866_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3866_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object* v_a_3935_, lean_object* v_x_3936_, lean_object* v_c_3937_, lean_object* v_y_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v_a_3935_, v_x_3936_, v_c_3937_, v_y_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
lean_dec(v_a_3949_);
lean_dec_ref(v_a_3948_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
lean_dec(v_a_3941_);
lean_dec(v_a_3940_);
lean_dec(v_a_3939_);
lean_dec(v_x_3936_);
lean_dec(v_a_3935_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object* v_a_3952_, lean_object* v_x_3953_, lean_object* v_c_3954_, lean_object* v_y_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_){
_start:
{
lean_object* v___x_3968_; 
lean_inc(v_y_3955_);
lean_inc_ref(v_c_3954_);
lean_inc(v_x_3953_);
lean_inc(v_a_3952_);
v___x_3968_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_3952_, v_x_3953_, v_c_3954_, v_y_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v___x_3969_; 
lean_dec_ref(v___x_3968_);
lean_inc(v_y_3955_);
lean_inc_ref(v_c_3954_);
lean_inc(v_x_3953_);
lean_inc(v_a_3952_);
v___x_3969_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_3952_, v_x_3953_, v_c_3954_, v_y_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v___x_3970_; lean_object* v___x_3971_; 
lean_dec_ref(v___x_3969_);
v___x_3970_ = lean_nat_to_int(v_a_3952_);
v___x_3971_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v___x_3970_, v_x_3953_, v_c_3954_, v_y_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_);
lean_dec(v_x_3953_);
lean_dec(v___x_3970_);
return v___x_3971_;
}
else
{
lean_dec(v_y_3955_);
lean_dec_ref(v_c_3954_);
lean_dec(v_x_3953_);
lean_dec(v_a_3952_);
return v___x_3969_;
}
}
else
{
lean_dec(v_y_3955_);
lean_dec_ref(v_c_3954_);
lean_dec(v_x_3953_);
lean_dec(v_a_3952_);
return v___x_3968_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object* v_a_3972_, lean_object* v_x_3973_, lean_object* v_c_3974_, lean_object* v_y_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_3972_, v_x_3973_, v_c_3974_, v_y_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_);
lean_dec(v_a_3986_);
lean_dec_ref(v_a_3985_);
lean_dec(v_a_3984_);
lean_dec_ref(v_a_3983_);
lean_dec(v_a_3982_);
lean_dec_ref(v_a_3981_);
lean_dec(v_a_3980_);
lean_dec_ref(v_a_3979_);
lean_dec(v_a_3978_);
lean_dec(v_a_3977_);
lean_dec(v_a_3976_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(lean_object* v_a_3989_, lean_object* v_x_3990_, lean_object* v_s_3991_){
_start:
{
lean_object* v_structs_3992_; lean_object* v_typeIdOf_3993_; lean_object* v_exprToStructId_3994_; lean_object* v_exprToStructIdEntries_3995_; lean_object* v_forbiddenNatModules_3996_; lean_object* v_natStructs_3997_; lean_object* v_natTypeIdOf_3998_; lean_object* v_exprToNatStructId_3999_; lean_object* v___x_4000_; uint8_t v___x_4001_; 
v_structs_3992_ = lean_ctor_get(v_s_3991_, 0);
v_typeIdOf_3993_ = lean_ctor_get(v_s_3991_, 1);
v_exprToStructId_3994_ = lean_ctor_get(v_s_3991_, 2);
v_exprToStructIdEntries_3995_ = lean_ctor_get(v_s_3991_, 3);
v_forbiddenNatModules_3996_ = lean_ctor_get(v_s_3991_, 4);
v_natStructs_3997_ = lean_ctor_get(v_s_3991_, 5);
v_natTypeIdOf_3998_ = lean_ctor_get(v_s_3991_, 6);
v_exprToNatStructId_3999_ = lean_ctor_get(v_s_3991_, 7);
v___x_4000_ = lean_array_get_size(v_structs_3992_);
v___x_4001_ = lean_nat_dec_lt(v_a_3989_, v___x_4000_);
if (v___x_4001_ == 0)
{
return v_s_3991_;
}
else
{
lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4064_; 
lean_inc_ref(v_exprToNatStructId_3999_);
lean_inc_ref(v_natTypeIdOf_3998_);
lean_inc_ref(v_natStructs_3997_);
lean_inc_ref(v_forbiddenNatModules_3996_);
lean_inc_ref(v_exprToStructIdEntries_3995_);
lean_inc_ref(v_exprToStructId_3994_);
lean_inc_ref(v_typeIdOf_3993_);
lean_inc_ref(v_structs_3992_);
v_isSharedCheck_4064_ = !lean_is_exclusive(v_s_3991_);
if (v_isSharedCheck_4064_ == 0)
{
lean_object* v_unused_4065_; lean_object* v_unused_4066_; lean_object* v_unused_4067_; lean_object* v_unused_4068_; lean_object* v_unused_4069_; lean_object* v_unused_4070_; lean_object* v_unused_4071_; lean_object* v_unused_4072_; 
v_unused_4065_ = lean_ctor_get(v_s_3991_, 7);
lean_dec(v_unused_4065_);
v_unused_4066_ = lean_ctor_get(v_s_3991_, 6);
lean_dec(v_unused_4066_);
v_unused_4067_ = lean_ctor_get(v_s_3991_, 5);
lean_dec(v_unused_4067_);
v_unused_4068_ = lean_ctor_get(v_s_3991_, 4);
lean_dec(v_unused_4068_);
v_unused_4069_ = lean_ctor_get(v_s_3991_, 3);
lean_dec(v_unused_4069_);
v_unused_4070_ = lean_ctor_get(v_s_3991_, 2);
lean_dec(v_unused_4070_);
v_unused_4071_ = lean_ctor_get(v_s_3991_, 1);
lean_dec(v_unused_4071_);
v_unused_4072_ = lean_ctor_get(v_s_3991_, 0);
lean_dec(v_unused_4072_);
v___x_4003_ = v_s_3991_;
v_isShared_4004_ = v_isSharedCheck_4064_;
goto v_resetjp_4002_;
}
else
{
lean_dec(v_s_3991_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4064_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v_v_4005_; lean_object* v_id_4006_; lean_object* v_ringId_x3f_4007_; lean_object* v_type_4008_; lean_object* v_u_4009_; lean_object* v_intModuleInst_4010_; lean_object* v_leInst_x3f_4011_; lean_object* v_ltInst_x3f_4012_; lean_object* v_lawfulOrderLTInst_x3f_4013_; lean_object* v_isPreorderInst_x3f_4014_; lean_object* v_orderedAddInst_x3f_4015_; lean_object* v_isLinearInst_x3f_4016_; lean_object* v_noNatDivInst_x3f_4017_; lean_object* v_ringInst_x3f_4018_; lean_object* v_commRingInst_x3f_4019_; lean_object* v_orderedRingInst_x3f_4020_; lean_object* v_fieldInst_x3f_4021_; lean_object* v_charInst_x3f_4022_; lean_object* v_zero_4023_; lean_object* v_ofNatZero_4024_; lean_object* v_one_x3f_4025_; lean_object* v_leFn_x3f_4026_; lean_object* v_ltFn_x3f_4027_; lean_object* v_addFn_4028_; lean_object* v_zsmulFn_4029_; lean_object* v_nsmulFn_4030_; lean_object* v_zsmulFn_x3f_4031_; lean_object* v_nsmulFn_x3f_4032_; lean_object* v_homomulFn_x3f_4033_; lean_object* v_subFn_4034_; lean_object* v_negFn_4035_; lean_object* v_vars_4036_; lean_object* v_varMap_4037_; lean_object* v_lowers_4038_; lean_object* v_uppers_4039_; lean_object* v_diseqs_4040_; lean_object* v_assignment_4041_; uint8_t v_caseSplits_4042_; lean_object* v_conflict_x3f_4043_; lean_object* v_diseqSplits_4044_; lean_object* v_elimEqs_4045_; lean_object* v_elimStack_4046_; lean_object* v_occurs_4047_; lean_object* v_ignored_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4063_; 
v_v_4005_ = lean_array_fget(v_structs_3992_, v_a_3989_);
v_id_4006_ = lean_ctor_get(v_v_4005_, 0);
v_ringId_x3f_4007_ = lean_ctor_get(v_v_4005_, 1);
v_type_4008_ = lean_ctor_get(v_v_4005_, 2);
v_u_4009_ = lean_ctor_get(v_v_4005_, 3);
v_intModuleInst_4010_ = lean_ctor_get(v_v_4005_, 4);
v_leInst_x3f_4011_ = lean_ctor_get(v_v_4005_, 5);
v_ltInst_x3f_4012_ = lean_ctor_get(v_v_4005_, 6);
v_lawfulOrderLTInst_x3f_4013_ = lean_ctor_get(v_v_4005_, 7);
v_isPreorderInst_x3f_4014_ = lean_ctor_get(v_v_4005_, 8);
v_orderedAddInst_x3f_4015_ = lean_ctor_get(v_v_4005_, 9);
v_isLinearInst_x3f_4016_ = lean_ctor_get(v_v_4005_, 10);
v_noNatDivInst_x3f_4017_ = lean_ctor_get(v_v_4005_, 11);
v_ringInst_x3f_4018_ = lean_ctor_get(v_v_4005_, 12);
v_commRingInst_x3f_4019_ = lean_ctor_get(v_v_4005_, 13);
v_orderedRingInst_x3f_4020_ = lean_ctor_get(v_v_4005_, 14);
v_fieldInst_x3f_4021_ = lean_ctor_get(v_v_4005_, 15);
v_charInst_x3f_4022_ = lean_ctor_get(v_v_4005_, 16);
v_zero_4023_ = lean_ctor_get(v_v_4005_, 17);
v_ofNatZero_4024_ = lean_ctor_get(v_v_4005_, 18);
v_one_x3f_4025_ = lean_ctor_get(v_v_4005_, 19);
v_leFn_x3f_4026_ = lean_ctor_get(v_v_4005_, 20);
v_ltFn_x3f_4027_ = lean_ctor_get(v_v_4005_, 21);
v_addFn_4028_ = lean_ctor_get(v_v_4005_, 22);
v_zsmulFn_4029_ = lean_ctor_get(v_v_4005_, 23);
v_nsmulFn_4030_ = lean_ctor_get(v_v_4005_, 24);
v_zsmulFn_x3f_4031_ = lean_ctor_get(v_v_4005_, 25);
v_nsmulFn_x3f_4032_ = lean_ctor_get(v_v_4005_, 26);
v_homomulFn_x3f_4033_ = lean_ctor_get(v_v_4005_, 27);
v_subFn_4034_ = lean_ctor_get(v_v_4005_, 28);
v_negFn_4035_ = lean_ctor_get(v_v_4005_, 29);
v_vars_4036_ = lean_ctor_get(v_v_4005_, 30);
v_varMap_4037_ = lean_ctor_get(v_v_4005_, 31);
v_lowers_4038_ = lean_ctor_get(v_v_4005_, 32);
v_uppers_4039_ = lean_ctor_get(v_v_4005_, 33);
v_diseqs_4040_ = lean_ctor_get(v_v_4005_, 34);
v_assignment_4041_ = lean_ctor_get(v_v_4005_, 35);
v_caseSplits_4042_ = lean_ctor_get_uint8(v_v_4005_, sizeof(void*)*42);
v_conflict_x3f_4043_ = lean_ctor_get(v_v_4005_, 36);
v_diseqSplits_4044_ = lean_ctor_get(v_v_4005_, 37);
v_elimEqs_4045_ = lean_ctor_get(v_v_4005_, 38);
v_elimStack_4046_ = lean_ctor_get(v_v_4005_, 39);
v_occurs_4047_ = lean_ctor_get(v_v_4005_, 40);
v_ignored_4048_ = lean_ctor_get(v_v_4005_, 41);
v_isSharedCheck_4063_ = !lean_is_exclusive(v_v_4005_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4050_ = v_v_4005_;
v_isShared_4051_ = v_isSharedCheck_4063_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_ignored_4048_);
lean_inc(v_occurs_4047_);
lean_inc(v_elimStack_4046_);
lean_inc(v_elimEqs_4045_);
lean_inc(v_diseqSplits_4044_);
lean_inc(v_conflict_x3f_4043_);
lean_inc(v_assignment_4041_);
lean_inc(v_diseqs_4040_);
lean_inc(v_uppers_4039_);
lean_inc(v_lowers_4038_);
lean_inc(v_varMap_4037_);
lean_inc(v_vars_4036_);
lean_inc(v_negFn_4035_);
lean_inc(v_subFn_4034_);
lean_inc(v_homomulFn_x3f_4033_);
lean_inc(v_nsmulFn_x3f_4032_);
lean_inc(v_zsmulFn_x3f_4031_);
lean_inc(v_nsmulFn_4030_);
lean_inc(v_zsmulFn_4029_);
lean_inc(v_addFn_4028_);
lean_inc(v_ltFn_x3f_4027_);
lean_inc(v_leFn_x3f_4026_);
lean_inc(v_one_x3f_4025_);
lean_inc(v_ofNatZero_4024_);
lean_inc(v_zero_4023_);
lean_inc(v_charInst_x3f_4022_);
lean_inc(v_fieldInst_x3f_4021_);
lean_inc(v_orderedRingInst_x3f_4020_);
lean_inc(v_commRingInst_x3f_4019_);
lean_inc(v_ringInst_x3f_4018_);
lean_inc(v_noNatDivInst_x3f_4017_);
lean_inc(v_isLinearInst_x3f_4016_);
lean_inc(v_orderedAddInst_x3f_4015_);
lean_inc(v_isPreorderInst_x3f_4014_);
lean_inc(v_lawfulOrderLTInst_x3f_4013_);
lean_inc(v_ltInst_x3f_4012_);
lean_inc(v_leInst_x3f_4011_);
lean_inc(v_intModuleInst_4010_);
lean_inc(v_u_4009_);
lean_inc(v_type_4008_);
lean_inc(v_ringId_x3f_4007_);
lean_inc(v_id_4006_);
lean_dec(v_v_4005_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4063_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4052_; lean_object* v_xs_x27_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4057_; 
v___x_4052_ = lean_box(0);
v_xs_x27_4053_ = lean_array_fset(v_structs_3992_, v_a_3989_, v___x_4052_);
v___x_4054_ = lean_box(1);
v___x_4055_ = l_Lean_PersistentArray_set___redArg(v_occurs_4047_, v_x_3990_, v___x_4054_);
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 40, v___x_4055_);
v___x_4057_ = v___x_4050_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_id_4006_);
lean_ctor_set(v_reuseFailAlloc_4062_, 1, v_ringId_x3f_4007_);
lean_ctor_set(v_reuseFailAlloc_4062_, 2, v_type_4008_);
lean_ctor_set(v_reuseFailAlloc_4062_, 3, v_u_4009_);
lean_ctor_set(v_reuseFailAlloc_4062_, 4, v_intModuleInst_4010_);
lean_ctor_set(v_reuseFailAlloc_4062_, 5, v_leInst_x3f_4011_);
lean_ctor_set(v_reuseFailAlloc_4062_, 6, v_ltInst_x3f_4012_);
lean_ctor_set(v_reuseFailAlloc_4062_, 7, v_lawfulOrderLTInst_x3f_4013_);
lean_ctor_set(v_reuseFailAlloc_4062_, 8, v_isPreorderInst_x3f_4014_);
lean_ctor_set(v_reuseFailAlloc_4062_, 9, v_orderedAddInst_x3f_4015_);
lean_ctor_set(v_reuseFailAlloc_4062_, 10, v_isLinearInst_x3f_4016_);
lean_ctor_set(v_reuseFailAlloc_4062_, 11, v_noNatDivInst_x3f_4017_);
lean_ctor_set(v_reuseFailAlloc_4062_, 12, v_ringInst_x3f_4018_);
lean_ctor_set(v_reuseFailAlloc_4062_, 13, v_commRingInst_x3f_4019_);
lean_ctor_set(v_reuseFailAlloc_4062_, 14, v_orderedRingInst_x3f_4020_);
lean_ctor_set(v_reuseFailAlloc_4062_, 15, v_fieldInst_x3f_4021_);
lean_ctor_set(v_reuseFailAlloc_4062_, 16, v_charInst_x3f_4022_);
lean_ctor_set(v_reuseFailAlloc_4062_, 17, v_zero_4023_);
lean_ctor_set(v_reuseFailAlloc_4062_, 18, v_ofNatZero_4024_);
lean_ctor_set(v_reuseFailAlloc_4062_, 19, v_one_x3f_4025_);
lean_ctor_set(v_reuseFailAlloc_4062_, 20, v_leFn_x3f_4026_);
lean_ctor_set(v_reuseFailAlloc_4062_, 21, v_ltFn_x3f_4027_);
lean_ctor_set(v_reuseFailAlloc_4062_, 22, v_addFn_4028_);
lean_ctor_set(v_reuseFailAlloc_4062_, 23, v_zsmulFn_4029_);
lean_ctor_set(v_reuseFailAlloc_4062_, 24, v_nsmulFn_4030_);
lean_ctor_set(v_reuseFailAlloc_4062_, 25, v_zsmulFn_x3f_4031_);
lean_ctor_set(v_reuseFailAlloc_4062_, 26, v_nsmulFn_x3f_4032_);
lean_ctor_set(v_reuseFailAlloc_4062_, 27, v_homomulFn_x3f_4033_);
lean_ctor_set(v_reuseFailAlloc_4062_, 28, v_subFn_4034_);
lean_ctor_set(v_reuseFailAlloc_4062_, 29, v_negFn_4035_);
lean_ctor_set(v_reuseFailAlloc_4062_, 30, v_vars_4036_);
lean_ctor_set(v_reuseFailAlloc_4062_, 31, v_varMap_4037_);
lean_ctor_set(v_reuseFailAlloc_4062_, 32, v_lowers_4038_);
lean_ctor_set(v_reuseFailAlloc_4062_, 33, v_uppers_4039_);
lean_ctor_set(v_reuseFailAlloc_4062_, 34, v_diseqs_4040_);
lean_ctor_set(v_reuseFailAlloc_4062_, 35, v_assignment_4041_);
lean_ctor_set(v_reuseFailAlloc_4062_, 36, v_conflict_x3f_4043_);
lean_ctor_set(v_reuseFailAlloc_4062_, 37, v_diseqSplits_4044_);
lean_ctor_set(v_reuseFailAlloc_4062_, 38, v_elimEqs_4045_);
lean_ctor_set(v_reuseFailAlloc_4062_, 39, v_elimStack_4046_);
lean_ctor_set(v_reuseFailAlloc_4062_, 40, v___x_4055_);
lean_ctor_set(v_reuseFailAlloc_4062_, 41, v_ignored_4048_);
lean_ctor_set_uint8(v_reuseFailAlloc_4062_, sizeof(void*)*42, v_caseSplits_4042_);
v___x_4057_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
lean_object* v___x_4058_; lean_object* v___x_4060_; 
v___x_4058_ = lean_array_fset(v_xs_x27_4053_, v_a_3989_, v___x_4057_);
if (v_isShared_4004_ == 0)
{
lean_ctor_set(v___x_4003_, 0, v___x_4058_);
v___x_4060_ = v___x_4003_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v___x_4058_);
lean_ctor_set(v_reuseFailAlloc_4061_, 1, v_typeIdOf_3993_);
lean_ctor_set(v_reuseFailAlloc_4061_, 2, v_exprToStructId_3994_);
lean_ctor_set(v_reuseFailAlloc_4061_, 3, v_exprToStructIdEntries_3995_);
lean_ctor_set(v_reuseFailAlloc_4061_, 4, v_forbiddenNatModules_3996_);
lean_ctor_set(v_reuseFailAlloc_4061_, 5, v_natStructs_3997_);
lean_ctor_set(v_reuseFailAlloc_4061_, 6, v_natTypeIdOf_3998_);
lean_ctor_set(v_reuseFailAlloc_4061_, 7, v_exprToNatStructId_3999_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed(lean_object* v_a_4073_, lean_object* v_x_4074_, lean_object* v_s_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(v_a_4073_, v_x_4074_, v_s_4075_);
lean_dec(v_x_4074_);
lean_dec(v_a_4073_);
return v_res_4076_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object* v_a_4077_, lean_object* v_x_4078_, lean_object* v_c_4079_, lean_object* v_init_4080_, lean_object* v_x_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
if (lean_obj_tag(v_x_4081_) == 0)
{
lean_object* v_k_4094_; lean_object* v_l_4095_; lean_object* v_r_4096_; lean_object* v___x_4097_; 
v_k_4094_ = lean_ctor_get(v_x_4081_, 1);
lean_inc(v_k_4094_);
v_l_4095_ = lean_ctor_get(v_x_4081_, 3);
lean_inc(v_l_4095_);
v_r_4096_ = lean_ctor_get(v_x_4081_, 4);
lean_inc(v_r_4096_);
lean_dec_ref(v_x_4081_);
lean_inc_ref(v_c_4079_);
lean_inc(v_x_4078_);
lean_inc(v_a_4077_);
v___x_4097_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4077_, v_x_4078_, v_c_4079_, v_init_4080_, v_l_4095_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v___x_4098_; 
lean_dec_ref(v___x_4097_);
lean_inc_ref(v_c_4079_);
lean_inc(v_x_4078_);
lean_inc(v_a_4077_);
v___x_4098_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4077_, v_x_4078_, v_c_4079_, v_k_4094_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v___x_4099_; 
lean_dec_ref(v___x_4098_);
v___x_4099_ = lean_box(0);
v_init_4080_ = v___x_4099_;
v_x_4081_ = v_r_4096_;
goto _start;
}
else
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
lean_dec(v_r_4096_);
lean_dec_ref(v_c_4079_);
lean_dec(v_x_4078_);
lean_dec(v_a_4077_);
v_a_4101_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4098_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4098_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
else
{
lean_dec(v_r_4096_);
lean_dec(v_k_4094_);
lean_dec_ref(v_c_4079_);
lean_dec(v_x_4078_);
lean_dec(v_a_4077_);
return v___x_4097_;
}
}
else
{
lean_object* v___x_4109_; lean_object* v___x_4110_; 
lean_dec_ref(v_c_4079_);
lean_dec(v_x_4078_);
lean_dec(v_a_4077_);
v___x_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4109_, 0, v_init_4080_);
v___x_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4109_);
return v___x_4110_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object** _args){
lean_object* v_a_4111_ = _args[0];
lean_object* v_x_4112_ = _args[1];
lean_object* v_c_4113_ = _args[2];
lean_object* v_init_4114_ = _args[3];
lean_object* v_x_4115_ = _args[4];
lean_object* v___y_4116_ = _args[5];
lean_object* v___y_4117_ = _args[6];
lean_object* v___y_4118_ = _args[7];
lean_object* v___y_4119_ = _args[8];
lean_object* v___y_4120_ = _args[9];
lean_object* v___y_4121_ = _args[10];
lean_object* v___y_4122_ = _args[11];
lean_object* v___y_4123_ = _args[12];
lean_object* v___y_4124_ = _args[13];
lean_object* v___y_4125_ = _args[14];
lean_object* v___y_4126_ = _args[15];
lean_object* v___y_4127_ = _args[16];
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4111_, v_x_4112_, v_c_4113_, v_init_4114_, v_x_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec(v___y_4116_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object* v_a_4129_, lean_object* v_x_4130_, lean_object* v_c_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_){
_start:
{
lean_object* v___x_4144_; 
v___x_4144_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_object* v_a_4145_; lean_object* v_occurs_4146_; lean_object* v_size_4147_; lean_object* v___f_4148_; lean_object* v___y_4150_; lean_object* v___x_4172_; uint8_t v___x_4173_; 
v_a_4145_ = lean_ctor_get(v___x_4144_, 0);
lean_inc(v_a_4145_);
lean_dec_ref(v___x_4144_);
v_occurs_4146_ = lean_ctor_get(v_a_4145_, 40);
lean_inc_ref(v_occurs_4146_);
lean_dec(v_a_4145_);
v_size_4147_ = lean_ctor_get(v_occurs_4146_, 2);
lean_inc(v_x_4130_);
lean_inc(v_a_4132_);
v___f_4148_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4148_, 0, v_a_4132_);
lean_closure_set(v___f_4148_, 1, v_x_4130_);
v___x_4172_ = lean_box(1);
v___x_4173_ = lean_nat_dec_lt(v_x_4130_, v_size_4147_);
if (v___x_4173_ == 0)
{
lean_object* v___x_4174_; 
lean_dec_ref(v_occurs_4146_);
v___x_4174_ = l_outOfBounds___redArg(v___x_4172_);
v___y_4150_ = v___x_4174_;
goto v___jp_4149_;
}
else
{
lean_object* v___x_4175_; 
v___x_4175_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4172_, v_occurs_4146_, v_x_4130_);
lean_dec_ref(v_occurs_4146_);
v___y_4150_ = v___x_4175_;
goto v___jp_4149_;
}
v___jp_4149_:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4151_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4152_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4151_, v___f_4148_, v_a_4133_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v___x_4153_; 
lean_dec_ref(v___x_4152_);
lean_inc_ref(v_c_4131_);
lean_inc_n(v_x_4130_, 2);
lean_inc(v_a_4129_);
v___x_4153_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4129_, v_x_4130_, v_c_4131_, v_x_4130_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
lean_dec_ref(v___x_4153_);
v___x_4154_ = lean_box(0);
v___x_4155_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4129_, v_x_4130_, v_c_4131_, v___x_4154_, v___y_4150_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4162_ == 0)
{
lean_object* v_unused_4163_; 
v_unused_4163_ = lean_ctor_get(v___x_4155_, 0);
lean_dec(v_unused_4163_);
v___x_4157_ = v___x_4155_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_dec(v___x_4155_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
lean_ctor_set(v___x_4157_, 0, v___x_4154_);
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4154_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
else
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
v_a_4164_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___x_4155_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_4155_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4164_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
}
else
{
lean_dec(v___y_4150_);
lean_dec_ref(v_c_4131_);
lean_dec(v_x_4130_);
lean_dec(v_a_4129_);
return v___x_4153_;
}
}
else
{
lean_dec(v___y_4150_);
lean_dec_ref(v_c_4131_);
lean_dec(v_x_4130_);
lean_dec(v_a_4129_);
return v___x_4152_;
}
}
}
else
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
lean_dec_ref(v_c_4131_);
lean_dec(v_x_4130_);
lean_dec(v_a_4129_);
v_a_4176_ = lean_ctor_get(v___x_4144_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4144_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4144_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4181_; 
if (v_isShared_4179_ == 0)
{
v___x_4181_ = v___x_4178_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___boxed(lean_object* v_a_4184_, lean_object* v_x_4185_, lean_object* v_c_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_){
_start:
{
lean_object* v_res_4199_; 
v_res_4199_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v_a_4184_, v_x_4185_, v_c_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_);
lean_dec(v_a_4197_);
lean_dec_ref(v_a_4196_);
lean_dec(v_a_4195_);
lean_dec_ref(v_a_4194_);
lean_dec(v_a_4193_);
lean_dec_ref(v_a_4192_);
lean_dec(v_a_4191_);
lean_dec_ref(v_a_4190_);
lean_dec(v_a_4189_);
lean_dec(v_a_4188_);
lean_dec(v_a_4187_);
return v_res_4199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(lean_object* v_c_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_){
_start:
{
lean_object* v_p_4217_; 
v_p_4217_ = lean_ctor_get(v_c_4200_, 0);
if (lean_obj_tag(v_p_4217_) == 1)
{
lean_object* v_k_4218_; lean_object* v_v_4219_; lean_object* v_p_4220_; lean_object* v_y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___x_4271_; lean_object* v___x_4272_; uint8_t v___x_4273_; 
v_k_4218_ = lean_ctor_get(v_p_4217_, 0);
v_v_4219_ = lean_ctor_get(v_p_4217_, 1);
v_p_4220_ = lean_ctor_get(v_p_4217_, 2);
v___x_4271_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_4272_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4273_ = lean_int_dec_eq(v_k_4218_, v___x_4272_);
if (v___x_4273_ == 0)
{
uint8_t v___x_4274_; 
v___x_4274_ = lean_int_dec_eq(v_k_4218_, v___x_4271_);
if (v___x_4274_ == 0)
{
goto v___jp_4213_;
}
else
{
if (lean_obj_tag(v_p_4220_) == 1)
{
lean_object* v_k_4275_; lean_object* v_v_4276_; lean_object* v_p_4277_; uint8_t v___x_4278_; 
v_k_4275_ = lean_ctor_get(v_p_4220_, 0);
v_v_4276_ = lean_ctor_get(v_p_4220_, 1);
v_p_4277_ = lean_ctor_get(v_p_4220_, 2);
v___x_4278_ = lean_int_dec_eq(v_k_4275_, v___x_4272_);
if (v___x_4278_ == 0)
{
goto v___jp_4213_;
}
else
{
if (lean_obj_tag(v_p_4277_) == 0)
{
v_y_4222_ = v_v_4276_;
v___y_4223_ = v_a_4201_;
v___y_4224_ = v_a_4202_;
v___y_4225_ = v_a_4203_;
v___y_4226_ = v_a_4204_;
v___y_4227_ = v_a_4205_;
v___y_4228_ = v_a_4206_;
v___y_4229_ = v_a_4207_;
v___y_4230_ = v_a_4208_;
v___y_4231_ = v_a_4209_;
v___y_4232_ = v_a_4210_;
v___y_4233_ = v_a_4211_;
goto v___jp_4221_;
}
else
{
goto v___jp_4213_;
}
}
}
else
{
goto v___jp_4213_;
}
}
}
else
{
if (lean_obj_tag(v_p_4220_) == 1)
{
lean_object* v_k_4279_; lean_object* v_v_4280_; lean_object* v_p_4281_; uint8_t v___x_4282_; 
v_k_4279_ = lean_ctor_get(v_p_4220_, 0);
v_v_4280_ = lean_ctor_get(v_p_4220_, 1);
v_p_4281_ = lean_ctor_get(v_p_4220_, 2);
v___x_4282_ = lean_int_dec_eq(v_k_4279_, v___x_4271_);
if (v___x_4282_ == 0)
{
goto v___jp_4213_;
}
else
{
if (lean_obj_tag(v_p_4281_) == 0)
{
v_y_4222_ = v_v_4280_;
v___y_4223_ = v_a_4201_;
v___y_4224_ = v_a_4202_;
v___y_4225_ = v_a_4203_;
v___y_4226_ = v_a_4204_;
v___y_4227_ = v_a_4205_;
v___y_4228_ = v_a_4206_;
v___y_4229_ = v_a_4207_;
v___y_4230_ = v_a_4208_;
v___y_4231_ = v_a_4209_;
v___y_4232_ = v_a_4210_;
v___y_4233_ = v_a_4211_;
goto v___jp_4221_;
}
else
{
goto v___jp_4213_;
}
}
}
else
{
goto v___jp_4213_;
}
}
v___jp_4221_:
{
lean_object* v___x_4234_; 
v___x_4234_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_v_4219_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_object* v_a_4235_; lean_object* v___x_4236_; 
v_a_4235_ = lean_ctor_get(v___x_4234_, 0);
lean_inc(v_a_4235_);
lean_dec_ref(v___x_4234_);
v___x_4236_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; lean_object* v___x_4238_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_a_4237_);
lean_dec_ref(v___x_4236_);
v___x_4238_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_4235_, v_a_4237_, v___y_4224_);
lean_dec(v_a_4237_);
lean_dec(v_a_4235_);
if (lean_obj_tag(v___x_4238_) == 0)
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4254_; 
v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4238_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4241_ = v___x_4238_;
v_isShared_4242_ = v_isSharedCheck_4254_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4238_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4254_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
uint8_t v___x_4243_; 
v___x_4243_ = lean_unbox(v_a_4239_);
lean_dec(v_a_4239_);
if (v___x_4243_ == 0)
{
uint8_t v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4247_; 
v___x_4244_ = 1;
v___x_4245_ = lean_box(v___x_4244_);
if (v_isShared_4242_ == 0)
{
lean_ctor_set(v___x_4241_, 0, v___x_4245_);
v___x_4247_ = v___x_4241_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4245_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
else
{
uint8_t v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4252_; 
v___x_4249_ = 0;
v___x_4250_ = lean_box(v___x_4249_);
if (v_isShared_4242_ == 0)
{
lean_ctor_set(v___x_4241_, 0, v___x_4250_);
v___x_4252_ = v___x_4241_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v___x_4250_);
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
else
{
return v___x_4238_;
}
}
else
{
lean_object* v_a_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4262_; 
lean_dec(v_a_4235_);
v_a_4255_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4262_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4257_ = v___x_4236_;
v_isShared_4258_ = v_isSharedCheck_4262_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_a_4255_);
lean_dec(v___x_4236_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4262_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v___x_4260_; 
if (v_isShared_4258_ == 0)
{
v___x_4260_ = v___x_4257_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_a_4255_);
v___x_4260_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
return v___x_4260_;
}
}
}
}
else
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4270_; 
v_a_4263_ = lean_ctor_get(v___x_4234_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4234_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4265_ = v___x_4234_;
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v___x_4234_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4268_; 
if (v_isShared_4266_ == 0)
{
v___x_4268_ = v___x_4265_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4263_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
}
else
{
goto v___jp_4213_;
}
v___jp_4213_:
{
uint8_t v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; 
v___x_4214_ = 0;
v___x_4215_ = lean_box(v___x_4214_);
v___x_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4215_);
return v___x_4216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq___boxed(lean_object* v_c_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v_c_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_);
lean_dec(v_a_4294_);
lean_dec_ref(v_a_4293_);
lean_dec(v_a_4292_);
lean_dec_ref(v_a_4291_);
lean_dec(v_a_4290_);
lean_dec_ref(v_a_4289_);
lean_dec(v_a_4288_);
lean_dec_ref(v_a_4287_);
lean_dec(v_a_4286_);
lean_dec(v_a_4285_);
lean_dec(v_a_4284_);
lean_dec_ref(v_c_4283_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(lean_object* v_c_4297_){
_start:
{
lean_object* v_p_4299_; 
v_p_4299_ = lean_ctor_get(v_c_4297_, 0);
if (lean_obj_tag(v_p_4299_) == 1)
{
lean_object* v_k_4300_; lean_object* v___x_4301_; uint8_t v___x_4302_; 
v_k_4300_ = lean_ctor_get(v_p_4299_, 0);
v___x_4301_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_4302_ = lean_int_dec_lt(v_k_4300_, v___x_4301_);
if (v___x_4302_ == 0)
{
lean_object* v___x_4303_; 
v___x_4303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4303_, 0, v_c_4297_);
return v___x_4303_;
}
else
{
lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4304_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_4299_);
v___x_4305_ = l_Lean_Grind_Linarith_Poly_mul(v_p_4299_, v___x_4304_);
v___x_4306_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4306_, 0, v_c_4297_);
v___x_4307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4305_);
lean_ctor_set(v___x_4307_, 1, v___x_4306_);
v___x_4308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4307_);
return v___x_4308_;
}
}
else
{
lean_object* v___x_4309_; 
v___x_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4309_, 0, v_c_4297_);
return v___x_4309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg___boxed(lean_object* v_c_4310_, lean_object* v_a_4311_){
_start:
{
lean_object* v_res_4312_; 
v_res_4312_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4310_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(lean_object* v_c_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_){
_start:
{
lean_object* v___x_4326_; 
v___x_4326_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4313_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___boxed(lean_object* v_c_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(v_c_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_, v_a_4337_, v_a_4338_);
lean_dec(v_a_4338_);
lean_dec_ref(v_a_4337_);
lean_dec(v_a_4336_);
lean_dec_ref(v_a_4335_);
lean_dec(v_a_4334_);
lean_dec_ref(v_a_4333_);
lean_dec(v_a_4332_);
lean_dec_ref(v_a_4331_);
lean_dec(v_a_4330_);
lean_dec(v_a_4329_);
lean_dec(v_a_4328_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(lean_object* v___y_4341_, lean_object* v_snd_4342_, lean_object* v_fst_4343_, lean_object* v_s_4344_){
_start:
{
lean_object* v_structs_4345_; lean_object* v_typeIdOf_4346_; lean_object* v_exprToStructId_4347_; lean_object* v_exprToStructIdEntries_4348_; lean_object* v_forbiddenNatModules_4349_; lean_object* v_natStructs_4350_; lean_object* v_natTypeIdOf_4351_; lean_object* v_exprToNatStructId_4352_; lean_object* v___x_4353_; uint8_t v___x_4354_; 
v_structs_4345_ = lean_ctor_get(v_s_4344_, 0);
v_typeIdOf_4346_ = lean_ctor_get(v_s_4344_, 1);
v_exprToStructId_4347_ = lean_ctor_get(v_s_4344_, 2);
v_exprToStructIdEntries_4348_ = lean_ctor_get(v_s_4344_, 3);
v_forbiddenNatModules_4349_ = lean_ctor_get(v_s_4344_, 4);
v_natStructs_4350_ = lean_ctor_get(v_s_4344_, 5);
v_natTypeIdOf_4351_ = lean_ctor_get(v_s_4344_, 6);
v_exprToNatStructId_4352_ = lean_ctor_get(v_s_4344_, 7);
v___x_4353_ = lean_array_get_size(v_structs_4345_);
v___x_4354_ = lean_nat_dec_lt(v___y_4341_, v___x_4353_);
if (v___x_4354_ == 0)
{
lean_dec(v_fst_4343_);
lean_dec_ref(v_snd_4342_);
return v_s_4344_;
}
else
{
lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4418_; 
lean_inc_ref(v_exprToNatStructId_4352_);
lean_inc_ref(v_natTypeIdOf_4351_);
lean_inc_ref(v_natStructs_4350_);
lean_inc_ref(v_forbiddenNatModules_4349_);
lean_inc_ref(v_exprToStructIdEntries_4348_);
lean_inc_ref(v_exprToStructId_4347_);
lean_inc_ref(v_typeIdOf_4346_);
lean_inc_ref(v_structs_4345_);
v_isSharedCheck_4418_ = !lean_is_exclusive(v_s_4344_);
if (v_isSharedCheck_4418_ == 0)
{
lean_object* v_unused_4419_; lean_object* v_unused_4420_; lean_object* v_unused_4421_; lean_object* v_unused_4422_; lean_object* v_unused_4423_; lean_object* v_unused_4424_; lean_object* v_unused_4425_; lean_object* v_unused_4426_; 
v_unused_4419_ = lean_ctor_get(v_s_4344_, 7);
lean_dec(v_unused_4419_);
v_unused_4420_ = lean_ctor_get(v_s_4344_, 6);
lean_dec(v_unused_4420_);
v_unused_4421_ = lean_ctor_get(v_s_4344_, 5);
lean_dec(v_unused_4421_);
v_unused_4422_ = lean_ctor_get(v_s_4344_, 4);
lean_dec(v_unused_4422_);
v_unused_4423_ = lean_ctor_get(v_s_4344_, 3);
lean_dec(v_unused_4423_);
v_unused_4424_ = lean_ctor_get(v_s_4344_, 2);
lean_dec(v_unused_4424_);
v_unused_4425_ = lean_ctor_get(v_s_4344_, 1);
lean_dec(v_unused_4425_);
v_unused_4426_ = lean_ctor_get(v_s_4344_, 0);
lean_dec(v_unused_4426_);
v___x_4356_ = v_s_4344_;
v_isShared_4357_ = v_isSharedCheck_4418_;
goto v_resetjp_4355_;
}
else
{
lean_dec(v_s_4344_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4418_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v_v_4358_; lean_object* v_id_4359_; lean_object* v_ringId_x3f_4360_; lean_object* v_type_4361_; lean_object* v_u_4362_; lean_object* v_intModuleInst_4363_; lean_object* v_leInst_x3f_4364_; lean_object* v_ltInst_x3f_4365_; lean_object* v_lawfulOrderLTInst_x3f_4366_; lean_object* v_isPreorderInst_x3f_4367_; lean_object* v_orderedAddInst_x3f_4368_; lean_object* v_isLinearInst_x3f_4369_; lean_object* v_noNatDivInst_x3f_4370_; lean_object* v_ringInst_x3f_4371_; lean_object* v_commRingInst_x3f_4372_; lean_object* v_orderedRingInst_x3f_4373_; lean_object* v_fieldInst_x3f_4374_; lean_object* v_charInst_x3f_4375_; lean_object* v_zero_4376_; lean_object* v_ofNatZero_4377_; lean_object* v_one_x3f_4378_; lean_object* v_leFn_x3f_4379_; lean_object* v_ltFn_x3f_4380_; lean_object* v_addFn_4381_; lean_object* v_zsmulFn_4382_; lean_object* v_nsmulFn_4383_; lean_object* v_zsmulFn_x3f_4384_; lean_object* v_nsmulFn_x3f_4385_; lean_object* v_homomulFn_x3f_4386_; lean_object* v_subFn_4387_; lean_object* v_negFn_4388_; lean_object* v_vars_4389_; lean_object* v_varMap_4390_; lean_object* v_lowers_4391_; lean_object* v_uppers_4392_; lean_object* v_diseqs_4393_; lean_object* v_assignment_4394_; uint8_t v_caseSplits_4395_; lean_object* v_conflict_x3f_4396_; lean_object* v_diseqSplits_4397_; lean_object* v_elimEqs_4398_; lean_object* v_elimStack_4399_; lean_object* v_occurs_4400_; lean_object* v_ignored_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4417_; 
v_v_4358_ = lean_array_fget(v_structs_4345_, v___y_4341_);
v_id_4359_ = lean_ctor_get(v_v_4358_, 0);
v_ringId_x3f_4360_ = lean_ctor_get(v_v_4358_, 1);
v_type_4361_ = lean_ctor_get(v_v_4358_, 2);
v_u_4362_ = lean_ctor_get(v_v_4358_, 3);
v_intModuleInst_4363_ = lean_ctor_get(v_v_4358_, 4);
v_leInst_x3f_4364_ = lean_ctor_get(v_v_4358_, 5);
v_ltInst_x3f_4365_ = lean_ctor_get(v_v_4358_, 6);
v_lawfulOrderLTInst_x3f_4366_ = lean_ctor_get(v_v_4358_, 7);
v_isPreorderInst_x3f_4367_ = lean_ctor_get(v_v_4358_, 8);
v_orderedAddInst_x3f_4368_ = lean_ctor_get(v_v_4358_, 9);
v_isLinearInst_x3f_4369_ = lean_ctor_get(v_v_4358_, 10);
v_noNatDivInst_x3f_4370_ = lean_ctor_get(v_v_4358_, 11);
v_ringInst_x3f_4371_ = lean_ctor_get(v_v_4358_, 12);
v_commRingInst_x3f_4372_ = lean_ctor_get(v_v_4358_, 13);
v_orderedRingInst_x3f_4373_ = lean_ctor_get(v_v_4358_, 14);
v_fieldInst_x3f_4374_ = lean_ctor_get(v_v_4358_, 15);
v_charInst_x3f_4375_ = lean_ctor_get(v_v_4358_, 16);
v_zero_4376_ = lean_ctor_get(v_v_4358_, 17);
v_ofNatZero_4377_ = lean_ctor_get(v_v_4358_, 18);
v_one_x3f_4378_ = lean_ctor_get(v_v_4358_, 19);
v_leFn_x3f_4379_ = lean_ctor_get(v_v_4358_, 20);
v_ltFn_x3f_4380_ = lean_ctor_get(v_v_4358_, 21);
v_addFn_4381_ = lean_ctor_get(v_v_4358_, 22);
v_zsmulFn_4382_ = lean_ctor_get(v_v_4358_, 23);
v_nsmulFn_4383_ = lean_ctor_get(v_v_4358_, 24);
v_zsmulFn_x3f_4384_ = lean_ctor_get(v_v_4358_, 25);
v_nsmulFn_x3f_4385_ = lean_ctor_get(v_v_4358_, 26);
v_homomulFn_x3f_4386_ = lean_ctor_get(v_v_4358_, 27);
v_subFn_4387_ = lean_ctor_get(v_v_4358_, 28);
v_negFn_4388_ = lean_ctor_get(v_v_4358_, 29);
v_vars_4389_ = lean_ctor_get(v_v_4358_, 30);
v_varMap_4390_ = lean_ctor_get(v_v_4358_, 31);
v_lowers_4391_ = lean_ctor_get(v_v_4358_, 32);
v_uppers_4392_ = lean_ctor_get(v_v_4358_, 33);
v_diseqs_4393_ = lean_ctor_get(v_v_4358_, 34);
v_assignment_4394_ = lean_ctor_get(v_v_4358_, 35);
v_caseSplits_4395_ = lean_ctor_get_uint8(v_v_4358_, sizeof(void*)*42);
v_conflict_x3f_4396_ = lean_ctor_get(v_v_4358_, 36);
v_diseqSplits_4397_ = lean_ctor_get(v_v_4358_, 37);
v_elimEqs_4398_ = lean_ctor_get(v_v_4358_, 38);
v_elimStack_4399_ = lean_ctor_get(v_v_4358_, 39);
v_occurs_4400_ = lean_ctor_get(v_v_4358_, 40);
v_ignored_4401_ = lean_ctor_get(v_v_4358_, 41);
v_isSharedCheck_4417_ = !lean_is_exclusive(v_v_4358_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4403_ = v_v_4358_;
v_isShared_4404_ = v_isSharedCheck_4417_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_ignored_4401_);
lean_inc(v_occurs_4400_);
lean_inc(v_elimStack_4399_);
lean_inc(v_elimEqs_4398_);
lean_inc(v_diseqSplits_4397_);
lean_inc(v_conflict_x3f_4396_);
lean_inc(v_assignment_4394_);
lean_inc(v_diseqs_4393_);
lean_inc(v_uppers_4392_);
lean_inc(v_lowers_4391_);
lean_inc(v_varMap_4390_);
lean_inc(v_vars_4389_);
lean_inc(v_negFn_4388_);
lean_inc(v_subFn_4387_);
lean_inc(v_homomulFn_x3f_4386_);
lean_inc(v_nsmulFn_x3f_4385_);
lean_inc(v_zsmulFn_x3f_4384_);
lean_inc(v_nsmulFn_4383_);
lean_inc(v_zsmulFn_4382_);
lean_inc(v_addFn_4381_);
lean_inc(v_ltFn_x3f_4380_);
lean_inc(v_leFn_x3f_4379_);
lean_inc(v_one_x3f_4378_);
lean_inc(v_ofNatZero_4377_);
lean_inc(v_zero_4376_);
lean_inc(v_charInst_x3f_4375_);
lean_inc(v_fieldInst_x3f_4374_);
lean_inc(v_orderedRingInst_x3f_4373_);
lean_inc(v_commRingInst_x3f_4372_);
lean_inc(v_ringInst_x3f_4371_);
lean_inc(v_noNatDivInst_x3f_4370_);
lean_inc(v_isLinearInst_x3f_4369_);
lean_inc(v_orderedAddInst_x3f_4368_);
lean_inc(v_isPreorderInst_x3f_4367_);
lean_inc(v_lawfulOrderLTInst_x3f_4366_);
lean_inc(v_ltInst_x3f_4365_);
lean_inc(v_leInst_x3f_4364_);
lean_inc(v_intModuleInst_4363_);
lean_inc(v_u_4362_);
lean_inc(v_type_4361_);
lean_inc(v_ringId_x3f_4360_);
lean_inc(v_id_4359_);
lean_dec(v_v_4358_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4417_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4405_; lean_object* v_xs_x27_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4411_; 
v___x_4405_ = lean_box(0);
v_xs_x27_4406_ = lean_array_fset(v_structs_4345_, v___y_4341_, v___x_4405_);
v___x_4407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4407_, 0, v_snd_4342_);
v___x_4408_ = l_Lean_PersistentArray_set___redArg(v_elimEqs_4398_, v_fst_4343_, v___x_4407_);
v___x_4409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4409_, 0, v_fst_4343_);
lean_ctor_set(v___x_4409_, 1, v_elimStack_4399_);
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 39, v___x_4409_);
lean_ctor_set(v___x_4403_, 38, v___x_4408_);
v___x_4411_ = v___x_4403_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_id_4359_);
lean_ctor_set(v_reuseFailAlloc_4416_, 1, v_ringId_x3f_4360_);
lean_ctor_set(v_reuseFailAlloc_4416_, 2, v_type_4361_);
lean_ctor_set(v_reuseFailAlloc_4416_, 3, v_u_4362_);
lean_ctor_set(v_reuseFailAlloc_4416_, 4, v_intModuleInst_4363_);
lean_ctor_set(v_reuseFailAlloc_4416_, 5, v_leInst_x3f_4364_);
lean_ctor_set(v_reuseFailAlloc_4416_, 6, v_ltInst_x3f_4365_);
lean_ctor_set(v_reuseFailAlloc_4416_, 7, v_lawfulOrderLTInst_x3f_4366_);
lean_ctor_set(v_reuseFailAlloc_4416_, 8, v_isPreorderInst_x3f_4367_);
lean_ctor_set(v_reuseFailAlloc_4416_, 9, v_orderedAddInst_x3f_4368_);
lean_ctor_set(v_reuseFailAlloc_4416_, 10, v_isLinearInst_x3f_4369_);
lean_ctor_set(v_reuseFailAlloc_4416_, 11, v_noNatDivInst_x3f_4370_);
lean_ctor_set(v_reuseFailAlloc_4416_, 12, v_ringInst_x3f_4371_);
lean_ctor_set(v_reuseFailAlloc_4416_, 13, v_commRingInst_x3f_4372_);
lean_ctor_set(v_reuseFailAlloc_4416_, 14, v_orderedRingInst_x3f_4373_);
lean_ctor_set(v_reuseFailAlloc_4416_, 15, v_fieldInst_x3f_4374_);
lean_ctor_set(v_reuseFailAlloc_4416_, 16, v_charInst_x3f_4375_);
lean_ctor_set(v_reuseFailAlloc_4416_, 17, v_zero_4376_);
lean_ctor_set(v_reuseFailAlloc_4416_, 18, v_ofNatZero_4377_);
lean_ctor_set(v_reuseFailAlloc_4416_, 19, v_one_x3f_4378_);
lean_ctor_set(v_reuseFailAlloc_4416_, 20, v_leFn_x3f_4379_);
lean_ctor_set(v_reuseFailAlloc_4416_, 21, v_ltFn_x3f_4380_);
lean_ctor_set(v_reuseFailAlloc_4416_, 22, v_addFn_4381_);
lean_ctor_set(v_reuseFailAlloc_4416_, 23, v_zsmulFn_4382_);
lean_ctor_set(v_reuseFailAlloc_4416_, 24, v_nsmulFn_4383_);
lean_ctor_set(v_reuseFailAlloc_4416_, 25, v_zsmulFn_x3f_4384_);
lean_ctor_set(v_reuseFailAlloc_4416_, 26, v_nsmulFn_x3f_4385_);
lean_ctor_set(v_reuseFailAlloc_4416_, 27, v_homomulFn_x3f_4386_);
lean_ctor_set(v_reuseFailAlloc_4416_, 28, v_subFn_4387_);
lean_ctor_set(v_reuseFailAlloc_4416_, 29, v_negFn_4388_);
lean_ctor_set(v_reuseFailAlloc_4416_, 30, v_vars_4389_);
lean_ctor_set(v_reuseFailAlloc_4416_, 31, v_varMap_4390_);
lean_ctor_set(v_reuseFailAlloc_4416_, 32, v_lowers_4391_);
lean_ctor_set(v_reuseFailAlloc_4416_, 33, v_uppers_4392_);
lean_ctor_set(v_reuseFailAlloc_4416_, 34, v_diseqs_4393_);
lean_ctor_set(v_reuseFailAlloc_4416_, 35, v_assignment_4394_);
lean_ctor_set(v_reuseFailAlloc_4416_, 36, v_conflict_x3f_4396_);
lean_ctor_set(v_reuseFailAlloc_4416_, 37, v_diseqSplits_4397_);
lean_ctor_set(v_reuseFailAlloc_4416_, 38, v___x_4408_);
lean_ctor_set(v_reuseFailAlloc_4416_, 39, v___x_4409_);
lean_ctor_set(v_reuseFailAlloc_4416_, 40, v_occurs_4400_);
lean_ctor_set(v_reuseFailAlloc_4416_, 41, v_ignored_4401_);
lean_ctor_set_uint8(v_reuseFailAlloc_4416_, sizeof(void*)*42, v_caseSplits_4395_);
v___x_4411_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
lean_object* v___x_4412_; lean_object* v___x_4414_; 
v___x_4412_ = lean_array_fset(v_xs_x27_4406_, v___y_4341_, v___x_4411_);
if (v_isShared_4357_ == 0)
{
lean_ctor_set(v___x_4356_, 0, v___x_4412_);
v___x_4414_ = v___x_4356_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v___x_4412_);
lean_ctor_set(v_reuseFailAlloc_4415_, 1, v_typeIdOf_4346_);
lean_ctor_set(v_reuseFailAlloc_4415_, 2, v_exprToStructId_4347_);
lean_ctor_set(v_reuseFailAlloc_4415_, 3, v_exprToStructIdEntries_4348_);
lean_ctor_set(v_reuseFailAlloc_4415_, 4, v_forbiddenNatModules_4349_);
lean_ctor_set(v_reuseFailAlloc_4415_, 5, v_natStructs_4350_);
lean_ctor_set(v_reuseFailAlloc_4415_, 6, v_natTypeIdOf_4351_);
lean_ctor_set(v_reuseFailAlloc_4415_, 7, v_exprToNatStructId_4352_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed(lean_object* v___y_4427_, lean_object* v_snd_4428_, lean_object* v_fst_4429_, lean_object* v_s_4430_){
_start:
{
lean_object* v_res_4431_; 
v_res_4431_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(v___y_4427_, v_snd_4428_, v_fst_4429_, v_s_4430_);
lean_dec(v___y_4427_);
return v_res_4431_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1(void){
_start:
{
lean_object* v___x_4433_; lean_object* v___x_4434_; 
v___x_4433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0));
v___x_4434_ = l_Lean_stringToMessageData(v___x_4433_);
return v___x_4434_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4(void){
_start:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4440_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4442_ = l_Lean_Name_append(v___x_4441_, v___x_4440_);
return v___x_4442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object* v_c_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_){
_start:
{
lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4492_; lean_object* v___y_4493_; lean_object* v___y_4494_; lean_object* v___y_4495_; lean_object* v___y_4496_; lean_object* v_options_4522_; lean_object* v_inheritedTraceOptions_4523_; uint8_t v_hasTrace_4524_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v_options_4541_; lean_object* v_inheritedTraceOptions_4542_; lean_object* v___y_4543_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v___y_4570_; 
v_options_4522_ = lean_ctor_get(v_a_4453_, 2);
v_inheritedTraceOptions_4523_ = lean_ctor_get(v_a_4453_, 13);
v_hasTrace_4524_ = lean_ctor_get_uint8(v_options_4522_, sizeof(void*)*1);
if (v_hasTrace_4524_ == 0)
{
v___y_4560_ = v_a_4444_;
v___y_4561_ = v_a_4445_;
v___y_4562_ = v_a_4446_;
v___y_4563_ = v_a_4447_;
v___y_4564_ = v_a_4448_;
v___y_4565_ = v_a_4449_;
v___y_4566_ = v_a_4450_;
v___y_4567_ = v_a_4451_;
v___y_4568_ = v_a_4452_;
v___y_4569_ = v_a_4453_;
v___y_4570_ = v_a_4454_;
goto v___jp_4559_;
}
else
{
lean_object* v_cls_4666_; lean_object* v___x_4667_; uint8_t v___x_4668_; 
v_cls_4666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_4667_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_4668_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4523_, v_options_4522_, v___x_4667_);
if (v___x_4668_ == 0)
{
v___y_4560_ = v_a_4444_;
v___y_4561_ = v_a_4445_;
v___y_4562_ = v_a_4446_;
v___y_4563_ = v_a_4447_;
v___y_4564_ = v_a_4448_;
v___y_4565_ = v_a_4449_;
v___y_4566_ = v_a_4450_;
v___y_4567_ = v_a_4451_;
v___y_4568_ = v_a_4452_;
v___y_4569_ = v_a_4453_;
v___y_4570_ = v_a_4454_;
goto v___jp_4559_;
}
else
{
lean_object* v___x_4669_; 
v___x_4669_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_4443_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
if (lean_obj_tag(v___x_4669_) == 0)
{
lean_object* v_a_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
v_a_4670_ = lean_ctor_get(v___x_4669_, 0);
lean_inc(v_a_4670_);
lean_dec_ref(v___x_4669_);
v___x_4671_ = l_Lean_MessageData_ofExpr(v_a_4670_);
v___x_4672_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4666_, v___x_4671_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
if (lean_obj_tag(v___x_4672_) == 0)
{
lean_dec_ref(v___x_4672_);
v___y_4560_ = v_a_4444_;
v___y_4561_ = v_a_4445_;
v___y_4562_ = v_a_4446_;
v___y_4563_ = v_a_4447_;
v___y_4564_ = v_a_4448_;
v___y_4565_ = v_a_4449_;
v___y_4566_ = v_a_4450_;
v___y_4567_ = v_a_4451_;
v___y_4568_ = v_a_4452_;
v___y_4569_ = v_a_4453_;
v___y_4570_ = v_a_4454_;
goto v___jp_4559_;
}
else
{
lean_dec_ref(v_c_4443_);
return v___x_4672_;
}
}
else
{
lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4680_; 
lean_dec_ref(v_c_4443_);
v_a_4673_ = lean_ctor_get(v___x_4669_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4669_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4675_ = v___x_4669_;
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_a_4673_);
lean_dec(v___x_4669_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4678_; 
if (v_isShared_4676_ == 0)
{
v___x_4678_ = v___x_4675_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v_a_4673_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
}
}
}
v___jp_4456_:
{
lean_object* v___x_4457_; lean_object* v___x_4458_; 
v___x_4457_ = lean_box(0);
v___x_4458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4458_, 0, v___x_4457_);
return v___x_4458_;
}
v___jp_4459_:
{
lean_object* v___f_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; 
lean_inc(v___y_4465_);
v___f_4476_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4476_, 0, v___y_4465_);
lean_closure_set(v___f_4476_, 1, v___y_4460_);
lean_closure_set(v___f_4476_, 2, v___y_4461_);
v___x_4477_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4478_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4477_, v___f_4476_, v___y_4466_);
if (lean_obj_tag(v___x_4478_) == 0)
{
lean_object* v___x_4479_; 
lean_dec_ref(v___x_4478_);
v___x_4479_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v___y_4463_, v___y_4464_, v___y_4462_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
return v___x_4479_;
}
else
{
lean_dec(v___y_4464_);
lean_dec(v___y_4463_);
lean_dec_ref(v___y_4462_);
return v___x_4478_;
}
}
v___jp_4480_:
{
lean_object* v___x_4497_; 
v___x_4497_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_object* v_a_4498_; uint8_t v_caseSplits_4499_; 
v_a_4498_ = lean_ctor_get(v___x_4497_, 0);
lean_inc(v_a_4498_);
lean_dec_ref(v___x_4497_);
v_caseSplits_4499_ = lean_ctor_get_uint8(v_a_4498_, sizeof(void*)*42);
lean_dec(v_a_4498_);
if (v_caseSplits_4499_ == 0)
{
lean_object* v___x_4500_; 
v___x_4500_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v___y_4483_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
if (lean_obj_tag(v___x_4500_) == 0)
{
lean_object* v_a_4501_; uint8_t v___x_4502_; 
v_a_4501_ = lean_ctor_get(v___x_4500_, 0);
lean_inc(v_a_4501_);
lean_dec_ref(v___x_4500_);
v___x_4502_ = lean_unbox(v_a_4501_);
lean_dec(v_a_4501_);
if (v___x_4502_ == 0)
{
v___y_4460_ = v___y_4481_;
v___y_4461_ = v___y_4482_;
v___y_4462_ = v___y_4483_;
v___y_4463_ = v___y_4484_;
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
goto v___jp_4459_;
}
else
{
lean_object* v___x_4503_; lean_object* v_a_4504_; lean_object* v___x_4505_; 
lean_inc_ref(v___y_4483_);
v___x_4503_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v___y_4483_);
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
lean_inc(v_a_4504_);
lean_dec_ref(v___x_4503_);
v___x_4505_ = l_Lean_Meta_Grind_Arith_Linear_propagateImpEq(v_a_4504_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
if (lean_obj_tag(v___x_4505_) == 0)
{
lean_dec_ref(v___x_4505_);
v___y_4460_ = v___y_4481_;
v___y_4461_ = v___y_4482_;
v___y_4462_ = v___y_4483_;
v___y_4463_ = v___y_4484_;
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
goto v___jp_4459_;
}
else
{
lean_dec(v___y_4485_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
return v___x_4505_;
}
}
}
else
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_dec(v___y_4485_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
v_a_4506_ = lean_ctor_get(v___x_4500_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4500_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4500_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4500_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
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
else
{
v___y_4460_ = v___y_4481_;
v___y_4461_ = v___y_4482_;
v___y_4462_ = v___y_4483_;
v___y_4463_ = v___y_4484_;
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
goto v___jp_4459_;
}
}
else
{
lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4521_; 
lean_dec(v___y_4485_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
v_a_4514_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4516_ = v___x_4497_;
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v___x_4497_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4519_; 
if (v_isShared_4517_ == 0)
{
v___x_4519_ = v___x_4516_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4514_);
v___x_4519_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
return v___x_4519_;
}
}
}
}
v___jp_4525_:
{
lean_object* v___x_4544_; lean_object* v___x_4545_; uint8_t v___x_4546_; 
v___x_4544_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_4545_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_4546_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4542_, v_options_4541_, v___x_4545_);
if (v___x_4546_ == 0)
{
v___y_4481_ = v___y_4526_;
v___y_4482_ = v___y_4527_;
v___y_4483_ = v___y_4528_;
v___y_4484_ = v___y_4529_;
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
v___y_4496_ = v___y_4543_;
goto v___jp_4480_;
}
else
{
lean_object* v___x_4547_; 
v___x_4547_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v___y_4528_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4543_);
if (lean_obj_tag(v___x_4547_) == 0)
{
lean_object* v_a_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; 
v_a_4548_ = lean_ctor_get(v___x_4547_, 0);
lean_inc(v_a_4548_);
lean_dec_ref(v___x_4547_);
v___x_4549_ = l_Lean_MessageData_ofExpr(v_a_4548_);
v___x_4550_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4544_, v___x_4549_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4543_);
if (lean_obj_tag(v___x_4550_) == 0)
{
lean_dec_ref(v___x_4550_);
v___y_4481_ = v___y_4526_;
v___y_4482_ = v___y_4527_;
v___y_4483_ = v___y_4528_;
v___y_4484_ = v___y_4529_;
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
v___y_4496_ = v___y_4543_;
goto v___jp_4480_;
}
else
{
lean_dec(v___y_4530_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
lean_dec(v___y_4527_);
lean_dec_ref(v___y_4526_);
return v___x_4550_;
}
}
else
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4558_; 
lean_dec(v___y_4530_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
lean_dec(v___y_4527_);
lean_dec_ref(v___y_4526_);
v_a_4551_ = lean_ctor_get(v___x_4547_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4547_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4553_ = v___x_4547_;
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4547_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4554_ == 0)
{
v___x_4556_ = v___x_4553_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4551_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
}
}
v___jp_4559_:
{
lean_object* v___x_4571_; 
lean_inc_ref(v___y_4569_);
v___x_4571_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_4443_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_);
if (lean_obj_tag(v___x_4571_) == 0)
{
lean_object* v_a_4572_; lean_object* v_p_4573_; lean_object* v___x_4574_; uint8_t v___x_4575_; 
v_a_4572_ = lean_ctor_get(v___x_4571_, 0);
lean_inc(v_a_4572_);
lean_dec_ref(v___x_4571_);
v_p_4573_ = lean_ctor_get(v_a_4572_, 0);
v___x_4574_ = lean_box(0);
v___x_4575_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_4573_, v___x_4574_);
if (v___x_4575_ == 0)
{
lean_object* v___x_4576_; 
v___x_4576_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_a_4572_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_);
if (lean_obj_tag(v___x_4576_) == 0)
{
lean_object* v_a_4577_; lean_object* v_snd_4578_; lean_object* v_options_4579_; uint8_t v_hasTrace_4580_; 
v_a_4577_ = lean_ctor_get(v___x_4576_, 0);
lean_inc(v_a_4577_);
lean_dec_ref(v___x_4576_);
v_snd_4578_ = lean_ctor_get(v_a_4577_, 1);
lean_inc(v_snd_4578_);
v_options_4579_ = lean_ctor_get(v___y_4569_, 2);
v_hasTrace_4580_ = lean_ctor_get_uint8(v_options_4579_, sizeof(void*)*1);
if (v_hasTrace_4580_ == 0)
{
lean_object* v_fst_4581_; lean_object* v_fst_4582_; lean_object* v_snd_4583_; 
v_fst_4581_ = lean_ctor_get(v_a_4577_, 0);
lean_inc(v_fst_4581_);
lean_dec(v_a_4577_);
v_fst_4582_ = lean_ctor_get(v_snd_4578_, 0);
lean_inc_n(v_fst_4582_, 2);
v_snd_4583_ = lean_ctor_get(v_snd_4578_, 1);
lean_inc_n(v_snd_4583_, 2);
lean_dec(v_snd_4578_);
v___y_4481_ = v_snd_4583_;
v___y_4482_ = v_fst_4582_;
v___y_4483_ = v_snd_4583_;
v___y_4484_ = v_fst_4581_;
v___y_4485_ = v_fst_4582_;
v___y_4486_ = v___y_4560_;
v___y_4487_ = v___y_4561_;
v___y_4488_ = v___y_4562_;
v___y_4489_ = v___y_4563_;
v___y_4490_ = v___y_4564_;
v___y_4491_ = v___y_4565_;
v___y_4492_ = v___y_4566_;
v___y_4493_ = v___y_4567_;
v___y_4494_ = v___y_4568_;
v___y_4495_ = v___y_4569_;
v___y_4496_ = v___y_4570_;
goto v___jp_4480_;
}
else
{
lean_object* v_fst_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4630_; 
v_fst_4584_ = lean_ctor_get(v_a_4577_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v_a_4577_);
if (v_isSharedCheck_4630_ == 0)
{
lean_object* v_unused_4631_; 
v_unused_4631_ = lean_ctor_get(v_a_4577_, 1);
lean_dec(v_unused_4631_);
v___x_4586_ = v_a_4577_;
v_isShared_4587_ = v_isSharedCheck_4630_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_fst_4584_);
lean_dec(v_a_4577_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4630_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v_fst_4588_; lean_object* v_snd_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4629_; 
v_fst_4588_ = lean_ctor_get(v_snd_4578_, 0);
v_snd_4589_ = lean_ctor_get(v_snd_4578_, 1);
v_isSharedCheck_4629_ = !lean_is_exclusive(v_snd_4578_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4591_ = v_snd_4578_;
v_isShared_4592_ = v_isSharedCheck_4629_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_snd_4589_);
lean_inc(v_fst_4588_);
lean_dec(v_snd_4578_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4629_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v_inheritedTraceOptions_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; uint8_t v___x_4596_; 
v_inheritedTraceOptions_4593_ = lean_ctor_get(v___y_4569_, 13);
v___x_4594_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_4595_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_4596_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4593_, v_options_4579_, v___x_4595_);
if (v___x_4596_ == 0)
{
lean_del_object(v___x_4591_);
lean_del_object(v___x_4586_);
lean_inc(v_fst_4588_);
lean_inc(v_snd_4589_);
v___y_4526_ = v_snd_4589_;
v___y_4527_ = v_fst_4588_;
v___y_4528_ = v_snd_4589_;
v___y_4529_ = v_fst_4584_;
v___y_4530_ = v_fst_4588_;
v___y_4531_ = v___y_4560_;
v___y_4532_ = v___y_4561_;
v___y_4533_ = v___y_4562_;
v___y_4534_ = v___y_4563_;
v___y_4535_ = v___y_4564_;
v___y_4536_ = v___y_4565_;
v___y_4537_ = v___y_4566_;
v___y_4538_ = v___y_4567_;
v___y_4539_ = v___y_4568_;
v___y_4540_ = v___y_4569_;
v_options_4541_ = v_options_4579_;
v_inheritedTraceOptions_4542_ = v_inheritedTraceOptions_4593_;
v___y_4543_ = v___y_4570_;
goto v___jp_4525_;
}
else
{
lean_object* v___x_4597_; 
v___x_4597_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_4588_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_);
if (lean_obj_tag(v___x_4597_) == 0)
{
lean_object* v_a_4598_; lean_object* v___x_4599_; 
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
lean_inc(v_a_4598_);
lean_dec_ref(v___x_4597_);
v___x_4599_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_4589_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_);
if (lean_obj_tag(v___x_4599_) == 0)
{
lean_object* v_a_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4604_; 
v_a_4600_ = lean_ctor_get(v___x_4599_, 0);
lean_inc(v_a_4600_);
lean_dec_ref(v___x_4599_);
v___x_4601_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1);
v___x_4602_ = l_Lean_MessageData_ofExpr(v_a_4598_);
if (v_isShared_4592_ == 0)
{
lean_ctor_set_tag(v___x_4591_, 7);
lean_ctor_set(v___x_4591_, 1, v___x_4602_);
lean_ctor_set(v___x_4591_, 0, v___x_4601_);
v___x_4604_ = v___x_4591_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4601_);
lean_ctor_set(v_reuseFailAlloc_4612_, 1, v___x_4602_);
v___x_4604_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
lean_object* v___x_4605_; lean_object* v___x_4607_; 
v___x_4605_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_4587_ == 0)
{
lean_ctor_set_tag(v___x_4586_, 7);
lean_ctor_set(v___x_4586_, 1, v___x_4605_);
lean_ctor_set(v___x_4586_, 0, v___x_4604_);
v___x_4607_ = v___x_4586_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v___x_4604_);
lean_ctor_set(v_reuseFailAlloc_4611_, 1, v___x_4605_);
v___x_4607_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; 
v___x_4608_ = l_Lean_MessageData_ofExpr(v_a_4600_);
v___x_4609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4609_, 0, v___x_4607_);
lean_ctor_set(v___x_4609_, 1, v___x_4608_);
v___x_4610_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4594_, v___x_4609_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_);
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_dec_ref(v___x_4610_);
lean_inc(v_fst_4588_);
lean_inc(v_snd_4589_);
v___y_4526_ = v_snd_4589_;
v___y_4527_ = v_fst_4588_;
v___y_4528_ = v_snd_4589_;
v___y_4529_ = v_fst_4584_;
v___y_4530_ = v_fst_4588_;
v___y_4531_ = v___y_4560_;
v___y_4532_ = v___y_4561_;
v___y_4533_ = v___y_4562_;
v___y_4534_ = v___y_4563_;
v___y_4535_ = v___y_4564_;
v___y_4536_ = v___y_4565_;
v___y_4537_ = v___y_4566_;
v___y_4538_ = v___y_4567_;
v___y_4539_ = v___y_4568_;
v___y_4540_ = v___y_4569_;
v_options_4541_ = v_options_4579_;
v_inheritedTraceOptions_4542_ = v_inheritedTraceOptions_4593_;
v___y_4543_ = v___y_4570_;
goto v___jp_4525_;
}
else
{
lean_dec(v_snd_4589_);
lean_dec(v_fst_4588_);
lean_dec(v_fst_4584_);
return v___x_4610_;
}
}
}
}
else
{
lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4620_; 
lean_dec(v_a_4598_);
lean_del_object(v___x_4591_);
lean_dec(v_snd_4589_);
lean_dec(v_fst_4588_);
lean_del_object(v___x_4586_);
lean_dec(v_fst_4584_);
v_a_4613_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4620_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4620_ == 0)
{
v___x_4615_ = v___x_4599_;
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v___x_4599_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4618_; 
if (v_isShared_4616_ == 0)
{
v___x_4618_ = v___x_4615_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_a_4613_);
v___x_4618_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
return v___x_4618_;
}
}
}
}
else
{
lean_object* v_a_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4628_; 
lean_del_object(v___x_4591_);
lean_dec(v_snd_4589_);
lean_dec(v_fst_4588_);
lean_del_object(v___x_4586_);
lean_dec(v_fst_4584_);
v_a_4621_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4623_ = v___x_4597_;
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_a_4621_);
lean_dec(v___x_4597_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v___x_4626_; 
if (v_isShared_4624_ == 0)
{
v___x_4626_ = v___x_4623_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_a_4621_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
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
lean_object* v_a_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4639_; 
v_a_4632_ = lean_ctor_get(v___x_4576_, 0);
v_isSharedCheck_4639_ = !lean_is_exclusive(v___x_4576_);
if (v_isSharedCheck_4639_ == 0)
{
v___x_4634_ = v___x_4576_;
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_a_4632_);
lean_dec(v___x_4576_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v___x_4637_; 
if (v_isShared_4635_ == 0)
{
v___x_4637_ = v___x_4634_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_a_4632_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
return v___x_4637_;
}
}
}
}
else
{
lean_object* v_options_4640_; uint8_t v_hasTrace_4641_; 
v_options_4640_ = lean_ctor_get(v___y_4569_, 2);
v_hasTrace_4641_ = lean_ctor_get_uint8(v_options_4640_, sizeof(void*)*1);
if (v_hasTrace_4641_ == 0)
{
lean_dec(v_a_4572_);
goto v___jp_4456_;
}
else
{
lean_object* v_inheritedTraceOptions_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; uint8_t v___x_4645_; 
v_inheritedTraceOptions_4642_ = lean_ctor_get(v___y_4569_, 13);
v___x_4643_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4644_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4);
v___x_4645_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4642_, v_options_4640_, v___x_4644_);
if (v___x_4645_ == 0)
{
lean_dec(v_a_4572_);
goto v___jp_4456_;
}
else
{
lean_object* v___x_4646_; 
v___x_4646_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_a_4572_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_);
lean_dec(v_a_4572_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v_a_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v_a_4647_ = lean_ctor_get(v___x_4646_, 0);
lean_inc(v_a_4647_);
lean_dec_ref(v___x_4646_);
v___x_4648_ = l_Lean_MessageData_ofExpr(v_a_4647_);
v___x_4649_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4643_, v___x_4648_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_);
if (lean_obj_tag(v___x_4649_) == 0)
{
lean_dec_ref(v___x_4649_);
goto v___jp_4456_;
}
else
{
return v___x_4649_;
}
}
else
{
lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4657_; 
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
}
}
else
{
lean_object* v_a_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4665_; 
v_a_4658_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4665_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4665_ == 0)
{
v___x_4660_ = v___x_4571_;
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_a_4658_);
lean_dec(v___x_4571_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4663_; 
if (v_isShared_4661_ == 0)
{
v___x_4663_ = v___x_4660_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_a_4658_);
v___x_4663_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
return v___x_4663_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object* v_c_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_){
_start:
{
lean_object* v_res_4694_; 
v_res_4694_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v_c_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_);
lean_dec(v_a_4692_);
lean_dec_ref(v_a_4691_);
lean_dec(v_a_4690_);
lean_dec_ref(v_a_4689_);
lean_dec(v_a_4688_);
lean_dec_ref(v_a_4687_);
lean_dec(v_a_4686_);
lean_dec_ref(v_a_4685_);
lean_dec(v_a_4684_);
lean_dec(v_a_4683_);
lean_dec(v_a_4682_);
return v_res_4694_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2(void){
_start:
{
lean_object* v_cls_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; 
v_cls_4699_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4700_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4701_ = l_Lean_Name_append(v___x_4700_, v_cls_4699_);
return v___x_4701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object* v_a_4702_, lean_object* v_b_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_){
_start:
{
lean_object* v_options_4712_; uint8_t v_hasTrace_4713_; 
v_options_4712_ = lean_ctor_get(v_a_4706_, 2);
v_hasTrace_4713_ = lean_ctor_get_uint8(v_options_4712_, sizeof(void*)*1);
if (v_hasTrace_4713_ == 0)
{
lean_dec_ref(v_b_4703_);
lean_dec_ref(v_a_4702_);
goto v___jp_4709_;
}
else
{
lean_object* v_inheritedTraceOptions_4714_; lean_object* v_cls_4715_; lean_object* v___x_4716_; uint8_t v___x_4717_; 
v_inheritedTraceOptions_4714_ = lean_ctor_get(v_a_4706_, 13);
v_cls_4715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4716_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2);
v___x_4717_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4714_, v_options_4712_, v___x_4716_);
if (v___x_4717_ == 0)
{
lean_dec_ref(v_b_4703_);
lean_dec_ref(v_a_4702_);
goto v___jp_4709_;
}
else
{
lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4718_ = l_Lean_MessageData_ofExpr(v_a_4702_);
v___x_4719_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_4720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4720_, 0, v___x_4718_);
lean_ctor_set(v___x_4720_, 1, v___x_4719_);
v___x_4721_ = l_Lean_MessageData_ofExpr(v_b_4703_);
v___x_4722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4722_, 0, v___x_4720_);
lean_ctor_set(v___x_4722_, 1, v___x_4721_);
v___x_4723_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4715_, v___x_4722_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_);
return v___x_4723_;
}
}
v___jp_4709_:
{
lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4710_ = lean_box(0);
v___x_4711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4711_, 0, v___x_4710_);
return v___x_4711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object* v_a_4724_, lean_object* v_b_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4724_, v_b_4725_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_);
lean_dec(v_a_4729_);
lean_dec_ref(v_a_4728_);
lean_dec(v_a_4727_);
lean_dec_ref(v_a_4726_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object* v_a_4732_, lean_object* v_b_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_){
_start:
{
lean_object* v___x_4746_; 
v___x_4746_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4732_, v_b_4733_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object* v_a_4747_, lean_object* v_b_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_){
_start:
{
lean_object* v_res_4761_; 
v_res_4761_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(v_a_4747_, v_b_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_);
lean_dec(v_a_4759_);
lean_dec_ref(v_a_4758_);
lean_dec(v_a_4757_);
lean_dec_ref(v_a_4756_);
lean_dec(v_a_4755_);
lean_dec_ref(v_a_4754_);
lean_dec(v_a_4753_);
lean_dec_ref(v_a_4752_);
lean_dec(v_a_4751_);
lean_dec(v_a_4750_);
lean_dec(v_a_4749_);
return v_res_4761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object* v_a_4762_, lean_object* v_b_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_){
_start:
{
lean_object* v___x_4776_; 
v___x_4776_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4762_, v_a_4765_);
if (lean_obj_tag(v___x_4776_) == 0)
{
lean_object* v_a_4777_; uint8_t v___x_4778_; lean_object* v___x_4779_; 
v_a_4777_ = lean_ctor_get(v___x_4776_, 0);
lean_inc(v_a_4777_);
lean_dec_ref(v___x_4776_);
v___x_4778_ = 0;
lean_inc_ref(v_a_4762_);
v___x_4779_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_4762_, v___x_4778_, v_a_4777_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_);
if (lean_obj_tag(v___x_4779_) == 0)
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4829_; 
v_a_4780_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4782_ = v___x_4779_;
v_isShared_4783_ = v_isSharedCheck_4829_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v___x_4779_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4829_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
if (lean_obj_tag(v_a_4780_) == 1)
{
lean_object* v_val_4784_; lean_object* v___x_4785_; 
lean_del_object(v___x_4782_);
v_val_4784_ = lean_ctor_get(v_a_4780_, 0);
lean_inc(v_val_4784_);
lean_dec_ref(v_a_4780_);
v___x_4785_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4763_, v_a_4765_);
if (lean_obj_tag(v___x_4785_) == 0)
{
lean_object* v_a_4786_; lean_object* v___x_4787_; 
v_a_4786_ = lean_ctor_get(v___x_4785_, 0);
lean_inc(v_a_4786_);
lean_dec_ref(v___x_4785_);
lean_inc_ref(v_b_4763_);
v___x_4787_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_4763_, v___x_4778_, v_a_4786_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_);
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_object* v_a_4788_; lean_object* v___x_4790_; uint8_t v_isShared_4791_; uint8_t v_isSharedCheck_4808_; 
v_a_4788_ = lean_ctor_get(v___x_4787_, 0);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4790_ = v___x_4787_;
v_isShared_4791_ = v_isSharedCheck_4808_;
goto v_resetjp_4789_;
}
else
{
lean_inc(v_a_4788_);
lean_dec(v___x_4787_);
v___x_4790_ = lean_box(0);
v_isShared_4791_ = v_isSharedCheck_4808_;
goto v_resetjp_4789_;
}
v_resetjp_4789_:
{
if (lean_obj_tag(v_a_4788_) == 1)
{
lean_object* v_val_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; uint8_t v___x_4796_; 
v_val_4792_ = lean_ctor_get(v_a_4788_, 0);
lean_inc_n(v_val_4792_, 2);
lean_dec_ref(v_a_4788_);
lean_inc(v_val_4784_);
v___x_4793_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4793_, 0, v_val_4784_);
lean_ctor_set(v___x_4793_, 1, v_val_4792_);
v___x_4794_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4793_);
v___x_4795_ = lean_box(0);
v___x_4796_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4794_, v___x_4795_);
if (v___x_4796_ == 0)
{
lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; 
lean_del_object(v___x_4790_);
v___x_4797_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4797_, 0, v_a_4762_);
lean_ctor_set(v___x_4797_, 1, v_b_4763_);
lean_ctor_set(v___x_4797_, 2, v_val_4784_);
lean_ctor_set(v___x_4797_, 3, v_val_4792_);
v___x_4798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4798_, 0, v___x_4794_);
lean_ctor_set(v___x_4798_, 1, v___x_4797_);
v___x_4799_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_4798_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_);
return v___x_4799_;
}
else
{
lean_object* v___x_4800_; lean_object* v___x_4802_; 
lean_dec(v___x_4794_);
lean_dec(v_val_4792_);
lean_dec(v_val_4784_);
lean_dec_ref(v_b_4763_);
lean_dec_ref(v_a_4762_);
v___x_4800_ = lean_box(0);
if (v_isShared_4791_ == 0)
{
lean_ctor_set(v___x_4790_, 0, v___x_4800_);
v___x_4802_ = v___x_4790_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v___x_4800_);
v___x_4802_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
return v___x_4802_;
}
}
}
else
{
lean_object* v___x_4804_; lean_object* v___x_4806_; 
lean_dec(v_a_4788_);
lean_dec(v_val_4784_);
lean_dec_ref(v_b_4763_);
lean_dec_ref(v_a_4762_);
v___x_4804_ = lean_box(0);
if (v_isShared_4791_ == 0)
{
lean_ctor_set(v___x_4790_, 0, v___x_4804_);
v___x_4806_ = v___x_4790_;
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
}
else
{
lean_object* v_a_4809_; lean_object* v___x_4811_; uint8_t v_isShared_4812_; uint8_t v_isSharedCheck_4816_; 
lean_dec(v_val_4784_);
lean_dec_ref(v_b_4763_);
lean_dec_ref(v_a_4762_);
v_a_4809_ = lean_ctor_get(v___x_4787_, 0);
v_isSharedCheck_4816_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4816_ == 0)
{
v___x_4811_ = v___x_4787_;
v_isShared_4812_ = v_isSharedCheck_4816_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_a_4809_);
lean_dec(v___x_4787_);
v___x_4811_ = lean_box(0);
v_isShared_4812_ = v_isSharedCheck_4816_;
goto v_resetjp_4810_;
}
v_resetjp_4810_:
{
lean_object* v___x_4814_; 
if (v_isShared_4812_ == 0)
{
v___x_4814_ = v___x_4811_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v_a_4809_);
v___x_4814_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
return v___x_4814_;
}
}
}
}
else
{
lean_object* v_a_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4824_; 
lean_dec(v_val_4784_);
lean_dec_ref(v_b_4763_);
lean_dec_ref(v_a_4762_);
v_a_4817_ = lean_ctor_get(v___x_4785_, 0);
v_isSharedCheck_4824_ = !lean_is_exclusive(v___x_4785_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4819_ = v___x_4785_;
v_isShared_4820_ = v_isSharedCheck_4824_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_a_4817_);
lean_dec(v___x_4785_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4824_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4822_; 
if (v_isShared_4820_ == 0)
{
v___x_4822_ = v___x_4819_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v_a_4817_);
v___x_4822_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
return v___x_4822_;
}
}
}
}
else
{
lean_object* v___x_4825_; lean_object* v___x_4827_; 
lean_dec(v_a_4780_);
lean_dec_ref(v_b_4763_);
lean_dec_ref(v_a_4762_);
v___x_4825_ = lean_box(0);
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 0, v___x_4825_);
v___x_4827_ = v___x_4782_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v___x_4825_);
v___x_4827_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
return v___x_4827_;
}
}
}
}
else
{
lean_object* v_a_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4837_; 
lean_dec_ref(v_b_4763_);
lean_dec_ref(v_a_4762_);
v_a_4830_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4832_ = v___x_4779_;
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_a_4830_);
lean_dec(v___x_4779_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v___x_4835_; 
if (v_isShared_4833_ == 0)
{
v___x_4835_ = v___x_4832_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v_a_4830_);
v___x_4835_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
return v___x_4835_;
}
}
}
}
else
{
lean_object* v_a_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4845_; 
lean_dec_ref(v_b_4763_);
lean_dec_ref(v_a_4762_);
v_a_4838_ = lean_ctor_get(v___x_4776_, 0);
v_isSharedCheck_4845_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4845_ == 0)
{
v___x_4840_ = v___x_4776_;
v_isShared_4841_ = v_isSharedCheck_4845_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_a_4838_);
lean_dec(v___x_4776_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4845_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v___x_4843_; 
if (v_isShared_4841_ == 0)
{
v___x_4843_ = v___x_4840_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4844_; 
v_reuseFailAlloc_4844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4844_, 0, v_a_4838_);
v___x_4843_ = v_reuseFailAlloc_4844_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
return v___x_4843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___boxed(lean_object* v_a_4846_, lean_object* v_b_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_){
_start:
{
lean_object* v_res_4860_; 
v_res_4860_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_4846_, v_b_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_, v_a_4858_);
lean_dec(v_a_4858_);
lean_dec_ref(v_a_4857_);
lean_dec(v_a_4856_);
lean_dec_ref(v_a_4855_);
lean_dec(v_a_4854_);
lean_dec_ref(v_a_4853_);
lean_dec(v_a_4852_);
lean_dec_ref(v_a_4851_);
lean_dec(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec(v_a_4848_);
return v_res_4860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(lean_object* v_a_4861_, lean_object* v_b_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_){
_start:
{
lean_object* v___x_4875_; 
v___x_4875_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_);
if (lean_obj_tag(v___x_4875_) == 0)
{
lean_object* v_a_4876_; lean_object* v___x_4877_; 
v_a_4876_ = lean_ctor_get(v___x_4875_, 0);
lean_inc(v_a_4876_);
lean_dec_ref(v___x_4875_);
lean_inc_ref(v_a_4861_);
v___x_4877_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_4861_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_);
if (lean_obj_tag(v___x_4877_) == 0)
{
lean_object* v_a_4878_; lean_object* v_fst_4879_; lean_object* v___x_4880_; 
v_a_4878_ = lean_ctor_get(v___x_4877_, 0);
lean_inc(v_a_4878_);
lean_dec_ref(v___x_4877_);
v_fst_4879_ = lean_ctor_get(v_a_4878_, 0);
lean_inc(v_fst_4879_);
lean_dec(v_a_4878_);
lean_inc_ref(v_b_4862_);
v___x_4880_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_);
if (lean_obj_tag(v___x_4880_) == 0)
{
lean_object* v_a_4881_; lean_object* v_fst_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4965_; 
v_a_4881_ = lean_ctor_get(v___x_4880_, 0);
lean_inc(v_a_4881_);
lean_dec_ref(v___x_4880_);
v_fst_4882_ = lean_ctor_get(v_a_4881_, 0);
v_isSharedCheck_4965_ = !lean_is_exclusive(v_a_4881_);
if (v_isSharedCheck_4965_ == 0)
{
lean_object* v_unused_4966_; 
v_unused_4966_ = lean_ctor_get(v_a_4881_, 1);
lean_dec(v_unused_4966_);
v___x_4884_ = v_a_4881_;
v_isShared_4885_ = v_isSharedCheck_4965_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_fst_4882_);
lean_dec(v_a_4881_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4965_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___x_4886_; 
v___x_4886_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4861_, v_a_4864_);
if (lean_obj_tag(v___x_4886_) == 0)
{
lean_object* v_a_4887_; lean_object* v_id_4888_; lean_object* v_structId_4889_; uint8_t v___x_4890_; lean_object* v___x_4891_; 
v_a_4887_ = lean_ctor_get(v___x_4886_, 0);
lean_inc(v_a_4887_);
lean_dec_ref(v___x_4886_);
v_id_4888_ = lean_ctor_get(v_a_4876_, 0);
lean_inc(v_id_4888_);
v_structId_4889_ = lean_ctor_get(v_a_4876_, 1);
lean_inc(v_structId_4889_);
lean_dec(v_a_4876_);
v___x_4890_ = 0;
v___x_4891_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4879_, v___x_4890_, v_a_4887_, v_structId_4889_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_);
if (lean_obj_tag(v___x_4891_) == 0)
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4948_; 
v_a_4892_ = lean_ctor_get(v___x_4891_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v___x_4891_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4894_ = v___x_4891_;
v_isShared_4895_ = v_isSharedCheck_4948_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4891_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4948_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
if (lean_obj_tag(v_a_4892_) == 1)
{
lean_object* v_val_4896_; lean_object* v___x_4897_; 
lean_del_object(v___x_4894_);
v_val_4896_ = lean_ctor_get(v_a_4892_, 0);
lean_inc(v_val_4896_);
lean_dec_ref(v_a_4892_);
v___x_4897_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4862_, v_a_4864_);
if (lean_obj_tag(v___x_4897_) == 0)
{
lean_object* v_a_4898_; lean_object* v___x_4899_; 
v_a_4898_ = lean_ctor_get(v___x_4897_, 0);
lean_inc(v_a_4898_);
lean_dec_ref(v___x_4897_);
v___x_4899_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4882_, v___x_4890_, v_a_4898_, v_structId_4889_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_);
if (lean_obj_tag(v___x_4899_) == 0)
{
lean_object* v_a_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4927_; 
v_a_4900_ = lean_ctor_get(v___x_4899_, 0);
v_isSharedCheck_4927_ = !lean_is_exclusive(v___x_4899_);
if (v_isSharedCheck_4927_ == 0)
{
v___x_4902_ = v___x_4899_;
v_isShared_4903_ = v_isSharedCheck_4927_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_a_4900_);
lean_dec(v___x_4899_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4927_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
if (lean_obj_tag(v_a_4900_) == 1)
{
lean_object* v_val_4904_; lean_object* v___x_4906_; 
v_val_4904_ = lean_ctor_get(v_a_4900_, 0);
lean_inc_n(v_val_4904_, 2);
lean_dec_ref(v_a_4900_);
lean_inc(v_val_4896_);
if (v_isShared_4885_ == 0)
{
lean_ctor_set_tag(v___x_4884_, 3);
lean_ctor_set(v___x_4884_, 1, v_val_4904_);
lean_ctor_set(v___x_4884_, 0, v_val_4896_);
v___x_4906_ = v___x_4884_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_val_4896_);
lean_ctor_set(v_reuseFailAlloc_4922_, 1, v_val_4904_);
v___x_4906_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
lean_object* v___x_4907_; lean_object* v___x_4908_; uint8_t v___x_4909_; 
v___x_4907_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4906_);
v___x_4908_ = lean_box(0);
v___x_4909_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4907_, v___x_4908_);
if (v___x_4909_ == 0)
{
lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; 
lean_del_object(v___x_4902_);
lean_inc(v_val_4904_);
lean_inc(v_val_4896_);
lean_inc(v_id_4888_);
lean_inc_ref(v_b_4862_);
lean_inc_ref(v_a_4861_);
v___x_4910_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4910_, 0, v_a_4861_);
lean_ctor_set(v___x_4910_, 1, v_b_4862_);
lean_ctor_set(v___x_4910_, 2, v_id_4888_);
lean_ctor_set(v___x_4910_, 3, v_val_4896_);
lean_ctor_set(v___x_4910_, 4, v_val_4904_);
lean_inc(v___x_4907_);
v___x_4911_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4911_, 0, v___x_4907_);
lean_ctor_set(v___x_4911_, 1, v___x_4910_);
lean_ctor_set_uint8(v___x_4911_, sizeof(void*)*2, v___x_4890_);
v___x_4912_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4911_, v_structId_4889_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; 
lean_dec_ref(v___x_4912_);
v___x_4913_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4914_ = l_Lean_Grind_Linarith_Poly_mul(v___x_4907_, v___x_4913_);
v___x_4915_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4915_, 0, v_b_4862_);
lean_ctor_set(v___x_4915_, 1, v_a_4861_);
lean_ctor_set(v___x_4915_, 2, v_id_4888_);
lean_ctor_set(v___x_4915_, 3, v_val_4904_);
lean_ctor_set(v___x_4915_, 4, v_val_4896_);
v___x_4916_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4916_, 0, v___x_4914_);
lean_ctor_set(v___x_4916_, 1, v___x_4915_);
lean_ctor_set_uint8(v___x_4916_, sizeof(void*)*2, v___x_4890_);
v___x_4917_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4916_, v_structId_4889_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_);
lean_dec(v_structId_4889_);
return v___x_4917_;
}
else
{
lean_dec(v___x_4907_);
lean_dec(v_val_4904_);
lean_dec(v_val_4896_);
lean_dec(v_structId_4889_);
lean_dec(v_id_4888_);
lean_dec_ref(v_b_4862_);
lean_dec_ref(v_a_4861_);
return v___x_4912_;
}
}
else
{
lean_object* v___x_4918_; lean_object* v___x_4920_; 
lean_dec(v___x_4907_);
lean_dec(v_val_4904_);
lean_dec(v_val_4896_);
lean_dec(v_structId_4889_);
lean_dec(v_id_4888_);
lean_dec_ref(v_b_4862_);
lean_dec_ref(v_a_4861_);
v___x_4918_ = lean_box(0);
if (v_isShared_4903_ == 0)
{
lean_ctor_set(v___x_4902_, 0, v___x_4918_);
v___x_4920_ = v___x_4902_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v___x_4918_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
}
else
{
lean_object* v___x_4923_; lean_object* v___x_4925_; 
lean_dec(v_a_4900_);
lean_dec(v_val_4896_);
lean_dec(v_structId_4889_);
lean_dec(v_id_4888_);
lean_del_object(v___x_4884_);
lean_dec_ref(v_b_4862_);
lean_dec_ref(v_a_4861_);
v___x_4923_ = lean_box(0);
if (v_isShared_4903_ == 0)
{
lean_ctor_set(v___x_4902_, 0, v___x_4923_);
v___x_4925_ = v___x_4902_;
goto v_reusejp_4924_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v___x_4923_);
v___x_4925_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4924_;
}
v_reusejp_4924_:
{
return v___x_4925_;
}
}
}
}
else
{
lean_object* v_a_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4935_; 
lean_dec(v_val_4896_);
lean_dec(v_structId_4889_);
lean_dec(v_id_4888_);
lean_del_object(v___x_4884_);
lean_dec_ref(v_b_4862_);
lean_dec_ref(v_a_4861_);
v_a_4928_ = lean_ctor_get(v___x_4899_, 0);
v_isSharedCheck_4935_ = !lean_is_exclusive(v___x_4899_);
if (v_isSharedCheck_4935_ == 0)
{
v___x_4930_ = v___x_4899_;
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_a_4928_);
lean_dec(v___x_4899_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v___x_4933_; 
if (v_isShared_4931_ == 0)
{
v___x_4933_ = v___x_4930_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_a_4928_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
}
else
{
lean_object* v_a_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4943_; 
lean_dec(v_val_4896_);
lean_dec(v_structId_4889_);
lean_dec(v_id_4888_);
lean_del_object(v___x_4884_);
lean_dec(v_fst_4882_);
lean_dec_ref(v_b_4862_);
lean_dec_ref(v_a_4861_);
v_a_4936_ = lean_ctor_get(v___x_4897_, 0);
v_isSharedCheck_4943_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4938_ = v___x_4897_;
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
else
{
lean_inc(v_a_4936_);
lean_dec(v___x_4897_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
v_resetjp_4937_:
{
lean_object* v___x_4941_; 
if (v_isShared_4939_ == 0)
{
v___x_4941_ = v___x_4938_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_a_4936_);
v___x_4941_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4940_;
}
v_reusejp_4940_:
{
return v___x_4941_;
}
}
}
}
else
{
lean_object* v___x_4944_; lean_object* v___x_4946_; 
lean_dec(v_a_4892_);
lean_dec(v_structId_4889_);
lean_dec(v_id_4888_);
lean_del_object(v___x_4884_);
lean_dec(v_fst_4882_);
lean_dec_ref(v_b_4862_);
lean_dec_ref(v_a_4861_);
v___x_4944_ = lean_box(0);
if (v_isShared_4895_ == 0)
{
lean_ctor_set(v___x_4894_, 0, v___x_4944_);
v___x_4946_ = v___x_4894_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v___x_4944_);
v___x_4946_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
return v___x_4946_;
}
}
}
}
else
{
lean_object* v_a_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_4956_; 
lean_dec(v_structId_4889_);
lean_dec(v_id_4888_);
lean_del_object(v___x_4884_);
lean_dec(v_fst_4882_);
lean_dec_ref(v_b_4862_);
lean_dec_ref(v_a_4861_);
v_a_4949_ = lean_ctor_get(v___x_4891_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4891_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4951_ = v___x_4891_;
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_a_4949_);
lean_dec(v___x_4891_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
lean_object* v___x_4954_; 
if (v_isShared_4952_ == 0)
{
v___x_4954_ = v___x_4951_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_a_4949_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
return v___x_4954_;
}
}
}
}
else
{
lean_object* v_a_4957_; lean_object* v___x_4959_; uint8_t v_isShared_4960_; uint8_t v_isSharedCheck_4964_; 
lean_del_object(v___x_4884_);
lean_dec(v_fst_4882_);
lean_dec(v_fst_4879_);
lean_dec(v_a_4876_);
lean_dec_ref(v_b_4862_);
lean_dec_ref(v_a_4861_);
v_a_4957_ = lean_ctor_get(v___x_4886_, 0);
v_isSharedCheck_4964_ = !lean_is_exclusive(v___x_4886_);
if (v_isSharedCheck_4964_ == 0)
{
v___x_4959_ = v___x_4886_;
v_isShared_4960_ = v_isSharedCheck_4964_;
goto v_resetjp_4958_;
}
else
{
lean_inc(v_a_4957_);
lean_dec(v___x_4886_);
v___x_4959_ = lean_box(0);
v_isShared_4960_ = v_isSharedCheck_4964_;
goto v_resetjp_4958_;
}
v_resetjp_4958_:
{
lean_object* v___x_4962_; 
if (v_isShared_4960_ == 0)
{
v___x_4962_ = v___x_4959_;
goto v_reusejp_4961_;
}
else
{
lean_object* v_reuseFailAlloc_4963_; 
v_reuseFailAlloc_4963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4963_, 0, v_a_4957_);
v___x_4962_ = v_reuseFailAlloc_4963_;
goto v_reusejp_4961_;
}
v_reusejp_4961_:
{
return v___x_4962_;
}
}
}
}
}
else
{
lean_object* v_a_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_4974_; 
lean_dec(v_fst_4879_);
lean_dec(v_a_4876_);
lean_dec_ref(v_b_4862_);
lean_dec_ref(v_a_4861_);
v_a_4967_ = lean_ctor_get(v___x_4880_, 0);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4969_ = v___x_4880_;
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_a_4967_);
lean_dec(v___x_4880_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v___x_4972_; 
if (v_isShared_4970_ == 0)
{
v___x_4972_ = v___x_4969_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_a_4967_);
v___x_4972_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
return v___x_4972_;
}
}
}
}
else
{
lean_object* v_a_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_4982_; 
lean_dec(v_a_4876_);
lean_dec_ref(v_b_4862_);
lean_dec_ref(v_a_4861_);
v_a_4975_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_4982_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4982_ == 0)
{
v___x_4977_ = v___x_4877_;
v_isShared_4978_ = v_isSharedCheck_4982_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_a_4975_);
lean_dec(v___x_4877_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_4982_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
lean_object* v___x_4980_; 
if (v_isShared_4978_ == 0)
{
v___x_4980_ = v___x_4977_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_a_4975_);
v___x_4980_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
return v___x_4980_;
}
}
}
}
else
{
lean_object* v_a_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_4990_; 
lean_dec_ref(v_b_4862_);
lean_dec_ref(v_a_4861_);
v_a_4983_ = lean_ctor_get(v___x_4875_, 0);
v_isSharedCheck_4990_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4990_ == 0)
{
v___x_4985_ = v___x_4875_;
v_isShared_4986_ = v_isSharedCheck_4990_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_a_4983_);
lean_dec(v___x_4875_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_4990_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
lean_object* v___x_4988_; 
if (v_isShared_4986_ == 0)
{
v___x_4988_ = v___x_4985_;
goto v_reusejp_4987_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v_a_4983_);
v___x_4988_ = v_reuseFailAlloc_4989_;
goto v_reusejp_4987_;
}
v_reusejp_4987_:
{
return v___x_4988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27___boxed(lean_object* v_a_4991_, lean_object* v_b_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_){
_start:
{
lean_object* v_res_5005_; 
v_res_5005_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_4991_, v_b_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_);
lean_dec(v_a_5003_);
lean_dec_ref(v_a_5002_);
lean_dec(v_a_5001_);
lean_dec_ref(v_a_5000_);
lean_dec(v_a_4999_);
lean_dec_ref(v_a_4998_);
lean_dec(v_a_4997_);
lean_dec_ref(v_a_4996_);
lean_dec(v_a_4995_);
lean_dec(v_a_4994_);
lean_dec(v_a_4993_);
return v_res_5005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(lean_object* v_a_5006_, lean_object* v_b_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_){
_start:
{
lean_object* v___x_5020_; 
v___x_5020_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_);
if (lean_obj_tag(v___x_5020_) == 0)
{
lean_object* v_a_5021_; lean_object* v___x_5022_; 
v_a_5021_ = lean_ctor_get(v___x_5020_, 0);
lean_inc(v_a_5021_);
lean_dec_ref(v___x_5020_);
lean_inc_ref(v_a_5006_);
v___x_5022_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5006_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_);
if (lean_obj_tag(v___x_5022_) == 0)
{
lean_object* v_a_5023_; lean_object* v_fst_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5120_; 
v_a_5023_ = lean_ctor_get(v___x_5022_, 0);
lean_inc(v_a_5023_);
lean_dec_ref(v___x_5022_);
v_fst_5024_ = lean_ctor_get(v_a_5023_, 0);
v_isSharedCheck_5120_ = !lean_is_exclusive(v_a_5023_);
if (v_isSharedCheck_5120_ == 0)
{
lean_object* v_unused_5121_; 
v_unused_5121_ = lean_ctor_get(v_a_5023_, 1);
lean_dec(v_unused_5121_);
v___x_5026_ = v_a_5023_;
v_isShared_5027_ = v_isSharedCheck_5120_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_fst_5024_);
lean_dec(v_a_5023_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5120_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v___x_5028_; 
lean_inc_ref(v_b_5007_);
v___x_5028_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_);
if (lean_obj_tag(v___x_5028_) == 0)
{
lean_object* v_a_5029_; lean_object* v_fst_5030_; lean_object* v___x_5032_; uint8_t v_isShared_5033_; uint8_t v_isSharedCheck_5110_; 
v_a_5029_ = lean_ctor_get(v___x_5028_, 0);
lean_inc(v_a_5029_);
lean_dec_ref(v___x_5028_);
v_fst_5030_ = lean_ctor_get(v_a_5029_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v_a_5029_);
if (v_isSharedCheck_5110_ == 0)
{
lean_object* v_unused_5111_; 
v_unused_5111_ = lean_ctor_get(v_a_5029_, 1);
lean_dec(v_unused_5111_);
v___x_5032_ = v_a_5029_;
v_isShared_5033_ = v_isSharedCheck_5110_;
goto v_resetjp_5031_;
}
else
{
lean_inc(v_fst_5030_);
lean_dec(v_a_5029_);
v___x_5032_ = lean_box(0);
v_isShared_5033_ = v_isSharedCheck_5110_;
goto v_resetjp_5031_;
}
v_resetjp_5031_:
{
lean_object* v___x_5034_; 
v___x_5034_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5006_, v_a_5009_);
if (lean_obj_tag(v___x_5034_) == 0)
{
lean_object* v_a_5035_; lean_object* v_id_5036_; lean_object* v_structId_5037_; uint8_t v___x_5038_; lean_object* v___x_5039_; 
v_a_5035_ = lean_ctor_get(v___x_5034_, 0);
lean_inc(v_a_5035_);
lean_dec_ref(v___x_5034_);
v_id_5036_ = lean_ctor_get(v_a_5021_, 0);
lean_inc(v_id_5036_);
v_structId_5037_ = lean_ctor_get(v_a_5021_, 1);
lean_inc(v_structId_5037_);
lean_dec(v_a_5021_);
v___x_5038_ = 0;
v___x_5039_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5024_, v___x_5038_, v_a_5035_, v_structId_5037_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_);
if (lean_obj_tag(v___x_5039_) == 0)
{
lean_object* v_a_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5093_; 
v_a_5040_ = lean_ctor_get(v___x_5039_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_5039_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5042_ = v___x_5039_;
v_isShared_5043_ = v_isSharedCheck_5093_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_a_5040_);
lean_dec(v___x_5039_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5093_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
if (lean_obj_tag(v_a_5040_) == 1)
{
lean_object* v_val_5044_; lean_object* v___x_5045_; 
lean_del_object(v___x_5042_);
v_val_5044_ = lean_ctor_get(v_a_5040_, 0);
lean_inc(v_val_5044_);
lean_dec_ref(v_a_5040_);
v___x_5045_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5007_, v_a_5009_);
if (lean_obj_tag(v___x_5045_) == 0)
{
lean_object* v_a_5046_; lean_object* v___x_5047_; 
v_a_5046_ = lean_ctor_get(v___x_5045_, 0);
lean_inc(v_a_5046_);
lean_dec_ref(v___x_5045_);
v___x_5047_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5030_, v___x_5038_, v_a_5046_, v_structId_5037_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_);
if (lean_obj_tag(v___x_5047_) == 0)
{
lean_object* v_a_5048_; lean_object* v___x_5050_; uint8_t v_isShared_5051_; uint8_t v_isSharedCheck_5072_; 
v_a_5048_ = lean_ctor_get(v___x_5047_, 0);
v_isSharedCheck_5072_ = !lean_is_exclusive(v___x_5047_);
if (v_isSharedCheck_5072_ == 0)
{
v___x_5050_ = v___x_5047_;
v_isShared_5051_ = v_isSharedCheck_5072_;
goto v_resetjp_5049_;
}
else
{
lean_inc(v_a_5048_);
lean_dec(v___x_5047_);
v___x_5050_ = lean_box(0);
v_isShared_5051_ = v_isSharedCheck_5072_;
goto v_resetjp_5049_;
}
v_resetjp_5049_:
{
if (lean_obj_tag(v_a_5048_) == 1)
{
lean_object* v_val_5052_; lean_object* v___x_5054_; 
v_val_5052_ = lean_ctor_get(v_a_5048_, 0);
lean_inc_n(v_val_5052_, 2);
lean_dec_ref(v_a_5048_);
lean_inc(v_val_5044_);
if (v_isShared_5033_ == 0)
{
lean_ctor_set_tag(v___x_5032_, 3);
lean_ctor_set(v___x_5032_, 1, v_val_5052_);
lean_ctor_set(v___x_5032_, 0, v_val_5044_);
v___x_5054_ = v___x_5032_;
goto v_reusejp_5053_;
}
else
{
lean_object* v_reuseFailAlloc_5067_; 
v_reuseFailAlloc_5067_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5067_, 0, v_val_5044_);
lean_ctor_set(v_reuseFailAlloc_5067_, 1, v_val_5052_);
v___x_5054_ = v_reuseFailAlloc_5067_;
goto v_reusejp_5053_;
}
v_reusejp_5053_:
{
lean_object* v___x_5055_; lean_object* v___x_5056_; uint8_t v___x_5057_; 
v___x_5055_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5054_);
v___x_5056_ = lean_box(0);
v___x_5057_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_5055_, v___x_5056_);
if (v___x_5057_ == 0)
{
lean_object* v___x_5058_; lean_object* v___x_5060_; 
lean_del_object(v___x_5050_);
v___x_5058_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5058_, 0, v_a_5006_);
lean_ctor_set(v___x_5058_, 1, v_b_5007_);
lean_ctor_set(v___x_5058_, 2, v_id_5036_);
lean_ctor_set(v___x_5058_, 3, v_val_5044_);
lean_ctor_set(v___x_5058_, 4, v_val_5052_);
if (v_isShared_5027_ == 0)
{
lean_ctor_set(v___x_5026_, 1, v___x_5058_);
lean_ctor_set(v___x_5026_, 0, v___x_5055_);
v___x_5060_ = v___x_5026_;
goto v_reusejp_5059_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v___x_5055_);
lean_ctor_set(v_reuseFailAlloc_5062_, 1, v___x_5058_);
v___x_5060_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5059_;
}
v_reusejp_5059_:
{
lean_object* v___x_5061_; 
v___x_5061_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_5060_, v_structId_5037_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_);
lean_dec(v_structId_5037_);
return v___x_5061_;
}
}
else
{
lean_object* v___x_5063_; lean_object* v___x_5065_; 
lean_dec(v___x_5055_);
lean_dec(v_val_5052_);
lean_dec(v_val_5044_);
lean_dec(v_structId_5037_);
lean_dec(v_id_5036_);
lean_del_object(v___x_5026_);
lean_dec_ref(v_b_5007_);
lean_dec_ref(v_a_5006_);
v___x_5063_ = lean_box(0);
if (v_isShared_5051_ == 0)
{
lean_ctor_set(v___x_5050_, 0, v___x_5063_);
v___x_5065_ = v___x_5050_;
goto v_reusejp_5064_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v___x_5063_);
v___x_5065_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5064_;
}
v_reusejp_5064_:
{
return v___x_5065_;
}
}
}
}
else
{
lean_object* v___x_5068_; lean_object* v___x_5070_; 
lean_dec(v_a_5048_);
lean_dec(v_val_5044_);
lean_dec(v_structId_5037_);
lean_dec(v_id_5036_);
lean_del_object(v___x_5032_);
lean_del_object(v___x_5026_);
lean_dec_ref(v_b_5007_);
lean_dec_ref(v_a_5006_);
v___x_5068_ = lean_box(0);
if (v_isShared_5051_ == 0)
{
lean_ctor_set(v___x_5050_, 0, v___x_5068_);
v___x_5070_ = v___x_5050_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v___x_5068_);
v___x_5070_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
return v___x_5070_;
}
}
}
}
else
{
lean_object* v_a_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5080_; 
lean_dec(v_val_5044_);
lean_dec(v_structId_5037_);
lean_dec(v_id_5036_);
lean_del_object(v___x_5032_);
lean_del_object(v___x_5026_);
lean_dec_ref(v_b_5007_);
lean_dec_ref(v_a_5006_);
v_a_5073_ = lean_ctor_get(v___x_5047_, 0);
v_isSharedCheck_5080_ = !lean_is_exclusive(v___x_5047_);
if (v_isSharedCheck_5080_ == 0)
{
v___x_5075_ = v___x_5047_;
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_a_5073_);
lean_dec(v___x_5047_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
lean_object* v___x_5078_; 
if (v_isShared_5076_ == 0)
{
v___x_5078_ = v___x_5075_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v_a_5073_);
v___x_5078_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
return v___x_5078_;
}
}
}
}
else
{
lean_object* v_a_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5088_; 
lean_dec(v_val_5044_);
lean_dec(v_structId_5037_);
lean_dec(v_id_5036_);
lean_del_object(v___x_5032_);
lean_dec(v_fst_5030_);
lean_del_object(v___x_5026_);
lean_dec_ref(v_b_5007_);
lean_dec_ref(v_a_5006_);
v_a_5081_ = lean_ctor_get(v___x_5045_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5045_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5083_ = v___x_5045_;
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
else
{
lean_inc(v_a_5081_);
lean_dec(v___x_5045_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
v_resetjp_5082_:
{
lean_object* v___x_5086_; 
if (v_isShared_5084_ == 0)
{
v___x_5086_ = v___x_5083_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_a_5081_);
v___x_5086_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
return v___x_5086_;
}
}
}
}
else
{
lean_object* v___x_5089_; lean_object* v___x_5091_; 
lean_dec(v_a_5040_);
lean_dec(v_structId_5037_);
lean_dec(v_id_5036_);
lean_del_object(v___x_5032_);
lean_dec(v_fst_5030_);
lean_del_object(v___x_5026_);
lean_dec_ref(v_b_5007_);
lean_dec_ref(v_a_5006_);
v___x_5089_ = lean_box(0);
if (v_isShared_5043_ == 0)
{
lean_ctor_set(v___x_5042_, 0, v___x_5089_);
v___x_5091_ = v___x_5042_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v___x_5089_);
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
else
{
lean_object* v_a_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5101_; 
lean_dec(v_structId_5037_);
lean_dec(v_id_5036_);
lean_del_object(v___x_5032_);
lean_dec(v_fst_5030_);
lean_del_object(v___x_5026_);
lean_dec_ref(v_b_5007_);
lean_dec_ref(v_a_5006_);
v_a_5094_ = lean_ctor_get(v___x_5039_, 0);
v_isSharedCheck_5101_ = !lean_is_exclusive(v___x_5039_);
if (v_isSharedCheck_5101_ == 0)
{
v___x_5096_ = v___x_5039_;
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_a_5094_);
lean_dec(v___x_5039_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5099_; 
if (v_isShared_5097_ == 0)
{
v___x_5099_ = v___x_5096_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v_a_5094_);
v___x_5099_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
return v___x_5099_;
}
}
}
}
else
{
lean_object* v_a_5102_; lean_object* v___x_5104_; uint8_t v_isShared_5105_; uint8_t v_isSharedCheck_5109_; 
lean_del_object(v___x_5032_);
lean_dec(v_fst_5030_);
lean_del_object(v___x_5026_);
lean_dec(v_fst_5024_);
lean_dec(v_a_5021_);
lean_dec_ref(v_b_5007_);
lean_dec_ref(v_a_5006_);
v_a_5102_ = lean_ctor_get(v___x_5034_, 0);
v_isSharedCheck_5109_ = !lean_is_exclusive(v___x_5034_);
if (v_isSharedCheck_5109_ == 0)
{
v___x_5104_ = v___x_5034_;
v_isShared_5105_ = v_isSharedCheck_5109_;
goto v_resetjp_5103_;
}
else
{
lean_inc(v_a_5102_);
lean_dec(v___x_5034_);
v___x_5104_ = lean_box(0);
v_isShared_5105_ = v_isSharedCheck_5109_;
goto v_resetjp_5103_;
}
v_resetjp_5103_:
{
lean_object* v___x_5107_; 
if (v_isShared_5105_ == 0)
{
v___x_5107_ = v___x_5104_;
goto v_reusejp_5106_;
}
else
{
lean_object* v_reuseFailAlloc_5108_; 
v_reuseFailAlloc_5108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5108_, 0, v_a_5102_);
v___x_5107_ = v_reuseFailAlloc_5108_;
goto v_reusejp_5106_;
}
v_reusejp_5106_:
{
return v___x_5107_;
}
}
}
}
}
else
{
lean_object* v_a_5112_; lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5119_; 
lean_del_object(v___x_5026_);
lean_dec(v_fst_5024_);
lean_dec(v_a_5021_);
lean_dec_ref(v_b_5007_);
lean_dec_ref(v_a_5006_);
v_a_5112_ = lean_ctor_get(v___x_5028_, 0);
v_isSharedCheck_5119_ = !lean_is_exclusive(v___x_5028_);
if (v_isSharedCheck_5119_ == 0)
{
v___x_5114_ = v___x_5028_;
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
else
{
lean_inc(v_a_5112_);
lean_dec(v___x_5028_);
v___x_5114_ = lean_box(0);
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
v_resetjp_5113_:
{
lean_object* v___x_5117_; 
if (v_isShared_5115_ == 0)
{
v___x_5117_ = v___x_5114_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_a_5112_);
v___x_5117_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
return v___x_5117_;
}
}
}
}
}
else
{
lean_object* v_a_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5129_; 
lean_dec(v_a_5021_);
lean_dec_ref(v_b_5007_);
lean_dec_ref(v_a_5006_);
v_a_5122_ = lean_ctor_get(v___x_5022_, 0);
v_isSharedCheck_5129_ = !lean_is_exclusive(v___x_5022_);
if (v_isSharedCheck_5129_ == 0)
{
v___x_5124_ = v___x_5022_;
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_a_5122_);
lean_dec(v___x_5022_);
v___x_5124_ = lean_box(0);
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
v_resetjp_5123_:
{
lean_object* v___x_5127_; 
if (v_isShared_5125_ == 0)
{
v___x_5127_ = v___x_5124_;
goto v_reusejp_5126_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v_a_5122_);
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
lean_dec_ref(v_b_5007_);
lean_dec_ref(v_a_5006_);
v_a_5130_ = lean_ctor_get(v___x_5020_, 0);
v_isSharedCheck_5137_ = !lean_is_exclusive(v___x_5020_);
if (v_isSharedCheck_5137_ == 0)
{
v___x_5132_ = v___x_5020_;
v_isShared_5133_ = v_isSharedCheck_5137_;
goto v_resetjp_5131_;
}
else
{
lean_inc(v_a_5130_);
lean_dec(v___x_5020_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq___boxed(lean_object* v_a_5138_, lean_object* v_b_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_){
_start:
{
lean_object* v_res_5152_; 
v_res_5152_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5138_, v_b_5139_, v_a_5140_, v_a_5141_, v_a_5142_, v_a_5143_, v_a_5144_, v_a_5145_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_);
lean_dec(v_a_5150_);
lean_dec_ref(v_a_5149_);
lean_dec(v_a_5148_);
lean_dec_ref(v_a_5147_);
lean_dec(v_a_5146_);
lean_dec_ref(v_a_5145_);
lean_dec(v_a_5144_);
lean_dec_ref(v_a_5143_);
lean_dec(v_a_5142_);
lean_dec(v_a_5141_);
lean_dec(v_a_5140_);
return v_res_5152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq(lean_object* v_a_5153_, lean_object* v_b_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_){
_start:
{
uint8_t v___x_5166_; 
v___x_5166_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_5153_, v_b_5154_);
if (v___x_5166_ == 0)
{
lean_object* v___x_5167_; 
v___x_5167_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5153_, v_b_5154_, v_a_5155_, v_a_5163_);
if (lean_obj_tag(v___x_5167_) == 0)
{
lean_object* v_a_5168_; 
v_a_5168_ = lean_ctor_get(v___x_5167_, 0);
lean_inc(v_a_5168_);
lean_dec_ref(v___x_5167_);
if (lean_obj_tag(v_a_5168_) == 1)
{
lean_object* v_val_5169_; lean_object* v___x_5170_; 
v_val_5169_ = lean_ctor_get(v_a_5168_, 0);
lean_inc(v_val_5169_);
lean_dec_ref(v_a_5168_);
v___x_5170_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_val_5169_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_);
if (lean_obj_tag(v___x_5170_) == 0)
{
lean_object* v_a_5171_; uint8_t v___x_5172_; 
v_a_5171_ = lean_ctor_get(v___x_5170_, 0);
lean_inc(v_a_5171_);
lean_dec_ref(v___x_5170_);
v___x_5172_ = lean_unbox(v_a_5171_);
lean_dec(v_a_5171_);
if (v___x_5172_ == 0)
{
lean_object* v___x_5173_; 
v___x_5173_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5169_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_);
if (lean_obj_tag(v___x_5173_) == 0)
{
lean_object* v_a_5174_; uint8_t v___x_5175_; 
v_a_5174_ = lean_ctor_get(v___x_5173_, 0);
lean_inc(v_a_5174_);
lean_dec_ref(v___x_5173_);
v___x_5175_ = lean_unbox(v_a_5174_);
lean_dec(v_a_5174_);
if (v___x_5175_ == 0)
{
lean_object* v___x_5176_; 
v___x_5176_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_5153_, v_b_5154_, v_val_5169_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_);
lean_dec(v_val_5169_);
return v___x_5176_;
}
else
{
lean_object* v___x_5177_; 
lean_dec(v_val_5169_);
v___x_5177_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_5153_, v_b_5154_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_);
return v___x_5177_;
}
}
else
{
lean_object* v_a_5178_; lean_object* v___x_5180_; uint8_t v_isShared_5181_; uint8_t v_isSharedCheck_5185_; 
lean_dec(v_val_5169_);
lean_dec_ref(v_b_5154_);
lean_dec_ref(v_a_5153_);
v_a_5178_ = lean_ctor_get(v___x_5173_, 0);
v_isSharedCheck_5185_ = !lean_is_exclusive(v___x_5173_);
if (v_isSharedCheck_5185_ == 0)
{
v___x_5180_ = v___x_5173_;
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
else
{
lean_inc(v_a_5178_);
lean_dec(v___x_5173_);
v___x_5180_ = lean_box(0);
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
v_resetjp_5179_:
{
lean_object* v___x_5183_; 
if (v_isShared_5181_ == 0)
{
v___x_5183_ = v___x_5180_;
goto v_reusejp_5182_;
}
else
{
lean_object* v_reuseFailAlloc_5184_; 
v_reuseFailAlloc_5184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5184_, 0, v_a_5178_);
v___x_5183_ = v_reuseFailAlloc_5184_;
goto v_reusejp_5182_;
}
v_reusejp_5182_:
{
return v___x_5183_;
}
}
}
}
else
{
lean_object* v___x_5186_; 
v___x_5186_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5169_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_);
if (lean_obj_tag(v___x_5186_) == 0)
{
lean_object* v_a_5187_; uint8_t v___x_5188_; 
v_a_5187_ = lean_ctor_get(v___x_5186_, 0);
lean_inc(v_a_5187_);
lean_dec_ref(v___x_5186_);
v___x_5188_ = lean_unbox(v_a_5187_);
lean_dec(v_a_5187_);
if (v___x_5188_ == 0)
{
lean_object* v___x_5189_; 
v___x_5189_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_5153_, v_b_5154_, v_val_5169_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_);
lean_dec(v_val_5169_);
return v___x_5189_;
}
else
{
lean_object* v___x_5190_; 
v___x_5190_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_5153_, v_b_5154_, v_val_5169_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_);
lean_dec(v_val_5169_);
return v___x_5190_;
}
}
else
{
lean_object* v_a_5191_; lean_object* v___x_5193_; uint8_t v_isShared_5194_; uint8_t v_isSharedCheck_5198_; 
lean_dec(v_val_5169_);
lean_dec_ref(v_b_5154_);
lean_dec_ref(v_a_5153_);
v_a_5191_ = lean_ctor_get(v___x_5186_, 0);
v_isSharedCheck_5198_ = !lean_is_exclusive(v___x_5186_);
if (v_isSharedCheck_5198_ == 0)
{
v___x_5193_ = v___x_5186_;
v_isShared_5194_ = v_isSharedCheck_5198_;
goto v_resetjp_5192_;
}
else
{
lean_inc(v_a_5191_);
lean_dec(v___x_5186_);
v___x_5193_ = lean_box(0);
v_isShared_5194_ = v_isSharedCheck_5198_;
goto v_resetjp_5192_;
}
v_resetjp_5192_:
{
lean_object* v___x_5196_; 
if (v_isShared_5194_ == 0)
{
v___x_5196_ = v___x_5193_;
goto v_reusejp_5195_;
}
else
{
lean_object* v_reuseFailAlloc_5197_; 
v_reuseFailAlloc_5197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5197_, 0, v_a_5191_);
v___x_5196_ = v_reuseFailAlloc_5197_;
goto v_reusejp_5195_;
}
v_reusejp_5195_:
{
return v___x_5196_;
}
}
}
}
}
else
{
lean_object* v_a_5199_; lean_object* v___x_5201_; uint8_t v_isShared_5202_; uint8_t v_isSharedCheck_5206_; 
lean_dec(v_val_5169_);
lean_dec_ref(v_b_5154_);
lean_dec_ref(v_a_5153_);
v_a_5199_ = lean_ctor_get(v___x_5170_, 0);
v_isSharedCheck_5206_ = !lean_is_exclusive(v___x_5170_);
if (v_isSharedCheck_5206_ == 0)
{
v___x_5201_ = v___x_5170_;
v_isShared_5202_ = v_isSharedCheck_5206_;
goto v_resetjp_5200_;
}
else
{
lean_inc(v_a_5199_);
lean_dec(v___x_5170_);
v___x_5201_ = lean_box(0);
v_isShared_5202_ = v_isSharedCheck_5206_;
goto v_resetjp_5200_;
}
v_resetjp_5200_:
{
lean_object* v___x_5204_; 
if (v_isShared_5202_ == 0)
{
v___x_5204_ = v___x_5201_;
goto v_reusejp_5203_;
}
else
{
lean_object* v_reuseFailAlloc_5205_; 
v_reuseFailAlloc_5205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5205_, 0, v_a_5199_);
v___x_5204_ = v_reuseFailAlloc_5205_;
goto v_reusejp_5203_;
}
v_reusejp_5203_:
{
return v___x_5204_;
}
}
}
}
else
{
lean_object* v___x_5207_; 
lean_dec(v_a_5168_);
v___x_5207_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5153_, v_b_5154_, v_a_5155_, v_a_5163_);
if (lean_obj_tag(v___x_5207_) == 0)
{
lean_object* v_a_5208_; lean_object* v___x_5210_; uint8_t v_isShared_5211_; uint8_t v_isSharedCheck_5230_; 
v_a_5208_ = lean_ctor_get(v___x_5207_, 0);
v_isSharedCheck_5230_ = !lean_is_exclusive(v___x_5207_);
if (v_isSharedCheck_5230_ == 0)
{
v___x_5210_ = v___x_5207_;
v_isShared_5211_ = v_isSharedCheck_5230_;
goto v_resetjp_5209_;
}
else
{
lean_inc(v_a_5208_);
lean_dec(v___x_5207_);
v___x_5210_ = lean_box(0);
v_isShared_5211_ = v_isSharedCheck_5230_;
goto v_resetjp_5209_;
}
v_resetjp_5209_:
{
if (lean_obj_tag(v_a_5208_) == 1)
{
lean_object* v_val_5212_; lean_object* v___x_5213_; 
lean_del_object(v___x_5210_);
v_val_5212_ = lean_ctor_get(v_a_5208_, 0);
lean_inc(v_val_5212_);
lean_dec_ref(v_a_5208_);
v___x_5213_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_5212_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_);
if (lean_obj_tag(v___x_5213_) == 0)
{
lean_object* v_a_5214_; lean_object* v_orderedAddInst_x3f_5215_; 
v_a_5214_ = lean_ctor_get(v___x_5213_, 0);
lean_inc(v_a_5214_);
lean_dec_ref(v___x_5213_);
v_orderedAddInst_x3f_5215_ = lean_ctor_get(v_a_5214_, 9);
lean_inc(v_orderedAddInst_x3f_5215_);
lean_dec(v_a_5214_);
if (lean_obj_tag(v_orderedAddInst_x3f_5215_) == 0)
{
lean_object* v___x_5216_; 
v___x_5216_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5153_, v_b_5154_, v_val_5212_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_);
lean_dec(v_val_5212_);
return v___x_5216_;
}
else
{
lean_object* v___x_5217_; 
lean_dec_ref(v_orderedAddInst_x3f_5215_);
v___x_5217_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5153_, v_b_5154_, v_val_5212_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_);
lean_dec(v_val_5212_);
return v___x_5217_;
}
}
else
{
lean_object* v_a_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5225_; 
lean_dec(v_val_5212_);
lean_dec_ref(v_b_5154_);
lean_dec_ref(v_a_5153_);
v_a_5218_ = lean_ctor_get(v___x_5213_, 0);
v_isSharedCheck_5225_ = !lean_is_exclusive(v___x_5213_);
if (v_isSharedCheck_5225_ == 0)
{
v___x_5220_ = v___x_5213_;
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
else
{
lean_inc(v_a_5218_);
lean_dec(v___x_5213_);
v___x_5220_ = lean_box(0);
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
v_resetjp_5219_:
{
lean_object* v___x_5223_; 
if (v_isShared_5221_ == 0)
{
v___x_5223_ = v___x_5220_;
goto v_reusejp_5222_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v_a_5218_);
v___x_5223_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5222_;
}
v_reusejp_5222_:
{
return v___x_5223_;
}
}
}
}
else
{
lean_object* v___x_5226_; lean_object* v___x_5228_; 
lean_dec(v_a_5208_);
lean_dec_ref(v_b_5154_);
lean_dec_ref(v_a_5153_);
v___x_5226_ = lean_box(0);
if (v_isShared_5211_ == 0)
{
lean_ctor_set(v___x_5210_, 0, v___x_5226_);
v___x_5228_ = v___x_5210_;
goto v_reusejp_5227_;
}
else
{
lean_object* v_reuseFailAlloc_5229_; 
v_reuseFailAlloc_5229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5229_, 0, v___x_5226_);
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
lean_object* v_a_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5238_; 
lean_dec_ref(v_b_5154_);
lean_dec_ref(v_a_5153_);
v_a_5231_ = lean_ctor_get(v___x_5207_, 0);
v_isSharedCheck_5238_ = !lean_is_exclusive(v___x_5207_);
if (v_isSharedCheck_5238_ == 0)
{
v___x_5233_ = v___x_5207_;
v_isShared_5234_ = v_isSharedCheck_5238_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_a_5231_);
lean_dec(v___x_5207_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5238_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
lean_object* v___x_5236_; 
if (v_isShared_5234_ == 0)
{
v___x_5236_ = v___x_5233_;
goto v_reusejp_5235_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v_a_5231_);
v___x_5236_ = v_reuseFailAlloc_5237_;
goto v_reusejp_5235_;
}
v_reusejp_5235_:
{
return v___x_5236_;
}
}
}
}
}
else
{
lean_object* v_a_5239_; lean_object* v___x_5241_; uint8_t v_isShared_5242_; uint8_t v_isSharedCheck_5246_; 
lean_dec_ref(v_b_5154_);
lean_dec_ref(v_a_5153_);
v_a_5239_ = lean_ctor_get(v___x_5167_, 0);
v_isSharedCheck_5246_ = !lean_is_exclusive(v___x_5167_);
if (v_isSharedCheck_5246_ == 0)
{
v___x_5241_ = v___x_5167_;
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
else
{
lean_inc(v_a_5239_);
lean_dec(v___x_5167_);
v___x_5241_ = lean_box(0);
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
v_resetjp_5240_:
{
lean_object* v___x_5244_; 
if (v_isShared_5242_ == 0)
{
v___x_5244_ = v___x_5241_;
goto v_reusejp_5243_;
}
else
{
lean_object* v_reuseFailAlloc_5245_; 
v_reuseFailAlloc_5245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_a_5239_);
v___x_5244_ = v_reuseFailAlloc_5245_;
goto v_reusejp_5243_;
}
v_reusejp_5243_:
{
return v___x_5244_;
}
}
}
}
else
{
lean_object* v___x_5247_; lean_object* v___x_5248_; 
lean_dec_ref(v_b_5154_);
lean_dec_ref(v_a_5153_);
v___x_5247_ = lean_box(0);
v___x_5248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5248_, 0, v___x_5247_);
return v___x_5248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed(lean_object* v_a_5249_, lean_object* v_b_5250_, lean_object* v_a_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_){
_start:
{
lean_object* v_res_5262_; 
v_res_5262_ = l_Lean_Meta_Grind_Arith_Linear_processNewEq(v_a_5249_, v_b_5250_, v_a_5251_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_);
lean_dec(v_a_5260_);
lean_dec_ref(v_a_5259_);
lean_dec(v_a_5258_);
lean_dec_ref(v_a_5257_);
lean_dec(v_a_5256_);
lean_dec_ref(v_a_5255_);
lean_dec(v_a_5254_);
lean_dec_ref(v_a_5253_);
lean_dec(v_a_5252_);
lean_dec(v_a_5251_);
return v_res_5262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object* v_a_5263_, lean_object* v_b_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_){
_start:
{
uint8_t v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; 
v___x_5277_ = 0;
v___x_5278_ = lean_unsigned_to_nat(0u);
v___x_5279_ = lean_box(v___x_5277_);
lean_inc_ref(v_a_5263_);
v___x_5280_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5280_, 0, v_a_5263_);
lean_closure_set(v___x_5280_, 1, v___x_5279_);
lean_closure_set(v___x_5280_, 2, v___x_5278_);
v___x_5281_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5280_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_);
if (lean_obj_tag(v___x_5281_) == 0)
{
lean_object* v_a_5282_; lean_object* v___x_5284_; uint8_t v_isShared_5285_; uint8_t v_isSharedCheck_5383_; 
v_a_5282_ = lean_ctor_get(v___x_5281_, 0);
v_isSharedCheck_5383_ = !lean_is_exclusive(v___x_5281_);
if (v_isSharedCheck_5383_ == 0)
{
v___x_5284_ = v___x_5281_;
v_isShared_5285_ = v_isSharedCheck_5383_;
goto v_resetjp_5283_;
}
else
{
lean_inc(v_a_5282_);
lean_dec(v___x_5281_);
v___x_5284_ = lean_box(0);
v_isShared_5285_ = v_isSharedCheck_5383_;
goto v_resetjp_5283_;
}
v_resetjp_5283_:
{
if (lean_obj_tag(v_a_5282_) == 1)
{
lean_object* v_val_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; 
lean_del_object(v___x_5284_);
v_val_5286_ = lean_ctor_get(v_a_5282_, 0);
lean_inc(v_val_5286_);
lean_dec_ref(v_a_5282_);
v___x_5287_ = lean_box(v___x_5277_);
lean_inc_ref(v_b_5264_);
v___x_5288_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5288_, 0, v_b_5264_);
lean_closure_set(v___x_5288_, 1, v___x_5287_);
lean_closure_set(v___x_5288_, 2, v___x_5278_);
v___x_5289_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5288_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_);
if (lean_obj_tag(v___x_5289_) == 0)
{
lean_object* v_a_5290_; lean_object* v___x_5292_; uint8_t v_isShared_5293_; uint8_t v_isSharedCheck_5370_; 
v_a_5290_ = lean_ctor_get(v___x_5289_, 0);
v_isSharedCheck_5370_ = !lean_is_exclusive(v___x_5289_);
if (v_isSharedCheck_5370_ == 0)
{
v___x_5292_ = v___x_5289_;
v_isShared_5293_ = v_isSharedCheck_5370_;
goto v_resetjp_5291_;
}
else
{
lean_inc(v_a_5290_);
lean_dec(v___x_5289_);
v___x_5292_ = lean_box(0);
v_isShared_5293_ = v_isSharedCheck_5370_;
goto v_resetjp_5291_;
}
v_resetjp_5291_:
{
if (lean_obj_tag(v_a_5290_) == 1)
{
lean_object* v_val_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; 
lean_del_object(v___x_5292_);
v_val_5294_ = lean_ctor_get(v_a_5290_, 0);
lean_inc_n(v_val_5294_, 2);
lean_dec_ref(v_a_5290_);
lean_inc(v_val_5286_);
v___x_5295_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_5295_, 0, v_val_5286_);
lean_ctor_set(v___x_5295_, 1, v_val_5294_);
v___x_5296_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_5295_);
lean_inc_ref(v_b_5264_);
lean_inc_ref(v_a_5263_);
v___x_5297_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5297_, 0, v_a_5263_);
lean_ctor_set(v___x_5297_, 1, v_b_5264_);
lean_ctor_set(v___x_5297_, 2, v_val_5286_);
lean_ctor_set(v___x_5297_, 3, v_val_5294_);
v___x_5298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5298_, 0, v___x_5296_);
lean_ctor_set(v___x_5298_, 1, v___x_5297_);
v___x_5299_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(v___x_5298_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_);
if (lean_obj_tag(v___x_5299_) == 0)
{
lean_object* v_a_5300_; lean_object* v___x_5301_; 
v_a_5300_ = lean_ctor_get(v___x_5299_, 0);
lean_inc(v_a_5300_);
lean_dec_ref(v___x_5299_);
v___x_5301_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5263_, v_a_5266_);
lean_dec_ref(v_a_5263_);
if (lean_obj_tag(v___x_5301_) == 0)
{
lean_object* v_a_5302_; lean_object* v___x_5303_; 
v_a_5302_ = lean_ctor_get(v___x_5301_, 0);
lean_inc(v_a_5302_);
lean_dec_ref(v___x_5301_);
v___x_5303_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5264_, v_a_5266_);
lean_dec_ref(v_b_5264_);
if (lean_obj_tag(v___x_5303_) == 0)
{
lean_object* v_a_5304_; lean_object* v_p_5305_; lean_object* v___y_5307_; uint8_t v___x_5341_; 
v_a_5304_ = lean_ctor_get(v___x_5303_, 0);
lean_inc(v_a_5304_);
lean_dec_ref(v___x_5303_);
v_p_5305_ = lean_ctor_get(v_a_5300_, 0);
v___x_5341_ = lean_nat_dec_le(v_a_5302_, v_a_5304_);
if (v___x_5341_ == 0)
{
lean_dec(v_a_5304_);
v___y_5307_ = v_a_5302_;
goto v___jp_5306_;
}
else
{
lean_dec(v_a_5302_);
v___y_5307_ = v_a_5304_;
goto v___jp_5306_;
}
v___jp_5306_:
{
lean_object* v___x_5308_; 
lean_inc(v___y_5307_);
lean_inc_ref(v_p_5305_);
v___x_5308_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_5305_, v___y_5307_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_);
if (lean_obj_tag(v___x_5308_) == 0)
{
lean_object* v_a_5309_; lean_object* v___x_5310_; 
v_a_5309_ = lean_ctor_get(v___x_5308_, 0);
lean_inc(v_a_5309_);
lean_dec_ref(v___x_5308_);
v___x_5310_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5309_, v___x_5277_, v___y_5307_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_);
if (lean_obj_tag(v___x_5310_) == 0)
{
lean_object* v_a_5311_; lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5324_; 
v_a_5311_ = lean_ctor_get(v___x_5310_, 0);
v_isSharedCheck_5324_ = !lean_is_exclusive(v___x_5310_);
if (v_isSharedCheck_5324_ == 0)
{
v___x_5313_ = v___x_5310_;
v_isShared_5314_ = v_isSharedCheck_5324_;
goto v_resetjp_5312_;
}
else
{
lean_inc(v_a_5311_);
lean_dec(v___x_5310_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5324_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
if (lean_obj_tag(v_a_5311_) == 1)
{
lean_object* v_val_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; 
lean_del_object(v___x_5313_);
v_val_5315_ = lean_ctor_get(v_a_5311_, 0);
lean_inc_n(v_val_5315_, 2);
lean_dec_ref(v_a_5311_);
v___x_5316_ = l_Lean_Grind_Linarith_Expr_norm(v_val_5315_);
v___x_5317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5317_, 0, v_a_5300_);
lean_ctor_set(v___x_5317_, 1, v_val_5315_);
v___x_5318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5318_, 0, v___x_5316_);
lean_ctor_set(v___x_5318_, 1, v___x_5317_);
v___x_5319_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5318_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_);
return v___x_5319_;
}
else
{
lean_object* v___x_5320_; lean_object* v___x_5322_; 
lean_dec(v_a_5311_);
lean_dec(v_a_5300_);
v___x_5320_ = lean_box(0);
if (v_isShared_5314_ == 0)
{
lean_ctor_set(v___x_5313_, 0, v___x_5320_);
v___x_5322_ = v___x_5313_;
goto v_reusejp_5321_;
}
else
{
lean_object* v_reuseFailAlloc_5323_; 
v_reuseFailAlloc_5323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5323_, 0, v___x_5320_);
v___x_5322_ = v_reuseFailAlloc_5323_;
goto v_reusejp_5321_;
}
v_reusejp_5321_:
{
return v___x_5322_;
}
}
}
}
else
{
lean_object* v_a_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5332_; 
lean_dec(v_a_5300_);
v_a_5325_ = lean_ctor_get(v___x_5310_, 0);
v_isSharedCheck_5332_ = !lean_is_exclusive(v___x_5310_);
if (v_isSharedCheck_5332_ == 0)
{
v___x_5327_ = v___x_5310_;
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_a_5325_);
lean_dec(v___x_5310_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v___x_5330_; 
if (v_isShared_5328_ == 0)
{
v___x_5330_ = v___x_5327_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v_a_5325_);
v___x_5330_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
return v___x_5330_;
}
}
}
}
else
{
lean_object* v_a_5333_; lean_object* v___x_5335_; uint8_t v_isShared_5336_; uint8_t v_isSharedCheck_5340_; 
lean_dec(v___y_5307_);
lean_dec(v_a_5300_);
v_a_5333_ = lean_ctor_get(v___x_5308_, 0);
v_isSharedCheck_5340_ = !lean_is_exclusive(v___x_5308_);
if (v_isSharedCheck_5340_ == 0)
{
v___x_5335_ = v___x_5308_;
v_isShared_5336_ = v_isSharedCheck_5340_;
goto v_resetjp_5334_;
}
else
{
lean_inc(v_a_5333_);
lean_dec(v___x_5308_);
v___x_5335_ = lean_box(0);
v_isShared_5336_ = v_isSharedCheck_5340_;
goto v_resetjp_5334_;
}
v_resetjp_5334_:
{
lean_object* v___x_5338_; 
if (v_isShared_5336_ == 0)
{
v___x_5338_ = v___x_5335_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5339_; 
v_reuseFailAlloc_5339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5339_, 0, v_a_5333_);
v___x_5338_ = v_reuseFailAlloc_5339_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
return v___x_5338_;
}
}
}
}
}
else
{
lean_object* v_a_5342_; lean_object* v___x_5344_; uint8_t v_isShared_5345_; uint8_t v_isSharedCheck_5349_; 
lean_dec(v_a_5302_);
lean_dec(v_a_5300_);
v_a_5342_ = lean_ctor_get(v___x_5303_, 0);
v_isSharedCheck_5349_ = !lean_is_exclusive(v___x_5303_);
if (v_isSharedCheck_5349_ == 0)
{
v___x_5344_ = v___x_5303_;
v_isShared_5345_ = v_isSharedCheck_5349_;
goto v_resetjp_5343_;
}
else
{
lean_inc(v_a_5342_);
lean_dec(v___x_5303_);
v___x_5344_ = lean_box(0);
v_isShared_5345_ = v_isSharedCheck_5349_;
goto v_resetjp_5343_;
}
v_resetjp_5343_:
{
lean_object* v___x_5347_; 
if (v_isShared_5345_ == 0)
{
v___x_5347_ = v___x_5344_;
goto v_reusejp_5346_;
}
else
{
lean_object* v_reuseFailAlloc_5348_; 
v_reuseFailAlloc_5348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5348_, 0, v_a_5342_);
v___x_5347_ = v_reuseFailAlloc_5348_;
goto v_reusejp_5346_;
}
v_reusejp_5346_:
{
return v___x_5347_;
}
}
}
}
else
{
lean_object* v_a_5350_; lean_object* v___x_5352_; uint8_t v_isShared_5353_; uint8_t v_isSharedCheck_5357_; 
lean_dec(v_a_5300_);
lean_dec_ref(v_b_5264_);
v_a_5350_ = lean_ctor_get(v___x_5301_, 0);
v_isSharedCheck_5357_ = !lean_is_exclusive(v___x_5301_);
if (v_isSharedCheck_5357_ == 0)
{
v___x_5352_ = v___x_5301_;
v_isShared_5353_ = v_isSharedCheck_5357_;
goto v_resetjp_5351_;
}
else
{
lean_inc(v_a_5350_);
lean_dec(v___x_5301_);
v___x_5352_ = lean_box(0);
v_isShared_5353_ = v_isSharedCheck_5357_;
goto v_resetjp_5351_;
}
v_resetjp_5351_:
{
lean_object* v___x_5355_; 
if (v_isShared_5353_ == 0)
{
v___x_5355_ = v___x_5352_;
goto v_reusejp_5354_;
}
else
{
lean_object* v_reuseFailAlloc_5356_; 
v_reuseFailAlloc_5356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5356_, 0, v_a_5350_);
v___x_5355_ = v_reuseFailAlloc_5356_;
goto v_reusejp_5354_;
}
v_reusejp_5354_:
{
return v___x_5355_;
}
}
}
}
else
{
lean_object* v_a_5358_; lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5365_; 
lean_dec_ref(v_b_5264_);
lean_dec_ref(v_a_5263_);
v_a_5358_ = lean_ctor_get(v___x_5299_, 0);
v_isSharedCheck_5365_ = !lean_is_exclusive(v___x_5299_);
if (v_isSharedCheck_5365_ == 0)
{
v___x_5360_ = v___x_5299_;
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
else
{
lean_inc(v_a_5358_);
lean_dec(v___x_5299_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
lean_object* v___x_5363_; 
if (v_isShared_5361_ == 0)
{
v___x_5363_ = v___x_5360_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5358_);
v___x_5363_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
return v___x_5363_;
}
}
}
}
else
{
lean_object* v___x_5366_; lean_object* v___x_5368_; 
lean_dec(v_a_5290_);
lean_dec(v_val_5286_);
lean_dec_ref(v_b_5264_);
lean_dec_ref(v_a_5263_);
v___x_5366_ = lean_box(0);
if (v_isShared_5293_ == 0)
{
lean_ctor_set(v___x_5292_, 0, v___x_5366_);
v___x_5368_ = v___x_5292_;
goto v_reusejp_5367_;
}
else
{
lean_object* v_reuseFailAlloc_5369_; 
v_reuseFailAlloc_5369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5369_, 0, v___x_5366_);
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
lean_object* v_a_5371_; lean_object* v___x_5373_; uint8_t v_isShared_5374_; uint8_t v_isSharedCheck_5378_; 
lean_dec(v_val_5286_);
lean_dec_ref(v_b_5264_);
lean_dec_ref(v_a_5263_);
v_a_5371_ = lean_ctor_get(v___x_5289_, 0);
v_isSharedCheck_5378_ = !lean_is_exclusive(v___x_5289_);
if (v_isSharedCheck_5378_ == 0)
{
v___x_5373_ = v___x_5289_;
v_isShared_5374_ = v_isSharedCheck_5378_;
goto v_resetjp_5372_;
}
else
{
lean_inc(v_a_5371_);
lean_dec(v___x_5289_);
v___x_5373_ = lean_box(0);
v_isShared_5374_ = v_isSharedCheck_5378_;
goto v_resetjp_5372_;
}
v_resetjp_5372_:
{
lean_object* v___x_5376_; 
if (v_isShared_5374_ == 0)
{
v___x_5376_ = v___x_5373_;
goto v_reusejp_5375_;
}
else
{
lean_object* v_reuseFailAlloc_5377_; 
v_reuseFailAlloc_5377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5377_, 0, v_a_5371_);
v___x_5376_ = v_reuseFailAlloc_5377_;
goto v_reusejp_5375_;
}
v_reusejp_5375_:
{
return v___x_5376_;
}
}
}
}
else
{
lean_object* v___x_5379_; lean_object* v___x_5381_; 
lean_dec(v_a_5282_);
lean_dec_ref(v_b_5264_);
lean_dec_ref(v_a_5263_);
v___x_5379_ = lean_box(0);
if (v_isShared_5285_ == 0)
{
lean_ctor_set(v___x_5284_, 0, v___x_5379_);
v___x_5381_ = v___x_5284_;
goto v_reusejp_5380_;
}
else
{
lean_object* v_reuseFailAlloc_5382_; 
v_reuseFailAlloc_5382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5382_, 0, v___x_5379_);
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
else
{
lean_object* v_a_5384_; lean_object* v___x_5386_; uint8_t v_isShared_5387_; uint8_t v_isSharedCheck_5391_; 
lean_dec_ref(v_b_5264_);
lean_dec_ref(v_a_5263_);
v_a_5384_ = lean_ctor_get(v___x_5281_, 0);
v_isSharedCheck_5391_ = !lean_is_exclusive(v___x_5281_);
if (v_isSharedCheck_5391_ == 0)
{
v___x_5386_ = v___x_5281_;
v_isShared_5387_ = v_isSharedCheck_5391_;
goto v_resetjp_5385_;
}
else
{
lean_inc(v_a_5384_);
lean_dec(v___x_5281_);
v___x_5386_ = lean_box(0);
v_isShared_5387_ = v_isSharedCheck_5391_;
goto v_resetjp_5385_;
}
v_resetjp_5385_:
{
lean_object* v___x_5389_; 
if (v_isShared_5387_ == 0)
{
v___x_5389_ = v___x_5386_;
goto v_reusejp_5388_;
}
else
{
lean_object* v_reuseFailAlloc_5390_; 
v_reuseFailAlloc_5390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5390_, 0, v_a_5384_);
v___x_5389_ = v_reuseFailAlloc_5390_;
goto v_reusejp_5388_;
}
v_reusejp_5388_:
{
return v___x_5389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq___boxed(lean_object* v_a_5392_, lean_object* v_b_5393_, lean_object* v_a_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_){
_start:
{
lean_object* v_res_5406_; 
v_res_5406_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5392_, v_b_5393_, v_a_5394_, v_a_5395_, v_a_5396_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_);
lean_dec(v_a_5404_);
lean_dec_ref(v_a_5403_);
lean_dec(v_a_5402_);
lean_dec_ref(v_a_5401_);
lean_dec(v_a_5400_);
lean_dec_ref(v_a_5399_);
lean_dec(v_a_5398_);
lean_dec_ref(v_a_5397_);
lean_dec(v_a_5396_);
lean_dec(v_a_5395_);
lean_dec(v_a_5394_);
return v_res_5406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(lean_object* v_a_5407_, lean_object* v_b_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_){
_start:
{
lean_object* v___x_5421_; 
v___x_5421_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5407_, v_a_5410_);
if (lean_obj_tag(v___x_5421_) == 0)
{
lean_object* v_a_5422_; uint8_t v___x_5423_; lean_object* v___x_5424_; 
v_a_5422_ = lean_ctor_get(v___x_5421_, 0);
lean_inc(v_a_5422_);
lean_dec_ref(v___x_5421_);
v___x_5423_ = 0;
lean_inc_ref(v_a_5407_);
v___x_5424_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5407_, v___x_5423_, v_a_5422_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_);
if (lean_obj_tag(v___x_5424_) == 0)
{
lean_object* v_a_5425_; lean_object* v___x_5427_; uint8_t v_isShared_5428_; uint8_t v_isSharedCheck_5468_; 
v_a_5425_ = lean_ctor_get(v___x_5424_, 0);
v_isSharedCheck_5468_ = !lean_is_exclusive(v___x_5424_);
if (v_isSharedCheck_5468_ == 0)
{
v___x_5427_ = v___x_5424_;
v_isShared_5428_ = v_isSharedCheck_5468_;
goto v_resetjp_5426_;
}
else
{
lean_inc(v_a_5425_);
lean_dec(v___x_5424_);
v___x_5427_ = lean_box(0);
v_isShared_5428_ = v_isSharedCheck_5468_;
goto v_resetjp_5426_;
}
v_resetjp_5426_:
{
if (lean_obj_tag(v_a_5425_) == 1)
{
lean_object* v_val_5429_; lean_object* v___x_5430_; 
lean_del_object(v___x_5427_);
v_val_5429_ = lean_ctor_get(v_a_5425_, 0);
lean_inc(v_val_5429_);
lean_dec_ref(v_a_5425_);
v___x_5430_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5408_, v_a_5410_);
if (lean_obj_tag(v___x_5430_) == 0)
{
lean_object* v_a_5431_; lean_object* v___x_5432_; 
v_a_5431_ = lean_ctor_get(v___x_5430_, 0);
lean_inc(v_a_5431_);
lean_dec_ref(v___x_5430_);
lean_inc_ref(v_b_5408_);
v___x_5432_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_5408_, v___x_5423_, v_a_5431_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_);
if (lean_obj_tag(v___x_5432_) == 0)
{
lean_object* v_a_5433_; lean_object* v___x_5435_; uint8_t v_isShared_5436_; uint8_t v_isSharedCheck_5447_; 
v_a_5433_ = lean_ctor_get(v___x_5432_, 0);
v_isSharedCheck_5447_ = !lean_is_exclusive(v___x_5432_);
if (v_isSharedCheck_5447_ == 0)
{
v___x_5435_ = v___x_5432_;
v_isShared_5436_ = v_isSharedCheck_5447_;
goto v_resetjp_5434_;
}
else
{
lean_inc(v_a_5433_);
lean_dec(v___x_5432_);
v___x_5435_ = lean_box(0);
v_isShared_5436_ = v_isSharedCheck_5447_;
goto v_resetjp_5434_;
}
v_resetjp_5434_:
{
if (lean_obj_tag(v_a_5433_) == 1)
{
lean_object* v_val_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; 
lean_del_object(v___x_5435_);
v_val_5437_ = lean_ctor_get(v_a_5433_, 0);
lean_inc_n(v_val_5437_, 2);
lean_dec_ref(v_a_5433_);
lean_inc(v_val_5429_);
v___x_5438_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5438_, 0, v_val_5429_);
lean_ctor_set(v___x_5438_, 1, v_val_5437_);
v___x_5439_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5438_);
v___x_5440_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5440_, 0, v_a_5407_);
lean_ctor_set(v___x_5440_, 1, v_b_5408_);
lean_ctor_set(v___x_5440_, 2, v_val_5429_);
lean_ctor_set(v___x_5440_, 3, v_val_5437_);
v___x_5441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5441_, 0, v___x_5439_);
lean_ctor_set(v___x_5441_, 1, v___x_5440_);
v___x_5442_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5441_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_);
return v___x_5442_;
}
else
{
lean_object* v___x_5443_; lean_object* v___x_5445_; 
lean_dec(v_a_5433_);
lean_dec(v_val_5429_);
lean_dec_ref(v_b_5408_);
lean_dec_ref(v_a_5407_);
v___x_5443_ = lean_box(0);
if (v_isShared_5436_ == 0)
{
lean_ctor_set(v___x_5435_, 0, v___x_5443_);
v___x_5445_ = v___x_5435_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5446_; 
v_reuseFailAlloc_5446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5446_, 0, v___x_5443_);
v___x_5445_ = v_reuseFailAlloc_5446_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
return v___x_5445_;
}
}
}
}
else
{
lean_object* v_a_5448_; lean_object* v___x_5450_; uint8_t v_isShared_5451_; uint8_t v_isSharedCheck_5455_; 
lean_dec(v_val_5429_);
lean_dec_ref(v_b_5408_);
lean_dec_ref(v_a_5407_);
v_a_5448_ = lean_ctor_get(v___x_5432_, 0);
v_isSharedCheck_5455_ = !lean_is_exclusive(v___x_5432_);
if (v_isSharedCheck_5455_ == 0)
{
v___x_5450_ = v___x_5432_;
v_isShared_5451_ = v_isSharedCheck_5455_;
goto v_resetjp_5449_;
}
else
{
lean_inc(v_a_5448_);
lean_dec(v___x_5432_);
v___x_5450_ = lean_box(0);
v_isShared_5451_ = v_isSharedCheck_5455_;
goto v_resetjp_5449_;
}
v_resetjp_5449_:
{
lean_object* v___x_5453_; 
if (v_isShared_5451_ == 0)
{
v___x_5453_ = v___x_5450_;
goto v_reusejp_5452_;
}
else
{
lean_object* v_reuseFailAlloc_5454_; 
v_reuseFailAlloc_5454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5454_, 0, v_a_5448_);
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
lean_dec(v_val_5429_);
lean_dec_ref(v_b_5408_);
lean_dec_ref(v_a_5407_);
v_a_5456_ = lean_ctor_get(v___x_5430_, 0);
v_isSharedCheck_5463_ = !lean_is_exclusive(v___x_5430_);
if (v_isSharedCheck_5463_ == 0)
{
v___x_5458_ = v___x_5430_;
v_isShared_5459_ = v_isSharedCheck_5463_;
goto v_resetjp_5457_;
}
else
{
lean_inc(v_a_5456_);
lean_dec(v___x_5430_);
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
lean_dec(v_a_5425_);
lean_dec_ref(v_b_5408_);
lean_dec_ref(v_a_5407_);
v___x_5464_ = lean_box(0);
if (v_isShared_5428_ == 0)
{
lean_ctor_set(v___x_5427_, 0, v___x_5464_);
v___x_5466_ = v___x_5427_;
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
lean_dec_ref(v_b_5408_);
lean_dec_ref(v_a_5407_);
v_a_5469_ = lean_ctor_get(v___x_5424_, 0);
v_isSharedCheck_5476_ = !lean_is_exclusive(v___x_5424_);
if (v_isSharedCheck_5476_ == 0)
{
v___x_5471_ = v___x_5424_;
v_isShared_5472_ = v_isSharedCheck_5476_;
goto v_resetjp_5470_;
}
else
{
lean_inc(v_a_5469_);
lean_dec(v___x_5424_);
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
else
{
lean_object* v_a_5477_; lean_object* v___x_5479_; uint8_t v_isShared_5480_; uint8_t v_isSharedCheck_5484_; 
lean_dec_ref(v_b_5408_);
lean_dec_ref(v_a_5407_);
v_a_5477_ = lean_ctor_get(v___x_5421_, 0);
v_isSharedCheck_5484_ = !lean_is_exclusive(v___x_5421_);
if (v_isSharedCheck_5484_ == 0)
{
v___x_5479_ = v___x_5421_;
v_isShared_5480_ = v_isSharedCheck_5484_;
goto v_resetjp_5478_;
}
else
{
lean_inc(v_a_5477_);
lean_dec(v___x_5421_);
v___x_5479_ = lean_box(0);
v_isShared_5480_ = v_isSharedCheck_5484_;
goto v_resetjp_5478_;
}
v_resetjp_5478_:
{
lean_object* v___x_5482_; 
if (v_isShared_5480_ == 0)
{
v___x_5482_ = v___x_5479_;
goto v_reusejp_5481_;
}
else
{
lean_object* v_reuseFailAlloc_5483_; 
v_reuseFailAlloc_5483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5483_, 0, v_a_5477_);
v___x_5482_ = v_reuseFailAlloc_5483_;
goto v_reusejp_5481_;
}
v_reusejp_5481_:
{
return v___x_5482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq___boxed(lean_object* v_a_5485_, lean_object* v_b_5486_, lean_object* v_a_5487_, lean_object* v_a_5488_, lean_object* v_a_5489_, lean_object* v_a_5490_, lean_object* v_a_5491_, lean_object* v_a_5492_, lean_object* v_a_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_){
_start:
{
lean_object* v_res_5499_; 
v_res_5499_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5485_, v_b_5486_, v_a_5487_, v_a_5488_, v_a_5489_, v_a_5490_, v_a_5491_, v_a_5492_, v_a_5493_, v_a_5494_, v_a_5495_, v_a_5496_, v_a_5497_);
lean_dec(v_a_5497_);
lean_dec_ref(v_a_5496_);
lean_dec(v_a_5495_);
lean_dec_ref(v_a_5494_);
lean_dec(v_a_5493_);
lean_dec_ref(v_a_5492_);
lean_dec(v_a_5491_);
lean_dec_ref(v_a_5490_);
lean_dec(v_a_5489_);
lean_dec(v_a_5488_);
lean_dec(v_a_5487_);
return v_res_5499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(lean_object* v_a_5500_, lean_object* v_b_5501_, lean_object* v_a_5502_, lean_object* v_a_5503_, lean_object* v_a_5504_, lean_object* v_a_5505_, lean_object* v_a_5506_, lean_object* v_a_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_){
_start:
{
lean_object* v___x_5514_; 
v___x_5514_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_);
if (lean_obj_tag(v___x_5514_) == 0)
{
lean_object* v_a_5515_; lean_object* v_addRightCancelInst_x3f_5516_; 
v_a_5515_ = lean_ctor_get(v___x_5514_, 0);
lean_inc(v_a_5515_);
lean_dec_ref(v___x_5514_);
v_addRightCancelInst_x3f_5516_ = lean_ctor_get(v_a_5515_, 11);
if (lean_obj_tag(v_addRightCancelInst_x3f_5516_) == 0)
{
lean_object* v___x_5517_; 
lean_dec(v_a_5515_);
v___x_5517_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(v_a_5500_, v_b_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_);
return v___x_5517_;
}
else
{
lean_object* v_id_5518_; lean_object* v_structId_5519_; lean_object* v___x_5520_; 
v_id_5518_ = lean_ctor_get(v_a_5515_, 0);
lean_inc(v_id_5518_);
v_structId_5519_ = lean_ctor_get(v_a_5515_, 1);
lean_inc(v_structId_5519_);
lean_dec(v_a_5515_);
lean_inc_ref(v_a_5500_);
v___x_5520_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5500_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_);
if (lean_obj_tag(v___x_5520_) == 0)
{
lean_object* v_a_5521_; lean_object* v_fst_5522_; lean_object* v___x_5524_; uint8_t v_isShared_5525_; uint8_t v_isSharedCheck_5610_; 
v_a_5521_ = lean_ctor_get(v___x_5520_, 0);
lean_inc(v_a_5521_);
lean_dec_ref(v___x_5520_);
v_fst_5522_ = lean_ctor_get(v_a_5521_, 0);
v_isSharedCheck_5610_ = !lean_is_exclusive(v_a_5521_);
if (v_isSharedCheck_5610_ == 0)
{
lean_object* v_unused_5611_; 
v_unused_5611_ = lean_ctor_get(v_a_5521_, 1);
lean_dec(v_unused_5611_);
v___x_5524_ = v_a_5521_;
v_isShared_5525_ = v_isSharedCheck_5610_;
goto v_resetjp_5523_;
}
else
{
lean_inc(v_fst_5522_);
lean_dec(v_a_5521_);
v___x_5524_ = lean_box(0);
v_isShared_5525_ = v_isSharedCheck_5610_;
goto v_resetjp_5523_;
}
v_resetjp_5523_:
{
lean_object* v___x_5526_; 
lean_inc_ref(v_b_5501_);
v___x_5526_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_);
if (lean_obj_tag(v___x_5526_) == 0)
{
lean_object* v_a_5527_; lean_object* v_fst_5528_; lean_object* v___x_5530_; uint8_t v_isShared_5531_; uint8_t v_isSharedCheck_5600_; 
v_a_5527_ = lean_ctor_get(v___x_5526_, 0);
lean_inc(v_a_5527_);
lean_dec_ref(v___x_5526_);
v_fst_5528_ = lean_ctor_get(v_a_5527_, 0);
v_isSharedCheck_5600_ = !lean_is_exclusive(v_a_5527_);
if (v_isSharedCheck_5600_ == 0)
{
lean_object* v_unused_5601_; 
v_unused_5601_ = lean_ctor_get(v_a_5527_, 1);
lean_dec(v_unused_5601_);
v___x_5530_ = v_a_5527_;
v_isShared_5531_ = v_isSharedCheck_5600_;
goto v_resetjp_5529_;
}
else
{
lean_inc(v_fst_5528_);
lean_dec(v_a_5527_);
v___x_5530_ = lean_box(0);
v_isShared_5531_ = v_isSharedCheck_5600_;
goto v_resetjp_5529_;
}
v_resetjp_5529_:
{
lean_object* v___x_5532_; 
v___x_5532_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5500_, v_a_5503_);
if (lean_obj_tag(v___x_5532_) == 0)
{
lean_object* v_a_5533_; uint8_t v___x_5534_; lean_object* v___x_5535_; 
v_a_5533_ = lean_ctor_get(v___x_5532_, 0);
lean_inc(v_a_5533_);
lean_dec_ref(v___x_5532_);
v___x_5534_ = 0;
v___x_5535_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5522_, v___x_5534_, v_a_5533_, v_structId_5519_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_);
if (lean_obj_tag(v___x_5535_) == 0)
{
lean_object* v_a_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5583_; 
v_a_5536_ = lean_ctor_get(v___x_5535_, 0);
v_isSharedCheck_5583_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5583_ == 0)
{
v___x_5538_ = v___x_5535_;
v_isShared_5539_ = v_isSharedCheck_5583_;
goto v_resetjp_5537_;
}
else
{
lean_inc(v_a_5536_);
lean_dec(v___x_5535_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5583_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
if (lean_obj_tag(v_a_5536_) == 1)
{
lean_object* v_val_5540_; lean_object* v___x_5541_; 
lean_del_object(v___x_5538_);
v_val_5540_ = lean_ctor_get(v_a_5536_, 0);
lean_inc(v_val_5540_);
lean_dec_ref(v_a_5536_);
v___x_5541_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5501_, v_a_5503_);
if (lean_obj_tag(v___x_5541_) == 0)
{
lean_object* v_a_5542_; lean_object* v___x_5543_; 
v_a_5542_ = lean_ctor_get(v___x_5541_, 0);
lean_inc(v_a_5542_);
lean_dec_ref(v___x_5541_);
v___x_5543_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5528_, v___x_5534_, v_a_5542_, v_structId_5519_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_);
if (lean_obj_tag(v___x_5543_) == 0)
{
lean_object* v_a_5544_; lean_object* v___x_5546_; uint8_t v_isShared_5547_; uint8_t v_isSharedCheck_5562_; 
v_a_5544_ = lean_ctor_get(v___x_5543_, 0);
v_isSharedCheck_5562_ = !lean_is_exclusive(v___x_5543_);
if (v_isSharedCheck_5562_ == 0)
{
v___x_5546_ = v___x_5543_;
v_isShared_5547_ = v_isSharedCheck_5562_;
goto v_resetjp_5545_;
}
else
{
lean_inc(v_a_5544_);
lean_dec(v___x_5543_);
v___x_5546_ = lean_box(0);
v_isShared_5547_ = v_isSharedCheck_5562_;
goto v_resetjp_5545_;
}
v_resetjp_5545_:
{
if (lean_obj_tag(v_a_5544_) == 1)
{
lean_object* v_val_5548_; lean_object* v___x_5550_; 
lean_del_object(v___x_5546_);
v_val_5548_ = lean_ctor_get(v_a_5544_, 0);
lean_inc_n(v_val_5548_, 2);
lean_dec_ref(v_a_5544_);
lean_inc(v_val_5540_);
if (v_isShared_5531_ == 0)
{
lean_ctor_set_tag(v___x_5530_, 3);
lean_ctor_set(v___x_5530_, 1, v_val_5548_);
lean_ctor_set(v___x_5530_, 0, v_val_5540_);
v___x_5550_ = v___x_5530_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v_val_5540_);
lean_ctor_set(v_reuseFailAlloc_5557_, 1, v_val_5548_);
v___x_5550_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5554_; 
v___x_5551_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5550_);
v___x_5552_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5552_, 0, v_a_5500_);
lean_ctor_set(v___x_5552_, 1, v_b_5501_);
lean_ctor_set(v___x_5552_, 2, v_id_5518_);
lean_ctor_set(v___x_5552_, 3, v_val_5540_);
lean_ctor_set(v___x_5552_, 4, v_val_5548_);
if (v_isShared_5525_ == 0)
{
lean_ctor_set(v___x_5524_, 1, v___x_5552_);
lean_ctor_set(v___x_5524_, 0, v___x_5551_);
v___x_5554_ = v___x_5524_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5556_; 
v_reuseFailAlloc_5556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5556_, 0, v___x_5551_);
lean_ctor_set(v_reuseFailAlloc_5556_, 1, v___x_5552_);
v___x_5554_ = v_reuseFailAlloc_5556_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
lean_object* v___x_5555_; 
v___x_5555_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5554_, v_structId_5519_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_);
lean_dec(v_structId_5519_);
return v___x_5555_;
}
}
}
else
{
lean_object* v___x_5558_; lean_object* v___x_5560_; 
lean_dec(v_a_5544_);
lean_dec(v_val_5540_);
lean_del_object(v___x_5530_);
lean_del_object(v___x_5524_);
lean_dec(v_structId_5519_);
lean_dec(v_id_5518_);
lean_dec_ref(v_b_5501_);
lean_dec_ref(v_a_5500_);
v___x_5558_ = lean_box(0);
if (v_isShared_5547_ == 0)
{
lean_ctor_set(v___x_5546_, 0, v___x_5558_);
v___x_5560_ = v___x_5546_;
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
lean_dec(v_val_5540_);
lean_del_object(v___x_5530_);
lean_del_object(v___x_5524_);
lean_dec(v_structId_5519_);
lean_dec(v_id_5518_);
lean_dec_ref(v_b_5501_);
lean_dec_ref(v_a_5500_);
v_a_5563_ = lean_ctor_get(v___x_5543_, 0);
v_isSharedCheck_5570_ = !lean_is_exclusive(v___x_5543_);
if (v_isSharedCheck_5570_ == 0)
{
v___x_5565_ = v___x_5543_;
v_isShared_5566_ = v_isSharedCheck_5570_;
goto v_resetjp_5564_;
}
else
{
lean_inc(v_a_5563_);
lean_dec(v___x_5543_);
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
else
{
lean_object* v_a_5571_; lean_object* v___x_5573_; uint8_t v_isShared_5574_; uint8_t v_isSharedCheck_5578_; 
lean_dec(v_val_5540_);
lean_del_object(v___x_5530_);
lean_dec(v_fst_5528_);
lean_del_object(v___x_5524_);
lean_dec(v_structId_5519_);
lean_dec(v_id_5518_);
lean_dec_ref(v_b_5501_);
lean_dec_ref(v_a_5500_);
v_a_5571_ = lean_ctor_get(v___x_5541_, 0);
v_isSharedCheck_5578_ = !lean_is_exclusive(v___x_5541_);
if (v_isSharedCheck_5578_ == 0)
{
v___x_5573_ = v___x_5541_;
v_isShared_5574_ = v_isSharedCheck_5578_;
goto v_resetjp_5572_;
}
else
{
lean_inc(v_a_5571_);
lean_dec(v___x_5541_);
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
else
{
lean_object* v___x_5579_; lean_object* v___x_5581_; 
lean_dec(v_a_5536_);
lean_del_object(v___x_5530_);
lean_dec(v_fst_5528_);
lean_del_object(v___x_5524_);
lean_dec(v_structId_5519_);
lean_dec(v_id_5518_);
lean_dec_ref(v_b_5501_);
lean_dec_ref(v_a_5500_);
v___x_5579_ = lean_box(0);
if (v_isShared_5539_ == 0)
{
lean_ctor_set(v___x_5538_, 0, v___x_5579_);
v___x_5581_ = v___x_5538_;
goto v_reusejp_5580_;
}
else
{
lean_object* v_reuseFailAlloc_5582_; 
v_reuseFailAlloc_5582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5582_, 0, v___x_5579_);
v___x_5581_ = v_reuseFailAlloc_5582_;
goto v_reusejp_5580_;
}
v_reusejp_5580_:
{
return v___x_5581_;
}
}
}
}
else
{
lean_object* v_a_5584_; lean_object* v___x_5586_; uint8_t v_isShared_5587_; uint8_t v_isSharedCheck_5591_; 
lean_del_object(v___x_5530_);
lean_dec(v_fst_5528_);
lean_del_object(v___x_5524_);
lean_dec(v_structId_5519_);
lean_dec(v_id_5518_);
lean_dec_ref(v_b_5501_);
lean_dec_ref(v_a_5500_);
v_a_5584_ = lean_ctor_get(v___x_5535_, 0);
v_isSharedCheck_5591_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5591_ == 0)
{
v___x_5586_ = v___x_5535_;
v_isShared_5587_ = v_isSharedCheck_5591_;
goto v_resetjp_5585_;
}
else
{
lean_inc(v_a_5584_);
lean_dec(v___x_5535_);
v___x_5586_ = lean_box(0);
v_isShared_5587_ = v_isSharedCheck_5591_;
goto v_resetjp_5585_;
}
v_resetjp_5585_:
{
lean_object* v___x_5589_; 
if (v_isShared_5587_ == 0)
{
v___x_5589_ = v___x_5586_;
goto v_reusejp_5588_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v_a_5584_);
v___x_5589_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5588_;
}
v_reusejp_5588_:
{
return v___x_5589_;
}
}
}
}
else
{
lean_object* v_a_5592_; lean_object* v___x_5594_; uint8_t v_isShared_5595_; uint8_t v_isSharedCheck_5599_; 
lean_del_object(v___x_5530_);
lean_dec(v_fst_5528_);
lean_del_object(v___x_5524_);
lean_dec(v_fst_5522_);
lean_dec(v_structId_5519_);
lean_dec(v_id_5518_);
lean_dec_ref(v_b_5501_);
lean_dec_ref(v_a_5500_);
v_a_5592_ = lean_ctor_get(v___x_5532_, 0);
v_isSharedCheck_5599_ = !lean_is_exclusive(v___x_5532_);
if (v_isSharedCheck_5599_ == 0)
{
v___x_5594_ = v___x_5532_;
v_isShared_5595_ = v_isSharedCheck_5599_;
goto v_resetjp_5593_;
}
else
{
lean_inc(v_a_5592_);
lean_dec(v___x_5532_);
v___x_5594_ = lean_box(0);
v_isShared_5595_ = v_isSharedCheck_5599_;
goto v_resetjp_5593_;
}
v_resetjp_5593_:
{
lean_object* v___x_5597_; 
if (v_isShared_5595_ == 0)
{
v___x_5597_ = v___x_5594_;
goto v_reusejp_5596_;
}
else
{
lean_object* v_reuseFailAlloc_5598_; 
v_reuseFailAlloc_5598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5598_, 0, v_a_5592_);
v___x_5597_ = v_reuseFailAlloc_5598_;
goto v_reusejp_5596_;
}
v_reusejp_5596_:
{
return v___x_5597_;
}
}
}
}
}
else
{
lean_object* v_a_5602_; lean_object* v___x_5604_; uint8_t v_isShared_5605_; uint8_t v_isSharedCheck_5609_; 
lean_del_object(v___x_5524_);
lean_dec(v_fst_5522_);
lean_dec(v_structId_5519_);
lean_dec(v_id_5518_);
lean_dec_ref(v_b_5501_);
lean_dec_ref(v_a_5500_);
v_a_5602_ = lean_ctor_get(v___x_5526_, 0);
v_isSharedCheck_5609_ = !lean_is_exclusive(v___x_5526_);
if (v_isSharedCheck_5609_ == 0)
{
v___x_5604_ = v___x_5526_;
v_isShared_5605_ = v_isSharedCheck_5609_;
goto v_resetjp_5603_;
}
else
{
lean_inc(v_a_5602_);
lean_dec(v___x_5526_);
v___x_5604_ = lean_box(0);
v_isShared_5605_ = v_isSharedCheck_5609_;
goto v_resetjp_5603_;
}
v_resetjp_5603_:
{
lean_object* v___x_5607_; 
if (v_isShared_5605_ == 0)
{
v___x_5607_ = v___x_5604_;
goto v_reusejp_5606_;
}
else
{
lean_object* v_reuseFailAlloc_5608_; 
v_reuseFailAlloc_5608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5608_, 0, v_a_5602_);
v___x_5607_ = v_reuseFailAlloc_5608_;
goto v_reusejp_5606_;
}
v_reusejp_5606_:
{
return v___x_5607_;
}
}
}
}
}
else
{
lean_object* v_a_5612_; lean_object* v___x_5614_; uint8_t v_isShared_5615_; uint8_t v_isSharedCheck_5619_; 
lean_dec(v_structId_5519_);
lean_dec(v_id_5518_);
lean_dec_ref(v_b_5501_);
lean_dec_ref(v_a_5500_);
v_a_5612_ = lean_ctor_get(v___x_5520_, 0);
v_isSharedCheck_5619_ = !lean_is_exclusive(v___x_5520_);
if (v_isSharedCheck_5619_ == 0)
{
v___x_5614_ = v___x_5520_;
v_isShared_5615_ = v_isSharedCheck_5619_;
goto v_resetjp_5613_;
}
else
{
lean_inc(v_a_5612_);
lean_dec(v___x_5520_);
v___x_5614_ = lean_box(0);
v_isShared_5615_ = v_isSharedCheck_5619_;
goto v_resetjp_5613_;
}
v_resetjp_5613_:
{
lean_object* v___x_5617_; 
if (v_isShared_5615_ == 0)
{
v___x_5617_ = v___x_5614_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5618_; 
v_reuseFailAlloc_5618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5618_, 0, v_a_5612_);
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
}
else
{
lean_object* v_a_5620_; lean_object* v___x_5622_; uint8_t v_isShared_5623_; uint8_t v_isSharedCheck_5627_; 
lean_dec_ref(v_b_5501_);
lean_dec_ref(v_a_5500_);
v_a_5620_ = lean_ctor_get(v___x_5514_, 0);
v_isSharedCheck_5627_ = !lean_is_exclusive(v___x_5514_);
if (v_isSharedCheck_5627_ == 0)
{
v___x_5622_ = v___x_5514_;
v_isShared_5623_ = v_isSharedCheck_5627_;
goto v_resetjp_5621_;
}
else
{
lean_inc(v_a_5620_);
lean_dec(v___x_5514_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq___boxed(lean_object* v_a_5628_, lean_object* v_b_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_, lean_object* v_a_5638_, lean_object* v_a_5639_, lean_object* v_a_5640_, lean_object* v_a_5641_){
_start:
{
lean_object* v_res_5642_; 
v_res_5642_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5628_, v_b_5629_, v_a_5630_, v_a_5631_, v_a_5632_, v_a_5633_, v_a_5634_, v_a_5635_, v_a_5636_, v_a_5637_, v_a_5638_, v_a_5639_, v_a_5640_);
lean_dec(v_a_5640_);
lean_dec_ref(v_a_5639_);
lean_dec(v_a_5638_);
lean_dec_ref(v_a_5637_);
lean_dec(v_a_5636_);
lean_dec_ref(v_a_5635_);
lean_dec(v_a_5634_);
lean_dec_ref(v_a_5633_);
lean_dec(v_a_5632_);
lean_dec(v_a_5631_);
lean_dec(v_a_5630_);
return v_res_5642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(lean_object* v_a_5643_, lean_object* v_b_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_){
_start:
{
lean_object* v___x_5656_; 
v___x_5656_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5643_, v_b_5644_, v_a_5645_, v_a_5653_);
if (lean_obj_tag(v___x_5656_) == 0)
{
lean_object* v_a_5657_; 
v_a_5657_ = lean_ctor_get(v___x_5656_, 0);
lean_inc(v_a_5657_);
lean_dec_ref(v___x_5656_);
if (lean_obj_tag(v_a_5657_) == 1)
{
lean_object* v_val_5658_; lean_object* v___x_5659_; 
v_val_5658_ = lean_ctor_get(v_a_5657_, 0);
lean_inc(v_val_5658_);
lean_dec_ref(v_a_5657_);
v___x_5659_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5658_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_);
if (lean_obj_tag(v___x_5659_) == 0)
{
lean_object* v_a_5660_; uint8_t v___x_5661_; 
v_a_5660_ = lean_ctor_get(v___x_5659_, 0);
lean_inc(v_a_5660_);
lean_dec_ref(v___x_5659_);
v___x_5661_ = lean_unbox(v_a_5660_);
lean_dec(v_a_5660_);
if (v___x_5661_ == 0)
{
lean_object* v___x_5662_; 
v___x_5662_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5643_, v_b_5644_, v_val_5658_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_);
lean_dec(v_val_5658_);
return v___x_5662_;
}
else
{
lean_object* v___x_5663_; 
v___x_5663_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5643_, v_b_5644_, v_val_5658_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_);
lean_dec(v_val_5658_);
return v___x_5663_;
}
}
else
{
lean_object* v_a_5664_; lean_object* v___x_5666_; uint8_t v_isShared_5667_; uint8_t v_isSharedCheck_5671_; 
lean_dec(v_val_5658_);
lean_dec_ref(v_b_5644_);
lean_dec_ref(v_a_5643_);
v_a_5664_ = lean_ctor_get(v___x_5659_, 0);
v_isSharedCheck_5671_ = !lean_is_exclusive(v___x_5659_);
if (v_isSharedCheck_5671_ == 0)
{
v___x_5666_ = v___x_5659_;
v_isShared_5667_ = v_isSharedCheck_5671_;
goto v_resetjp_5665_;
}
else
{
lean_inc(v_a_5664_);
lean_dec(v___x_5659_);
v___x_5666_ = lean_box(0);
v_isShared_5667_ = v_isSharedCheck_5671_;
goto v_resetjp_5665_;
}
v_resetjp_5665_:
{
lean_object* v___x_5669_; 
if (v_isShared_5667_ == 0)
{
v___x_5669_ = v___x_5666_;
goto v_reusejp_5668_;
}
else
{
lean_object* v_reuseFailAlloc_5670_; 
v_reuseFailAlloc_5670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5670_, 0, v_a_5664_);
v___x_5669_ = v_reuseFailAlloc_5670_;
goto v_reusejp_5668_;
}
v_reusejp_5668_:
{
return v___x_5669_;
}
}
}
}
else
{
lean_object* v___x_5672_; 
lean_dec(v_a_5657_);
v___x_5672_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5643_, v_b_5644_, v_a_5645_, v_a_5653_);
if (lean_obj_tag(v___x_5672_) == 0)
{
lean_object* v_a_5673_; lean_object* v___x_5675_; uint8_t v_isShared_5676_; uint8_t v_isSharedCheck_5683_; 
v_a_5673_ = lean_ctor_get(v___x_5672_, 0);
v_isSharedCheck_5683_ = !lean_is_exclusive(v___x_5672_);
if (v_isSharedCheck_5683_ == 0)
{
v___x_5675_ = v___x_5672_;
v_isShared_5676_ = v_isSharedCheck_5683_;
goto v_resetjp_5674_;
}
else
{
lean_inc(v_a_5673_);
lean_dec(v___x_5672_);
v___x_5675_ = lean_box(0);
v_isShared_5676_ = v_isSharedCheck_5683_;
goto v_resetjp_5674_;
}
v_resetjp_5674_:
{
if (lean_obj_tag(v_a_5673_) == 1)
{
lean_object* v_val_5677_; lean_object* v___x_5678_; 
lean_del_object(v___x_5675_);
v_val_5677_ = lean_ctor_get(v_a_5673_, 0);
lean_inc(v_val_5677_);
lean_dec_ref(v_a_5673_);
v___x_5678_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5643_, v_b_5644_, v_val_5677_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_);
lean_dec(v_val_5677_);
return v___x_5678_;
}
else
{
lean_object* v___x_5679_; lean_object* v___x_5681_; 
lean_dec(v_a_5673_);
lean_dec_ref(v_b_5644_);
lean_dec_ref(v_a_5643_);
v___x_5679_ = lean_box(0);
if (v_isShared_5676_ == 0)
{
lean_ctor_set(v___x_5675_, 0, v___x_5679_);
v___x_5681_ = v___x_5675_;
goto v_reusejp_5680_;
}
else
{
lean_object* v_reuseFailAlloc_5682_; 
v_reuseFailAlloc_5682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5682_, 0, v___x_5679_);
v___x_5681_ = v_reuseFailAlloc_5682_;
goto v_reusejp_5680_;
}
v_reusejp_5680_:
{
return v___x_5681_;
}
}
}
}
else
{
lean_object* v_a_5684_; lean_object* v___x_5686_; uint8_t v_isShared_5687_; uint8_t v_isSharedCheck_5691_; 
lean_dec_ref(v_b_5644_);
lean_dec_ref(v_a_5643_);
v_a_5684_ = lean_ctor_get(v___x_5672_, 0);
v_isSharedCheck_5691_ = !lean_is_exclusive(v___x_5672_);
if (v_isSharedCheck_5691_ == 0)
{
v___x_5686_ = v___x_5672_;
v_isShared_5687_ = v_isSharedCheck_5691_;
goto v_resetjp_5685_;
}
else
{
lean_inc(v_a_5684_);
lean_dec(v___x_5672_);
v___x_5686_ = lean_box(0);
v_isShared_5687_ = v_isSharedCheck_5691_;
goto v_resetjp_5685_;
}
v_resetjp_5685_:
{
lean_object* v___x_5689_; 
if (v_isShared_5687_ == 0)
{
v___x_5689_ = v___x_5686_;
goto v_reusejp_5688_;
}
else
{
lean_object* v_reuseFailAlloc_5690_; 
v_reuseFailAlloc_5690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5690_, 0, v_a_5684_);
v___x_5689_ = v_reuseFailAlloc_5690_;
goto v_reusejp_5688_;
}
v_reusejp_5688_:
{
return v___x_5689_;
}
}
}
}
}
else
{
lean_object* v_a_5692_; lean_object* v___x_5694_; uint8_t v_isShared_5695_; uint8_t v_isSharedCheck_5699_; 
lean_dec_ref(v_b_5644_);
lean_dec_ref(v_a_5643_);
v_a_5692_ = lean_ctor_get(v___x_5656_, 0);
v_isSharedCheck_5699_ = !lean_is_exclusive(v___x_5656_);
if (v_isSharedCheck_5699_ == 0)
{
v___x_5694_ = v___x_5656_;
v_isShared_5695_ = v_isSharedCheck_5699_;
goto v_resetjp_5693_;
}
else
{
lean_inc(v_a_5692_);
lean_dec(v___x_5656_);
v___x_5694_ = lean_box(0);
v_isShared_5695_ = v_isSharedCheck_5699_;
goto v_resetjp_5693_;
}
v_resetjp_5693_:
{
lean_object* v___x_5697_; 
if (v_isShared_5695_ == 0)
{
v___x_5697_ = v___x_5694_;
goto v_reusejp_5696_;
}
else
{
lean_object* v_reuseFailAlloc_5698_; 
v_reuseFailAlloc_5698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5698_, 0, v_a_5692_);
v___x_5697_ = v_reuseFailAlloc_5698_;
goto v_reusejp_5696_;
}
v_reusejp_5696_:
{
return v___x_5697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed(lean_object* v_a_5700_, lean_object* v_b_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_, lean_object* v_a_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_, lean_object* v_a_5712_){
_start:
{
lean_object* v_res_5713_; 
v_res_5713_ = l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(v_a_5700_, v_b_5701_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_, v_a_5711_);
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
return v_res_5713_;
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
