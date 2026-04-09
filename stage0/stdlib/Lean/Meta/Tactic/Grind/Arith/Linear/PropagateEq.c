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
lean_dec_ref(v___x_460_);
v___x_462_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_432_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref(v___x_462_);
v___x_464_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_426_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_466_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref(v___x_464_);
v___x_466_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v___x_443_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_467_);
lean_dec_ref(v___x_466_);
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
lean_dec_ref(v___x_489_);
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
lean_dec_ref(v___x_606_);
v___x_608_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v_ofNatZero_610_; lean_object* v___x_611_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref(v___x_608_);
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
lean_dec_ref(v___x_729_);
v___x_731_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_654_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_733_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref(v___x_731_);
v___x_733_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_u2082_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref(v___x_733_);
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
lean_dec_ref(v___x_743_);
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
lean_dec_ref(v_a_806_);
v___x_811_ = lean_nat_dec_eq(v_val_804_, v_val_810_);
lean_dec(v_val_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; lean_object* v___x_814_; 
lean_dec_ref(v_a_800_);
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
lean_dec_ref(v_a_800_);
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
lean_dec_ref(v_a_800_);
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
lean_dec_ref(v_a_884_);
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
lean_dec_ref(v_a_892_);
v___x_897_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_865_, v_a_868_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_899_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref(v___x_897_);
v___x_899_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_866_, v_a_868_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___y_902_; uint8_t v___x_1001_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref(v___x_899_);
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
lean_dec_ref(v___x_907_);
v_p_909_ = lean_ctor_get(v_a_908_, 0);
lean_inc(v___y_902_);
lean_inc_ref(v_p_909_);
v___x_910_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_909_, v___y_902_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_912_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref(v___x_910_);
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
lean_dec_ref(v_a_913_);
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
lean_dec_ref(v___x_932_);
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
lean_dec_ref(v_a_935_);
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
lean_dec_ref(v___x_931_);
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
lean_dec_ref(v___x_931_);
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
lean_dec_ref(v___x_931_);
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
lean_dec_ref(v___x_1073_);
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
lean_dec_ref(v_a_1077_);
v___x_1082_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1060_, v_a_1062_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1084_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref(v___x_1082_);
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
lean_dec_ref(v_a_1085_);
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
lean_dec_ref(v___x_1096_);
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
lean_object* v___x_1177_; lean_object* v___f_1178_; lean_object* v___x_3480__overap_1179_; lean_object* v___x_1180_; 
v___x_1177_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm_spec__0___closed__0);
v___f_1178_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1178_, 0, v___x_1177_);
v___x_3480__overap_1179_ = lean_panic_fn_borrowed(v___f_1178_, v_msg_1164_);
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
v___x_1180_ = lean_apply_12(v___x_3480__overap_1179_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, lean_box(0));
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
lean_dec_ref(v___x_1227_);
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
v_c_1230_ = v___x_1276_;
v_p_1231_ = v___x_1274_;
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
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec_ref(v_c_1206_);
v_a_1277_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1227_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1227_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm___boxed(lean_object* v_c_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_c_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1291_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
lean_dec(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec(v_a_1286_);
return v_res_1298_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = l_Lean_maxRecDepthErrorMessage;
v___x_1305_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
return v___x_1305_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_1307_ = l_Lean_MessageData_ofFormat(v___x_1306_);
return v___x_1307_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1308_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_1309_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_1310_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set(v___x_1310_, 1, v___x_1308_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_1311_){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_1314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1314_, 0, v_ref_1311_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1316_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_1319_, lean_object* v_ref_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1320_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_1334_, lean_object* v_ref_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0(v_00_u03b1_1334_, v_ref_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec(v___y_1336_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(lean_object* v_c_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v_p_1380_; lean_object* v_fileName_1381_; lean_object* v_fileMap_1382_; lean_object* v_options_1383_; lean_object* v_currRecDepth_1384_; lean_object* v_maxRecDepth_1385_; lean_object* v_ref_1386_; lean_object* v_currNamespace_1387_; lean_object* v_openDecls_1388_; lean_object* v_initHeartbeats_1389_; lean_object* v_maxHeartbeats_1390_; lean_object* v_quotContext_1391_; lean_object* v_currMacroScope_1392_; uint8_t v_diag_1393_; lean_object* v_cancelTk_x3f_1394_; uint8_t v_suppressElabErrors_1395_; lean_object* v_inheritedTraceOptions_1396_; lean_object* v___x_1490_; uint8_t v___x_1491_; 
v_p_1380_ = lean_ctor_get(v_c_1349_, 0);
v_fileName_1381_ = lean_ctor_get(v_a_1359_, 0);
lean_inc_ref(v_fileName_1381_);
v_fileMap_1382_ = lean_ctor_get(v_a_1359_, 1);
lean_inc_ref(v_fileMap_1382_);
v_options_1383_ = lean_ctor_get(v_a_1359_, 2);
lean_inc_ref(v_options_1383_);
v_currRecDepth_1384_ = lean_ctor_get(v_a_1359_, 3);
lean_inc(v_currRecDepth_1384_);
v_maxRecDepth_1385_ = lean_ctor_get(v_a_1359_, 4);
lean_inc(v_maxRecDepth_1385_);
v_ref_1386_ = lean_ctor_get(v_a_1359_, 5);
lean_inc(v_ref_1386_);
v_currNamespace_1387_ = lean_ctor_get(v_a_1359_, 6);
lean_inc(v_currNamespace_1387_);
v_openDecls_1388_ = lean_ctor_get(v_a_1359_, 7);
lean_inc(v_openDecls_1388_);
v_initHeartbeats_1389_ = lean_ctor_get(v_a_1359_, 8);
lean_inc(v_initHeartbeats_1389_);
v_maxHeartbeats_1390_ = lean_ctor_get(v_a_1359_, 9);
lean_inc(v_maxHeartbeats_1390_);
v_quotContext_1391_ = lean_ctor_get(v_a_1359_, 10);
lean_inc(v_quotContext_1391_);
v_currMacroScope_1392_ = lean_ctor_get(v_a_1359_, 11);
lean_inc(v_currMacroScope_1392_);
v_diag_1393_ = lean_ctor_get_uint8(v_a_1359_, sizeof(void*)*14);
v_cancelTk_x3f_1394_ = lean_ctor_get(v_a_1359_, 12);
lean_inc(v_cancelTk_x3f_1394_);
v_suppressElabErrors_1395_ = lean_ctor_get_uint8(v_a_1359_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1396_ = lean_ctor_get(v_a_1359_, 13);
lean_inc_ref(v_inheritedTraceOptions_1396_);
lean_dec_ref(v_a_1359_);
v___x_1490_ = lean_unsigned_to_nat(0u);
v___x_1491_ = lean_nat_dec_eq(v_maxRecDepth_1385_, v___x_1490_);
if (v___x_1491_ == 0)
{
uint8_t v___x_1492_; 
v___x_1492_ = lean_nat_dec_eq(v_currRecDepth_1384_, v_maxRecDepth_1385_);
if (v___x_1492_ == 0)
{
goto v___jp_1397_;
}
else
{
lean_object* v___x_1493_; 
lean_dec_ref(v_inheritedTraceOptions_1396_);
lean_dec(v_cancelTk_x3f_1394_);
lean_dec(v_currMacroScope_1392_);
lean_dec(v_quotContext_1391_);
lean_dec(v_maxHeartbeats_1390_);
lean_dec(v_initHeartbeats_1389_);
lean_dec(v_openDecls_1388_);
lean_dec(v_currNamespace_1387_);
lean_dec(v_maxRecDepth_1385_);
lean_dec(v_currRecDepth_1384_);
lean_dec_ref(v_options_1383_);
lean_dec_ref(v_fileMap_1382_);
lean_dec_ref(v_fileName_1381_);
lean_dec_ref(v_c_1349_);
v___x_1493_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1386_);
return v___x_1493_;
}
}
else
{
goto v___jp_1397_;
}
v___jp_1362_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_1377_, 0, v___y_1364_);
lean_ctor_set(v___x_1377_, 1, v___y_1365_);
lean_ctor_set(v___x_1377_, 2, v_c_1349_);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___y_1363_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v_c_1349_ = v___x_1378_;
v_a_1350_ = v___y_1366_;
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
goto _start;
}
v___jp_1397_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1398_ = lean_unsigned_to_nat(1u);
v___x_1399_ = lean_nat_add(v_currRecDepth_1384_, v___x_1398_);
lean_dec(v_currRecDepth_1384_);
lean_inc_ref(v_inheritedTraceOptions_1396_);
lean_inc_ref(v_options_1383_);
v___x_1400_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1400_, 0, v_fileName_1381_);
lean_ctor_set(v___x_1400_, 1, v_fileMap_1382_);
lean_ctor_set(v___x_1400_, 2, v_options_1383_);
lean_ctor_set(v___x_1400_, 3, v___x_1399_);
lean_ctor_set(v___x_1400_, 4, v_maxRecDepth_1385_);
lean_ctor_set(v___x_1400_, 5, v_ref_1386_);
lean_ctor_set(v___x_1400_, 6, v_currNamespace_1387_);
lean_ctor_set(v___x_1400_, 7, v_openDecls_1388_);
lean_ctor_set(v___x_1400_, 8, v_initHeartbeats_1389_);
lean_ctor_set(v___x_1400_, 9, v_maxHeartbeats_1390_);
lean_ctor_set(v___x_1400_, 10, v_quotContext_1391_);
lean_ctor_set(v___x_1400_, 11, v_currMacroScope_1392_);
lean_ctor_set(v___x_1400_, 12, v_cancelTk_x3f_1394_);
lean_ctor_set(v___x_1400_, 13, v_inheritedTraceOptions_1396_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*14, v_diag_1393_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*14 + 1, v_suppressElabErrors_1395_);
lean_inc(v_p_1380_);
v___x_1401_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_1380_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v___x_1400_, v_a_1360_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1481_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1481_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1481_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
if (lean_obj_tag(v_a_1402_) == 1)
{
lean_object* v_val_1406_; lean_object* v_snd_1407_; uint8_t v_hasTrace_1408_; 
lean_del_object(v___x_1404_);
v_val_1406_ = lean_ctor_get(v_a_1402_, 0);
lean_inc(v_val_1406_);
lean_dec_ref(v_a_1402_);
v_snd_1407_ = lean_ctor_get(v_val_1406_, 1);
lean_inc(v_snd_1407_);
v_hasTrace_1408_ = lean_ctor_get_uint8(v_options_1383_, sizeof(void*)*1);
if (v_hasTrace_1408_ == 0)
{
lean_object* v_fst_1409_; lean_object* v_fst_1410_; lean_object* v_snd_1411_; 
lean_dec_ref(v_inheritedTraceOptions_1396_);
lean_dec_ref(v_options_1383_);
v_fst_1409_ = lean_ctor_get(v_val_1406_, 0);
lean_inc(v_fst_1409_);
lean_dec(v_val_1406_);
v_fst_1410_ = lean_ctor_get(v_snd_1407_, 0);
lean_inc(v_fst_1410_);
v_snd_1411_ = lean_ctor_get(v_snd_1407_, 1);
lean_inc(v_snd_1411_);
lean_dec(v_snd_1407_);
v___y_1363_ = v_snd_1411_;
v___y_1364_ = v_fst_1409_;
v___y_1365_ = v_fst_1410_;
v___y_1366_ = v_a_1350_;
v___y_1367_ = v_a_1351_;
v___y_1368_ = v_a_1352_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v___x_1400_;
v___y_1376_ = v_a_1360_;
goto v___jp_1362_;
}
else
{
lean_object* v_fst_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1476_; 
v_fst_1412_ = lean_ctor_get(v_val_1406_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_val_1406_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; 
v_unused_1477_ = lean_ctor_get(v_val_1406_, 1);
lean_dec(v_unused_1477_);
v___x_1414_ = v_val_1406_;
v_isShared_1415_ = v_isSharedCheck_1476_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_fst_1412_);
lean_dec(v_val_1406_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1476_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v_fst_1416_; lean_object* v_snd_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1475_; 
v_fst_1416_ = lean_ctor_get(v_snd_1407_, 0);
v_snd_1417_ = lean_ctor_get(v_snd_1407_, 1);
v_isSharedCheck_1475_ = !lean_is_exclusive(v_snd_1407_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1419_ = v_snd_1407_;
v_isShared_1420_ = v_isSharedCheck_1475_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_snd_1417_);
lean_inc(v_fst_1416_);
lean_dec(v_snd_1407_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1475_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_1422_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_1423_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1396_, v_options_1383_, v___x_1422_);
lean_dec_ref(v_options_1383_);
lean_dec_ref(v_inheritedTraceOptions_1396_);
if (v___x_1423_ == 0)
{
lean_del_object(v___x_1419_);
lean_del_object(v___x_1414_);
v___y_1363_ = v_snd_1417_;
v___y_1364_ = v_fst_1412_;
v___y_1365_ = v_fst_1416_;
v___y_1366_ = v_a_1350_;
v___y_1367_ = v_a_1351_;
v___y_1368_ = v_a_1352_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v___x_1400_;
v___y_1376_ = v_a_1360_;
goto v___jp_1362_;
}
else
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_1412_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v___x_1400_, v_a_1360_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1426_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref(v___x_1424_);
v___x_1426_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v___x_1400_, v_a_1360_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref(v___x_1426_);
v___x_1428_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_fst_1416_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v___x_1400_, v_a_1360_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref(v___x_1428_);
v___x_1430_ = l_Lean_MessageData_ofExpr(v_a_1425_);
v___x_1431_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_1420_ == 0)
{
lean_ctor_set_tag(v___x_1419_, 7);
lean_ctor_set(v___x_1419_, 1, v___x_1431_);
lean_ctor_set(v___x_1419_, 0, v___x_1430_);
v___x_1433_ = v___x_1419_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1434_ = l_Lean_MessageData_ofExpr(v_a_1427_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set_tag(v___x_1414_, 7);
lean_ctor_set(v___x_1414_, 1, v___x_1434_);
lean_ctor_set(v___x_1414_, 0, v___x_1433_);
v___x_1436_ = v___x_1414_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
lean_ctor_set(v___x_1437_, 1, v___x_1431_);
v___x_1438_ = l_Lean_MessageData_ofExpr(v_a_1429_);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_1421_, v___x_1439_, v_a_1357_, v_a_1358_, v___x_1400_, v_a_1360_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_dec_ref(v___x_1440_);
v___y_1363_ = v_snd_1417_;
v___y_1364_ = v_fst_1412_;
v___y_1365_ = v_fst_1416_;
v___y_1366_ = v_a_1350_;
v___y_1367_ = v_a_1351_;
v___y_1368_ = v_a_1352_;
v___y_1369_ = v_a_1353_;
v___y_1370_ = v_a_1354_;
v___y_1371_ = v_a_1355_;
v___y_1372_ = v_a_1356_;
v___y_1373_ = v_a_1357_;
v___y_1374_ = v_a_1358_;
v___y_1375_ = v___x_1400_;
v___y_1376_ = v_a_1360_;
goto v___jp_1362_;
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec(v_snd_1417_);
lean_dec(v_fst_1416_);
lean_dec(v_fst_1412_);
lean_dec_ref(v___x_1400_);
lean_dec_ref(v_c_1349_);
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1440_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1440_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec(v_a_1427_);
lean_dec(v_a_1425_);
lean_del_object(v___x_1419_);
lean_dec(v_snd_1417_);
lean_dec(v_fst_1416_);
lean_del_object(v___x_1414_);
lean_dec(v_fst_1412_);
lean_dec_ref(v___x_1400_);
lean_dec_ref(v_c_1349_);
v_a_1451_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1428_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1428_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
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
lean_dec(v_a_1425_);
lean_del_object(v___x_1419_);
lean_dec(v_snd_1417_);
lean_dec(v_fst_1416_);
lean_del_object(v___x_1414_);
lean_dec(v_fst_1412_);
lean_dec_ref(v___x_1400_);
lean_dec_ref(v_c_1349_);
v_a_1459_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1426_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1426_);
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
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_del_object(v___x_1419_);
lean_dec(v_snd_1417_);
lean_dec(v_fst_1416_);
lean_del_object(v___x_1414_);
lean_dec(v_fst_1412_);
lean_dec_ref(v___x_1400_);
lean_dec_ref(v_c_1349_);
v_a_1467_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1424_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1424_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
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
lean_object* v___x_1479_; 
lean_dec(v_a_1402_);
lean_dec_ref(v___x_1400_);
lean_dec_ref(v_inheritedTraceOptions_1396_);
lean_dec_ref(v_options_1383_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v_c_1349_);
v___x_1479_ = v___x_1404_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_c_1349_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec_ref(v___x_1400_);
lean_dec_ref(v_inheritedTraceOptions_1396_);
lean_dec_ref(v_options_1383_);
lean_dec_ref(v_c_1349_);
v_a_1482_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1401_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1401_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object* v_c_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
lean_dec(v_a_1505_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec(v_a_1496_);
lean_dec(v_a_1495_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_ref_1514_; lean_object* v___x_1515_; lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1524_; 
v_ref_1514_ = lean_ctor_get(v___y_1511_, 5);
v___x_1515_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msg_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1518_ = v___x_1515_;
v_isShared_1519_ = v_isSharedCheck_1524_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1524_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
lean_inc(v_ref_1514_);
v___x_1520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1520_, 0, v_ref_1514_);
lean_ctor_set(v___x_1520_, 1, v_a_1516_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set_tag(v___x_1518_, 1);
lean_ctor_set(v___x_1518_, 0, v___x_1520_);
v___x_1522_ = v___x_1518_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
return v_res_1531_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0));
v___x_1534_ = l_Lean_stringToMessageData(v___x_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1559_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1559_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1559_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v_leFn_x3f_1552_; 
v_leFn_x3f_1552_ = lean_ctor_get(v_a_1548_, 20);
lean_inc(v_leFn_x3f_1552_);
lean_dec(v_a_1548_);
if (lean_obj_tag(v_leFn_x3f_1552_) == 1)
{
lean_object* v_val_1553_; lean_object* v___x_1555_; 
v_val_1553_ = lean_ctor_get(v_leFn_x3f_1552_, 0);
lean_inc(v_val_1553_);
lean_dec_ref(v_leFn_x3f_1552_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v_val_1553_);
v___x_1555_ = v___x_1550_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_val_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
else
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_dec(v_leFn_x3f_1552_);
lean_del_object(v___x_1550_);
v___x_1557_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1);
v___x_1558_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1557_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
return v___x_1558_;
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
v_a_1560_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1547_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1547_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___boxed(lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec(v___y_1568_);
return v_res_1580_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0));
v___x_1583_ = l_Lean_stringToMessageData(v___x_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1608_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1599_ = v___x_1596_;
v_isShared_1600_ = v_isSharedCheck_1608_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1596_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1608_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v_ltFn_x3f_1601_; 
v_ltFn_x3f_1601_ = lean_ctor_get(v_a_1597_, 21);
lean_inc(v_ltFn_x3f_1601_);
lean_dec(v_a_1597_);
if (lean_obj_tag(v_ltFn_x3f_1601_) == 1)
{
lean_object* v_val_1602_; lean_object* v___x_1604_; 
v_val_1602_ = lean_ctor_get(v_ltFn_x3f_1601_, 0);
lean_inc(v_val_1602_);
lean_dec_ref(v_ltFn_x3f_1601_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v_val_1602_);
v___x_1604_ = v___x_1599_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_val_1602_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_dec(v_ltFn_x3f_1601_);
lean_del_object(v___x_1599_);
v___x_1606_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1);
v___x_1607_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1606_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
return v___x_1607_;
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
v_a_1609_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1596_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1596_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(lean_object* v_p_1630_, uint8_t v_strict_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
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
lean_dec_ref(v___x_1644_);
v___x_1646_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1630_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1648_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1647_);
lean_dec_ref(v___x_1646_);
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
lean_dec_ref(v___x_1667_);
v___x_1669_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1630_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1671_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1670_);
lean_dec_ref(v___x_1669_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_p_1690_, lean_object* v_strict_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
uint8_t v_strict_boxed_1704_; lean_object* v_res_1705_; 
v_strict_boxed_1704_ = lean_unbox(v_strict_1691_);
v_res_1705_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1690_, v_strict_boxed_1704_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec(v_p_1690_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(lean_object* v_c_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_p_1719_; uint8_t v_strict_1720_; lean_object* v___x_1721_; 
v_p_1719_ = lean_ctor_get(v_c_1706_, 0);
v_strict_1720_ = lean_ctor_get_uint8(v_c_1706_, sizeof(void*)*2);
v___x_1721_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1719_, v_strict_1720_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0___boxed(lean_object* v_c_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v_c_1722_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object* v_a_1736_, lean_object* v_x_1737_, lean_object* v_c_u2081_1738_, lean_object* v_b_1739_, lean_object* v_c_u2082_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v_options_1753_; lean_object* v_p_1754_; lean_object* v_p_1755_; uint8_t v_strict_1756_; lean_object* v_inheritedTraceOptions_1757_; uint8_t v_hasTrace_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v_p_1763_; 
v_options_1753_ = lean_ctor_get(v_a_1750_, 2);
v_p_1754_ = lean_ctor_get(v_c_u2081_1738_, 0);
v_p_1755_ = lean_ctor_get(v_c_u2082_1740_, 0);
v_strict_1756_ = lean_ctor_get_uint8(v_c_u2082_1740_, sizeof(void*)*2);
v_inheritedTraceOptions_1757_ = lean_ctor_get(v_a_1750_, 13);
v_hasTrace_1758_ = lean_ctor_get_uint8(v_options_1753_, sizeof(void*)*1);
v___x_1759_ = lean_nat_to_int(v_a_1736_);
lean_inc(v_p_1755_);
v___x_1760_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1755_, v___x_1759_);
lean_dec(v___x_1759_);
v___x_1761_ = lean_int_neg(v_b_1739_);
lean_inc(v_p_1754_);
v___x_1762_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1754_, v___x_1761_);
lean_dec(v___x_1761_);
v_p_1763_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1760_, v___x_1762_);
if (v_hasTrace_1758_ == 0)
{
goto v___jp_1764_;
}
else
{
lean_object* v_cls_1768_; lean_object* v___x_1769_; uint8_t v___x_1770_; 
v_cls_1768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_1769_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2);
v___x_1770_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1757_, v_options_1753_, v___x_1769_);
if (v___x_1770_ == 0)
{
goto v___jp_1764_;
}
else
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1737_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1773_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref(v___x_1771_);
v___x_1773_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_1738_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1775_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref(v___x_1773_);
v___x_1775_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_u2082_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref(v___x_1775_);
v___x_1777_ = l_Lean_MessageData_ofExpr(v_a_1772_);
v___x_1778_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_1779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1777_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = l_Lean_MessageData_ofExpr(v_a_1774_);
v___x_1781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1779_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
lean_ctor_set(v___x_1782_, 1, v___x_1778_);
v___x_1783_ = l_Lean_MessageData_ofExpr(v_a_1776_);
v___x_1784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_1768_, v___x_1784_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_dec_ref(v___x_1785_);
goto v___jp_1764_;
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec(v_p_1763_);
lean_dec_ref(v_c_u2082_1740_);
lean_dec_ref(v_c_u2081_1738_);
lean_dec(v_x_1737_);
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1785_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1785_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_dec(v_a_1774_);
lean_dec(v_a_1772_);
lean_dec(v_p_1763_);
lean_dec_ref(v_c_u2082_1740_);
lean_dec_ref(v_c_u2081_1738_);
lean_dec(v_x_1737_);
v_a_1794_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1775_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1775_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
lean_dec(v_a_1772_);
lean_dec(v_p_1763_);
lean_dec_ref(v_c_u2082_1740_);
lean_dec_ref(v_c_u2081_1738_);
lean_dec(v_x_1737_);
v_a_1802_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1773_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1773_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
lean_dec(v_p_1763_);
lean_dec_ref(v_c_u2082_1740_);
lean_dec_ref(v_c_u2081_1738_);
lean_dec(v_x_1737_);
v_a_1810_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1771_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1771_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
v___jp_1764_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1765_ = lean_alloc_ctor(13, 3, 0);
lean_ctor_set(v___x_1765_, 0, v_x_1737_);
lean_ctor_set(v___x_1765_, 1, v_c_u2081_1738_);
lean_ctor_set(v___x_1765_, 2, v_c_u2082_1740_);
v___x_1766_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1766_, 0, v_p_1763_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*2, v_strict_1756_);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
return v___x_1767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object** _args){
lean_object* v_a_1818_ = _args[0];
lean_object* v_x_1819_ = _args[1];
lean_object* v_c_u2081_1820_ = _args[2];
lean_object* v_b_1821_ = _args[3];
lean_object* v_c_u2082_1822_ = _args[4];
lean_object* v_a_1823_ = _args[5];
lean_object* v_a_1824_ = _args[6];
lean_object* v_a_1825_ = _args[7];
lean_object* v_a_1826_ = _args[8];
lean_object* v_a_1827_ = _args[9];
lean_object* v_a_1828_ = _args[10];
lean_object* v_a_1829_ = _args[11];
lean_object* v_a_1830_ = _args[12];
lean_object* v_a_1831_ = _args[13];
lean_object* v_a_1832_ = _args[14];
lean_object* v_a_1833_ = _args[15];
lean_object* v_a_1834_ = _args[16];
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1818_, v_x_1819_, v_c_u2081_1820_, v_b_1821_, v_c_u2082_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
lean_dec(v_a_1829_);
lean_dec_ref(v_a_1828_);
lean_dec(v_a_1827_);
lean_dec_ref(v_a_1826_);
lean_dec(v_a_1825_);
lean_dec(v_a_1824_);
lean_dec(v_a_1823_);
lean_dec(v_b_1821_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1836_, lean_object* v_msg_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1837_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1851_, lean_object* v_msg_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1851_, v_msg_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec(v___y_1853_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(lean_object* v_a_1874_, lean_object* v_x_1875_, lean_object* v_c_u2081_1876_, lean_object* v_as_1877_, size_t v_sz_1878_, size_t v_i_1879_, lean_object* v_b_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
uint8_t v___x_1893_; 
v___x_1893_ = lean_usize_dec_lt(v_i_1879_, v_sz_1878_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; 
lean_dec_ref(v_c_u2081_1876_);
lean_dec(v_x_1875_);
lean_dec(v_a_1874_);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v_b_1880_);
return v___x_1894_;
}
else
{
lean_object* v_a_1895_; lean_object* v_fst_1896_; lean_object* v_snd_1897_; lean_object* v___x_1898_; 
lean_dec_ref(v_b_1880_);
v_a_1895_ = lean_array_uget_borrowed(v_as_1877_, v_i_1879_);
v_fst_1896_ = lean_ctor_get(v_a_1895_, 0);
v_snd_1897_ = lean_ctor_get(v_a_1895_, 1);
lean_inc(v_snd_1897_);
lean_inc_ref(v_c_u2081_1876_);
lean_inc(v_x_1875_);
lean_inc(v_a_1874_);
v___x_1898_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1874_, v_x_1875_, v_c_u2081_1876_, v_fst_1896_, v_snd_1897_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1900_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref(v___x_1898_);
v___x_1900_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_a_1899_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v___x_1901_; 
lean_dec_ref(v___x_1900_);
v___x_1901_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1915_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1915_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1915_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
uint8_t v___x_1906_; 
v___x_1906_ = lean_unbox(v_a_1902_);
lean_dec(v_a_1902_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; size_t v___x_1908_; size_t v___x_1909_; 
lean_del_object(v___x_1904_);
v___x_1907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v___x_1908_ = ((size_t)1ULL);
v___x_1909_ = lean_usize_add(v_i_1879_, v___x_1908_);
v_i_1879_ = v___x_1909_;
v_b_1880_ = v___x_1907_;
goto _start;
}
else
{
lean_object* v___x_1911_; lean_object* v___x_1913_; 
lean_dec_ref(v_c_u2081_1876_);
lean_dec(v_x_1875_);
lean_dec(v_a_1874_);
v___x_1911_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1911_);
v___x_1913_ = v___x_1904_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec_ref(v_c_u2081_1876_);
lean_dec(v_x_1875_);
lean_dec(v_a_1874_);
v_a_1916_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1901_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1901_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
lean_dec_ref(v_c_u2081_1876_);
lean_dec(v_x_1875_);
lean_dec(v_a_1874_);
v_a_1924_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1926_ = v___x_1900_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1900_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1924_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec_ref(v_c_u2081_1876_);
lean_dec(v_x_1875_);
lean_dec(v_a_1874_);
v_a_1932_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1898_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1898_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___boxed(lean_object** _args){
lean_object* v_a_1940_ = _args[0];
lean_object* v_x_1941_ = _args[1];
lean_object* v_c_u2081_1942_ = _args[2];
lean_object* v_as_1943_ = _args[3];
lean_object* v_sz_1944_ = _args[4];
lean_object* v_i_1945_ = _args[5];
lean_object* v_b_1946_ = _args[6];
lean_object* v___y_1947_ = _args[7];
lean_object* v___y_1948_ = _args[8];
lean_object* v___y_1949_ = _args[9];
lean_object* v___y_1950_ = _args[10];
lean_object* v___y_1951_ = _args[11];
lean_object* v___y_1952_ = _args[12];
lean_object* v___y_1953_ = _args[13];
lean_object* v___y_1954_ = _args[14];
lean_object* v___y_1955_ = _args[15];
lean_object* v___y_1956_ = _args[16];
lean_object* v___y_1957_ = _args[17];
lean_object* v___y_1958_ = _args[18];
_start:
{
size_t v_sz_boxed_1959_; size_t v_i_boxed_1960_; lean_object* v_res_1961_; 
v_sz_boxed_1959_ = lean_unbox_usize(v_sz_1944_);
lean_dec(v_sz_1944_);
v_i_boxed_1960_ = lean_unbox_usize(v_i_1945_);
lean_dec(v_i_1945_);
v_res_1961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1940_, v_x_1941_, v_c_u2081_1942_, v_as_1943_, v_sz_boxed_1959_, v_i_boxed_1960_, v_b_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v_as_1943_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(lean_object* v_a_1962_, lean_object* v_x_1963_, lean_object* v_c_u2081_1964_, lean_object* v_todo_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; size_t v_sz_1980_; size_t v___x_1981_; lean_object* v___x_1982_; 
v___x_1978_ = lean_box(0);
v___x_1979_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_1980_ = lean_array_size(v_todo_1965_);
v___x_1981_ = ((size_t)0ULL);
v___x_1982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1962_, v_x_1963_, v_c_u2081_1964_, v_todo_1965_, v_sz_1980_, v___x_1981_, v___x_1979_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1995_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1985_ = v___x_1982_;
v_isShared_1986_ = v_isSharedCheck_1995_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1995_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v_fst_1987_; 
v_fst_1987_ = lean_ctor_get(v_a_1983_, 0);
lean_inc(v_fst_1987_);
lean_dec(v_a_1983_);
if (lean_obj_tag(v_fst_1987_) == 0)
{
lean_object* v___x_1989_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_1978_);
v___x_1989_ = v___x_1985_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1978_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
else
{
lean_object* v_val_1991_; lean_object* v___x_1993_; 
v_val_1991_ = lean_ctor_get(v_fst_1987_, 0);
lean_inc(v_val_1991_);
lean_dec_ref(v_fst_1987_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v_val_1991_);
v___x_1993_ = v___x_1985_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_val_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
v_a_1996_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1982_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1982_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object* v_a_2004_, lean_object* v_x_2005_, lean_object* v_c_u2081_2006_, lean_object* v_todo_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2004_, v_x_2005_, v_c_u2081_2006_, v_todo_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
lean_dec(v_a_2018_);
lean_dec_ref(v_a_2017_);
lean_dec(v_a_2016_);
lean_dec_ref(v_a_2015_);
lean_dec(v_a_2014_);
lean_dec_ref(v_a_2013_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec(v_a_2008_);
lean_dec_ref(v_todo_2007_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_2021_, lean_object* v_as_2022_, size_t v_sz_2023_, size_t v_i_2024_, lean_object* v_b_2025_){
_start:
{
uint8_t v___x_2026_; 
v___x_2026_ = lean_usize_dec_lt(v_i_2024_, v_sz_2023_);
if (v___x_2026_ == 0)
{
return v_b_2025_;
}
else
{
lean_object* v_snd_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2060_; 
v_snd_2027_ = lean_ctor_get(v_b_2025_, 1);
v_isSharedCheck_2060_ = !lean_is_exclusive(v_b_2025_);
if (v_isSharedCheck_2060_ == 0)
{
lean_object* v_unused_2061_; 
v_unused_2061_ = lean_ctor_get(v_b_2025_, 0);
lean_dec(v_unused_2061_);
v___x_2029_ = v_b_2025_;
v_isShared_2030_ = v_isSharedCheck_2060_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_snd_2027_);
lean_dec(v_b_2025_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2060_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v_fst_2031_; lean_object* v_snd_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2059_; 
v_fst_2031_ = lean_ctor_get(v_snd_2027_, 0);
v_snd_2032_ = lean_ctor_get(v_snd_2027_, 1);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_snd_2027_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2034_ = v_snd_2027_;
v_isShared_2035_ = v_isSharedCheck_2059_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_snd_2032_);
lean_inc(v_fst_2031_);
lean_dec(v_snd_2027_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2059_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v_a_2036_; lean_object* v_p_2037_; lean_object* v___x_2038_; lean_object* v_a_2040_; lean_object* v_b_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v_a_2036_ = lean_array_uget_borrowed(v_as_2022_, v_i_2024_);
v_p_2037_ = lean_ctor_get(v_a_2036_, 0);
v___x_2038_ = lean_box(0);
v_b_2047_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2037_, v_x_2021_);
v___x_2048_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2049_ = lean_int_dec_eq(v_b_2047_, v___x_2048_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2051_; 
lean_inc(v_a_2036_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 1, v_a_2036_);
lean_ctor_set(v___x_2029_, 0, v_b_2047_);
v___x_2051_ = v___x_2029_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_b_2047_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_a_2036_);
v___x_2051_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v_todo_2052_; lean_object* v___x_2053_; 
v_todo_2052_ = lean_array_push(v_snd_2032_, v___x_2051_);
v___x_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2053_, 0, v_fst_2031_);
lean_ctor_set(v___x_2053_, 1, v_todo_2052_);
v_a_2040_ = v___x_2053_;
goto v___jp_2039_;
}
}
else
{
lean_object* v_cs_x27_2055_; lean_object* v___x_2057_; 
lean_dec(v_b_2047_);
lean_inc(v_a_2036_);
v_cs_x27_2055_ = l_Lean_PersistentArray_push___redArg(v_fst_2031_, v_a_2036_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 1, v_snd_2032_);
lean_ctor_set(v___x_2029_, 0, v_cs_x27_2055_);
v___x_2057_ = v___x_2029_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_cs_x27_2055_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v_snd_2032_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
v_a_2040_ = v___x_2057_;
goto v___jp_2039_;
}
}
v___jp_2039_:
{
lean_object* v___x_2042_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 1, v_a_2040_);
lean_ctor_set(v___x_2034_, 0, v___x_2038_);
v___x_2042_ = v___x_2034_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_a_2040_);
v___x_2042_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
size_t v___x_2043_; size_t v___x_2044_; 
v___x_2043_ = ((size_t)1ULL);
v___x_2044_ = lean_usize_add(v_i_2024_, v___x_2043_);
v_i_2024_ = v___x_2044_;
v_b_2025_ = v___x_2042_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_2062_, lean_object* v_as_2063_, lean_object* v_sz_2064_, lean_object* v_i_2065_, lean_object* v_b_2066_){
_start:
{
size_t v_sz_boxed_2067_; size_t v_i_boxed_2068_; lean_object* v_res_2069_; 
v_sz_boxed_2067_ = lean_unbox_usize(v_sz_2064_);
lean_dec(v_sz_2064_);
v_i_boxed_2068_ = lean_unbox_usize(v_i_2065_);
lean_dec(v_i_2065_);
v_res_2069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2062_, v_as_2063_, v_sz_boxed_2067_, v_i_boxed_2068_, v_b_2066_);
lean_dec_ref(v_as_2063_);
lean_dec(v_x_2062_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(lean_object* v_x_2070_, lean_object* v_as_2071_, size_t v_sz_2072_, size_t v_i_2073_, lean_object* v_b_2074_){
_start:
{
uint8_t v___x_2075_; 
v___x_2075_ = lean_usize_dec_lt(v_i_2073_, v_sz_2072_);
if (v___x_2075_ == 0)
{
return v_b_2074_;
}
else
{
lean_object* v_snd_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2109_; 
v_snd_2076_ = lean_ctor_get(v_b_2074_, 1);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_b_2074_);
if (v_isSharedCheck_2109_ == 0)
{
lean_object* v_unused_2110_; 
v_unused_2110_ = lean_ctor_get(v_b_2074_, 0);
lean_dec(v_unused_2110_);
v___x_2078_ = v_b_2074_;
v_isShared_2079_ = v_isSharedCheck_2109_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_snd_2076_);
lean_dec(v_b_2074_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2109_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v_fst_2080_; lean_object* v_snd_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2108_; 
v_fst_2080_ = lean_ctor_get(v_snd_2076_, 0);
v_snd_2081_ = lean_ctor_get(v_snd_2076_, 1);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_snd_2076_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2083_ = v_snd_2076_;
v_isShared_2084_ = v_isSharedCheck_2108_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_snd_2081_);
lean_inc(v_fst_2080_);
lean_dec(v_snd_2076_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2108_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v_a_2085_; lean_object* v_p_2086_; lean_object* v___x_2087_; lean_object* v_a_2089_; lean_object* v_b_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; 
v_a_2085_ = lean_array_uget_borrowed(v_as_2071_, v_i_2073_);
v_p_2086_ = lean_ctor_get(v_a_2085_, 0);
v___x_2087_ = lean_box(0);
v_b_2096_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2086_, v_x_2070_);
v___x_2097_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2098_ = lean_int_dec_eq(v_b_2096_, v___x_2097_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2100_; 
lean_inc(v_a_2085_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 1, v_a_2085_);
lean_ctor_set(v___x_2078_, 0, v_b_2096_);
v___x_2100_ = v___x_2078_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_b_2096_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_a_2085_);
v___x_2100_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v_todo_2101_; lean_object* v___x_2102_; 
v_todo_2101_ = lean_array_push(v_snd_2081_, v___x_2100_);
v___x_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2102_, 0, v_fst_2080_);
lean_ctor_set(v___x_2102_, 1, v_todo_2101_);
v_a_2089_ = v___x_2102_;
goto v___jp_2088_;
}
}
else
{
lean_object* v_cs_x27_2104_; lean_object* v___x_2106_; 
lean_dec(v_b_2096_);
lean_inc(v_a_2085_);
v_cs_x27_2104_ = l_Lean_PersistentArray_push___redArg(v_fst_2080_, v_a_2085_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 1, v_snd_2081_);
lean_ctor_set(v___x_2078_, 0, v_cs_x27_2104_);
v___x_2106_ = v___x_2078_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_cs_x27_2104_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_snd_2081_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
v_a_2089_ = v___x_2106_;
goto v___jp_2088_;
}
}
v___jp_2088_:
{
lean_object* v___x_2091_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 1, v_a_2089_);
lean_ctor_set(v___x_2083_, 0, v___x_2087_);
v___x_2091_ = v___x_2083_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_a_2089_);
v___x_2091_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
size_t v___x_2092_; size_t v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = ((size_t)1ULL);
v___x_2093_ = lean_usize_add(v_i_2073_, v___x_2092_);
v___x_2094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2070_, v_as_2071_, v_sz_2072_, v___x_2093_, v___x_2091_);
return v___x_2094_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2111_, lean_object* v_as_2112_, lean_object* v_sz_2113_, lean_object* v_i_2114_, lean_object* v_b_2115_){
_start:
{
size_t v_sz_boxed_2116_; size_t v_i_boxed_2117_; lean_object* v_res_2118_; 
v_sz_boxed_2116_ = lean_unbox_usize(v_sz_2113_);
lean_dec(v_sz_2113_);
v_i_boxed_2117_ = lean_unbox_usize(v_i_2114_);
lean_dec(v_i_2114_);
v_res_2118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2111_, v_as_2112_, v_sz_boxed_2116_, v_i_boxed_2117_, v_b_2115_);
lean_dec_ref(v_as_2112_);
lean_dec(v_x_2111_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_2119_, lean_object* v_as_2120_, size_t v_sz_2121_, size_t v_i_2122_, lean_object* v_b_2123_){
_start:
{
uint8_t v___x_2124_; 
v___x_2124_ = lean_usize_dec_lt(v_i_2122_, v_sz_2121_);
if (v___x_2124_ == 0)
{
return v_b_2123_;
}
else
{
lean_object* v_snd_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2158_; 
v_snd_2125_ = lean_ctor_get(v_b_2123_, 1);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_b_2123_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; 
v_unused_2159_ = lean_ctor_get(v_b_2123_, 0);
lean_dec(v_unused_2159_);
v___x_2127_ = v_b_2123_;
v_isShared_2128_ = v_isSharedCheck_2158_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_snd_2125_);
lean_dec(v_b_2123_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2158_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v_fst_2129_; lean_object* v_snd_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2157_; 
v_fst_2129_ = lean_ctor_get(v_snd_2125_, 0);
v_snd_2130_ = lean_ctor_get(v_snd_2125_, 1);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_snd_2125_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2132_ = v_snd_2125_;
v_isShared_2133_ = v_isSharedCheck_2157_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_snd_2130_);
lean_inc(v_fst_2129_);
lean_dec(v_snd_2125_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2157_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v_a_2134_; lean_object* v_p_2135_; lean_object* v___x_2136_; lean_object* v_a_2138_; lean_object* v_b_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v_a_2134_ = lean_array_uget_borrowed(v_as_2120_, v_i_2122_);
v_p_2135_ = lean_ctor_get(v_a_2134_, 0);
v___x_2136_ = lean_box(0);
v_b_2145_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2135_, v_x_2119_);
v___x_2146_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2147_ = lean_int_dec_eq(v_b_2145_, v___x_2146_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2149_; 
lean_inc(v_a_2134_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 1, v_a_2134_);
lean_ctor_set(v___x_2127_, 0, v_b_2145_);
v___x_2149_ = v___x_2127_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_b_2145_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_a_2134_);
v___x_2149_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v_todo_2150_; lean_object* v___x_2151_; 
v_todo_2150_ = lean_array_push(v_snd_2130_, v___x_2149_);
v___x_2151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2151_, 0, v_fst_2129_);
lean_ctor_set(v___x_2151_, 1, v_todo_2150_);
v_a_2138_ = v___x_2151_;
goto v___jp_2137_;
}
}
else
{
lean_object* v_cs_x27_2153_; lean_object* v___x_2155_; 
lean_dec(v_b_2145_);
lean_inc(v_a_2134_);
v_cs_x27_2153_ = l_Lean_PersistentArray_push___redArg(v_fst_2129_, v_a_2134_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 1, v_snd_2130_);
lean_ctor_set(v___x_2127_, 0, v_cs_x27_2153_);
v___x_2155_ = v___x_2127_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_cs_x27_2153_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_snd_2130_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
v_a_2138_ = v___x_2155_;
goto v___jp_2137_;
}
}
v___jp_2137_:
{
lean_object* v___x_2140_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 1, v_a_2138_);
lean_ctor_set(v___x_2132_, 0, v___x_2136_);
v___x_2140_ = v___x_2132_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_a_2138_);
v___x_2140_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
size_t v___x_2141_; size_t v___x_2142_; 
v___x_2141_ = ((size_t)1ULL);
v___x_2142_ = lean_usize_add(v_i_2122_, v___x_2141_);
v_i_2122_ = v___x_2142_;
v_b_2123_ = v___x_2140_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_2160_, lean_object* v_as_2161_, lean_object* v_sz_2162_, lean_object* v_i_2163_, lean_object* v_b_2164_){
_start:
{
size_t v_sz_boxed_2165_; size_t v_i_boxed_2166_; lean_object* v_res_2167_; 
v_sz_boxed_2165_ = lean_unbox_usize(v_sz_2162_);
lean_dec(v_sz_2162_);
v_i_boxed_2166_ = lean_unbox_usize(v_i_2163_);
lean_dec(v_i_2163_);
v_res_2167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2160_, v_as_2161_, v_sz_boxed_2165_, v_i_boxed_2166_, v_b_2164_);
lean_dec_ref(v_as_2161_);
lean_dec(v_x_2160_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2168_, lean_object* v_as_2169_, size_t v_sz_2170_, size_t v_i_2171_, lean_object* v_b_2172_){
_start:
{
uint8_t v___x_2173_; 
v___x_2173_ = lean_usize_dec_lt(v_i_2171_, v_sz_2170_);
if (v___x_2173_ == 0)
{
return v_b_2172_;
}
else
{
lean_object* v_snd_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2207_; 
v_snd_2174_ = lean_ctor_get(v_b_2172_, 1);
v_isSharedCheck_2207_ = !lean_is_exclusive(v_b_2172_);
if (v_isSharedCheck_2207_ == 0)
{
lean_object* v_unused_2208_; 
v_unused_2208_ = lean_ctor_get(v_b_2172_, 0);
lean_dec(v_unused_2208_);
v___x_2176_ = v_b_2172_;
v_isShared_2177_ = v_isSharedCheck_2207_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_snd_2174_);
lean_dec(v_b_2172_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2207_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v_fst_2178_; lean_object* v_snd_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2206_; 
v_fst_2178_ = lean_ctor_get(v_snd_2174_, 0);
v_snd_2179_ = lean_ctor_get(v_snd_2174_, 1);
v_isSharedCheck_2206_ = !lean_is_exclusive(v_snd_2174_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2181_ = v_snd_2174_;
v_isShared_2182_ = v_isSharedCheck_2206_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_snd_2179_);
lean_inc(v_fst_2178_);
lean_dec(v_snd_2174_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2206_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v_a_2183_; lean_object* v_p_2184_; lean_object* v___x_2185_; lean_object* v_a_2187_; lean_object* v_b_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v_a_2183_ = lean_array_uget_borrowed(v_as_2169_, v_i_2171_);
v_p_2184_ = lean_ctor_get(v_a_2183_, 0);
v___x_2185_ = lean_box(0);
v_b_2194_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2184_, v_x_2168_);
v___x_2195_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2196_ = lean_int_dec_eq(v_b_2194_, v___x_2195_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2198_; 
lean_inc(v_a_2183_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 1, v_a_2183_);
lean_ctor_set(v___x_2176_, 0, v_b_2194_);
v___x_2198_ = v___x_2176_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_b_2194_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_a_2183_);
v___x_2198_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v_todo_2199_; lean_object* v___x_2200_; 
v_todo_2199_ = lean_array_push(v_snd_2179_, v___x_2198_);
v___x_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2200_, 0, v_fst_2178_);
lean_ctor_set(v___x_2200_, 1, v_todo_2199_);
v_a_2187_ = v___x_2200_;
goto v___jp_2186_;
}
}
else
{
lean_object* v_cs_x27_2202_; lean_object* v___x_2204_; 
lean_dec(v_b_2194_);
lean_inc(v_a_2183_);
v_cs_x27_2202_ = l_Lean_PersistentArray_push___redArg(v_fst_2178_, v_a_2183_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 1, v_snd_2179_);
lean_ctor_set(v___x_2176_, 0, v_cs_x27_2202_);
v___x_2204_ = v___x_2176_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_cs_x27_2202_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_snd_2179_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
v_a_2187_ = v___x_2204_;
goto v___jp_2186_;
}
}
v___jp_2186_:
{
lean_object* v___x_2189_; 
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 1, v_a_2187_);
lean_ctor_set(v___x_2181_, 0, v___x_2185_);
v___x_2189_ = v___x_2181_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2185_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_a_2187_);
v___x_2189_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
size_t v___x_2190_; size_t v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = ((size_t)1ULL);
v___x_2191_ = lean_usize_add(v_i_2171_, v___x_2190_);
v___x_2192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2168_, v_as_2169_, v_sz_2170_, v___x_2191_, v___x_2189_);
return v___x_2192_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_2209_, lean_object* v_as_2210_, lean_object* v_sz_2211_, lean_object* v_i_2212_, lean_object* v_b_2213_){
_start:
{
size_t v_sz_boxed_2214_; size_t v_i_boxed_2215_; lean_object* v_res_2216_; 
v_sz_boxed_2214_ = lean_unbox_usize(v_sz_2211_);
lean_dec(v_sz_2211_);
v_i_boxed_2215_ = lean_unbox_usize(v_i_2212_);
lean_dec(v_i_2212_);
v_res_2216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2209_, v_as_2210_, v_sz_boxed_2214_, v_i_boxed_2215_, v_b_2213_);
lean_dec_ref(v_as_2210_);
lean_dec(v_x_2209_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(lean_object* v_init_2217_, lean_object* v_x_2218_, lean_object* v_n_2219_, lean_object* v_b_2220_){
_start:
{
if (lean_obj_tag(v_n_2219_) == 0)
{
lean_object* v_cs_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2236_; 
v_cs_2221_ = lean_ctor_get(v_n_2219_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v_n_2219_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2223_ = v_n_2219_;
v_isShared_2224_ = v_isSharedCheck_2236_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_cs_2221_);
lean_dec(v_n_2219_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2236_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; size_t v_sz_2227_; size_t v___x_2228_; lean_object* v___x_2229_; lean_object* v_fst_2230_; 
v___x_2225_ = lean_box(0);
v___x_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
lean_ctor_set(v___x_2226_, 1, v_b_2220_);
v_sz_2227_ = lean_array_size(v_cs_2221_);
v___x_2228_ = ((size_t)0ULL);
v___x_2229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2217_, v_x_2218_, v_cs_2221_, v_sz_2227_, v___x_2228_, v___x_2226_);
lean_dec_ref(v_cs_2221_);
v_fst_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_fst_2230_);
if (lean_obj_tag(v_fst_2230_) == 0)
{
lean_object* v_snd_2231_; lean_object* v___x_2233_; 
v_snd_2231_ = lean_ctor_get(v___x_2229_, 1);
lean_inc(v_snd_2231_);
lean_dec_ref(v___x_2229_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set_tag(v___x_2223_, 1);
lean_ctor_set(v___x_2223_, 0, v_snd_2231_);
v___x_2233_ = v___x_2223_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_snd_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
else
{
lean_object* v_val_2235_; 
lean_dec_ref(v___x_2229_);
lean_del_object(v___x_2223_);
v_val_2235_ = lean_ctor_get(v_fst_2230_, 0);
lean_inc(v_val_2235_);
lean_dec_ref(v_fst_2230_);
return v_val_2235_;
}
}
}
else
{
lean_object* v_vs_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2252_; 
v_vs_2237_ = lean_ctor_get(v_n_2219_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v_n_2219_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2239_ = v_n_2219_;
v_isShared_2240_ = v_isSharedCheck_2252_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_vs_2237_);
lean_dec(v_n_2219_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2252_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; size_t v_sz_2243_; size_t v___x_2244_; lean_object* v___x_2245_; lean_object* v_fst_2246_; 
v___x_2241_ = lean_box(0);
v___x_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
lean_ctor_set(v___x_2242_, 1, v_b_2220_);
v_sz_2243_ = lean_array_size(v_vs_2237_);
v___x_2244_ = ((size_t)0ULL);
v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2218_, v_vs_2237_, v_sz_2243_, v___x_2244_, v___x_2242_);
lean_dec_ref(v_vs_2237_);
v_fst_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_fst_2246_);
if (lean_obj_tag(v_fst_2246_) == 0)
{
lean_object* v_snd_2247_; lean_object* v___x_2249_; 
v_snd_2247_ = lean_ctor_get(v___x_2245_, 1);
lean_inc(v_snd_2247_);
lean_dec_ref(v___x_2245_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v_snd_2247_);
v___x_2249_ = v___x_2239_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_snd_2247_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
else
{
lean_object* v_val_2251_; 
lean_dec_ref(v___x_2245_);
lean_del_object(v___x_2239_);
v_val_2251_ = lean_ctor_get(v_fst_2246_, 0);
lean_inc(v_val_2251_);
lean_dec_ref(v_fst_2246_);
return v_val_2251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_2253_, lean_object* v_x_2254_, lean_object* v_as_2255_, size_t v_sz_2256_, size_t v_i_2257_, lean_object* v_b_2258_){
_start:
{
uint8_t v___x_2259_; 
v___x_2259_ = lean_usize_dec_lt(v_i_2257_, v_sz_2256_);
if (v___x_2259_ == 0)
{
return v_b_2258_;
}
else
{
lean_object* v_snd_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2278_; 
v_snd_2260_ = lean_ctor_get(v_b_2258_, 1);
v_isSharedCheck_2278_ = !lean_is_exclusive(v_b_2258_);
if (v_isSharedCheck_2278_ == 0)
{
lean_object* v_unused_2279_; 
v_unused_2279_ = lean_ctor_get(v_b_2258_, 0);
lean_dec(v_unused_2279_);
v___x_2262_ = v_b_2258_;
v_isShared_2263_ = v_isSharedCheck_2278_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_snd_2260_);
lean_dec(v_b_2258_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2278_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v_a_2264_; lean_object* v___x_2265_; 
v_a_2264_ = lean_array_uget_borrowed(v_as_2255_, v_i_2257_);
lean_inc(v_snd_2260_);
lean_inc(v_a_2264_);
v___x_2265_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2253_, v_x_2254_, v_a_2264_, v_snd_2260_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
v___x_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2266_);
v___x_2268_ = v___x_2262_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_snd_2260_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2271_; lean_object* v___x_2273_; 
lean_dec(v_snd_2260_);
v_a_2270_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2270_);
lean_dec_ref(v___x_2265_);
v___x_2271_ = lean_box(0);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 1, v_a_2270_);
lean_ctor_set(v___x_2262_, 0, v___x_2271_);
v___x_2273_ = v___x_2262_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_a_2270_);
v___x_2273_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
size_t v___x_2274_; size_t v___x_2275_; 
v___x_2274_ = ((size_t)1ULL);
v___x_2275_ = lean_usize_add(v_i_2257_, v___x_2274_);
v_i_2257_ = v___x_2275_;
v_b_2258_ = v___x_2273_;
goto _start;
}
}
}
}
}
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
lean_inc_ref(v_root_2297_);
v_tail_2298_ = lean_ctor_get(v_t_2295_, 1);
lean_inc_ref(v_tail_2298_);
lean_dec_ref(v_t_2295_);
lean_inc_ref(v_init_2296_);
v___x_2299_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2296_, v_x_2294_, v_root_2297_, v_init_2296_);
lean_dec_ref(v_init_2296_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; 
lean_dec_ref(v_tail_2298_);
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref(v___x_2299_);
return v_a_2300_;
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; size_t v_sz_2304_; size_t v___x_2305_; lean_object* v___x_2306_; lean_object* v_fst_2307_; 
v_a_2301_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2301_);
lean_dec_ref(v___x_2299_);
v___x_2302_ = lean_box(0);
v___x_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
lean_ctor_set(v___x_2303_, 1, v_a_2301_);
v_sz_2304_ = lean_array_size(v_tail_2298_);
v___x_2305_ = ((size_t)0ULL);
v___x_2306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2294_, v_tail_2298_, v_sz_2304_, v___x_2305_, v___x_2303_);
lean_dec_ref(v_tail_2298_);
v_fst_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_fst_2307_);
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
lean_dec_ref(v___x_2306_);
v_val_2309_ = lean_ctor_get(v_fst_2307_, 0);
lean_inc(v_val_2309_);
lean_dec_ref(v_fst_2307_);
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
v___x_2439_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object* v_a_2440_, lean_object* v_x_2441_, lean_object* v_c_2442_, lean_object* v_y_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2491_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2459_ = v___x_2456_;
v_isShared_2460_ = v_isSharedCheck_2491_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2491_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
uint8_t v___x_2461_; 
v___x_2461_ = lean_unbox(v_a_2457_);
lean_dec(v_a_2457_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; 
lean_del_object(v___x_2459_);
v___x_2462_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___y_2465_; lean_object* v_lowers_2473_; lean_object* v_size_2474_; lean_object* v___x_2475_; uint8_t v___x_2476_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_a_2463_);
lean_dec_ref(v___x_2462_);
v_lowers_2473_ = lean_ctor_get(v_a_2463_, 32);
lean_inc_ref(v_lowers_2473_);
lean_dec(v_a_2463_);
v_size_2474_ = lean_ctor_get(v_lowers_2473_, 2);
v___x_2475_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2476_ = lean_nat_dec_lt(v_y_2443_, v_size_2474_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; 
lean_dec_ref(v_lowers_2473_);
v___x_2477_ = l_outOfBounds___redArg(v___x_2475_);
v___y_2465_ = v___x_2477_;
goto v___jp_2464_;
}
else
{
lean_object* v___x_2478_; 
v___x_2478_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2475_, v_lowers_2473_, v_y_2443_);
lean_dec_ref(v_lowers_2473_);
v___y_2465_ = v___x_2478_;
goto v___jp_2464_;
}
v___jp_2464_:
{
lean_object* v___x_2466_; lean_object* v_fst_2467_; lean_object* v_snd_2468_; lean_object* v___f_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2466_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2441_, v___y_2465_);
v_fst_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_fst_2467_);
v_snd_2468_ = lean_ctor_get(v___x_2466_, 1);
lean_inc(v_snd_2468_);
lean_dec_ref(v___x_2466_);
lean_inc(v_a_2444_);
v___f_2469_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2469_, 0, v_a_2444_);
lean_closure_set(v___f_2469_, 1, v_y_2443_);
lean_closure_set(v___f_2469_, 2, v_fst_2467_);
v___x_2470_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2471_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2470_, v___f_2469_, v_a_2445_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v___x_2472_; 
lean_dec_ref(v___x_2471_);
v___x_2472_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2440_, v_x_2441_, v_c_2442_, v_snd_2468_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
lean_dec(v_snd_2468_);
return v___x_2472_;
}
else
{
lean_dec(v_snd_2468_);
lean_dec_ref(v_c_2442_);
lean_dec(v_x_2441_);
lean_dec(v_a_2440_);
return v___x_2471_;
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
v_a_2479_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2462_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2462_);
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
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2487_);
v___x_2489_ = v___x_2459_;
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
v_a_2492_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2494_ = v___x_2456_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2456_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object* v_a_2500_, lean_object* v_x_2501_, lean_object* v_c_2502_, lean_object* v_y_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_2500_, v_x_2501_, v_c_2502_, v_y_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec(v_a_2504_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(lean_object* v_a_2517_, lean_object* v_y_2518_, lean_object* v_fst_2519_, lean_object* v_s_2520_){
_start:
{
lean_object* v_structs_2521_; lean_object* v_typeIdOf_2522_; lean_object* v_exprToStructId_2523_; lean_object* v_exprToStructIdEntries_2524_; lean_object* v_forbiddenNatModules_2525_; lean_object* v_natStructs_2526_; lean_object* v_natTypeIdOf_2527_; lean_object* v_exprToNatStructId_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v_structs_2521_ = lean_ctor_get(v_s_2520_, 0);
v_typeIdOf_2522_ = lean_ctor_get(v_s_2520_, 1);
v_exprToStructId_2523_ = lean_ctor_get(v_s_2520_, 2);
v_exprToStructIdEntries_2524_ = lean_ctor_get(v_s_2520_, 3);
v_forbiddenNatModules_2525_ = lean_ctor_get(v_s_2520_, 4);
v_natStructs_2526_ = lean_ctor_get(v_s_2520_, 5);
v_natTypeIdOf_2527_ = lean_ctor_get(v_s_2520_, 6);
v_exprToNatStructId_2528_ = lean_ctor_get(v_s_2520_, 7);
v___x_2529_ = lean_array_get_size(v_structs_2521_);
v___x_2530_ = lean_nat_dec_lt(v_a_2517_, v___x_2529_);
if (v___x_2530_ == 0)
{
lean_dec_ref(v_fst_2519_);
return v_s_2520_;
}
else
{
lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2592_; 
lean_inc_ref(v_exprToNatStructId_2528_);
lean_inc_ref(v_natTypeIdOf_2527_);
lean_inc_ref(v_natStructs_2526_);
lean_inc_ref(v_forbiddenNatModules_2525_);
lean_inc_ref(v_exprToStructIdEntries_2524_);
lean_inc_ref(v_exprToStructId_2523_);
lean_inc_ref(v_typeIdOf_2522_);
lean_inc_ref(v_structs_2521_);
v_isSharedCheck_2592_ = !lean_is_exclusive(v_s_2520_);
if (v_isSharedCheck_2592_ == 0)
{
lean_object* v_unused_2593_; lean_object* v_unused_2594_; lean_object* v_unused_2595_; lean_object* v_unused_2596_; lean_object* v_unused_2597_; lean_object* v_unused_2598_; lean_object* v_unused_2599_; lean_object* v_unused_2600_; 
v_unused_2593_ = lean_ctor_get(v_s_2520_, 7);
lean_dec(v_unused_2593_);
v_unused_2594_ = lean_ctor_get(v_s_2520_, 6);
lean_dec(v_unused_2594_);
v_unused_2595_ = lean_ctor_get(v_s_2520_, 5);
lean_dec(v_unused_2595_);
v_unused_2596_ = lean_ctor_get(v_s_2520_, 4);
lean_dec(v_unused_2596_);
v_unused_2597_ = lean_ctor_get(v_s_2520_, 3);
lean_dec(v_unused_2597_);
v_unused_2598_ = lean_ctor_get(v_s_2520_, 2);
lean_dec(v_unused_2598_);
v_unused_2599_ = lean_ctor_get(v_s_2520_, 1);
lean_dec(v_unused_2599_);
v_unused_2600_ = lean_ctor_get(v_s_2520_, 0);
lean_dec(v_unused_2600_);
v___x_2532_ = v_s_2520_;
v_isShared_2533_ = v_isSharedCheck_2592_;
goto v_resetjp_2531_;
}
else
{
lean_dec(v_s_2520_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2592_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v_v_2534_; lean_object* v_id_2535_; lean_object* v_ringId_x3f_2536_; lean_object* v_type_2537_; lean_object* v_u_2538_; lean_object* v_intModuleInst_2539_; lean_object* v_leInst_x3f_2540_; lean_object* v_ltInst_x3f_2541_; lean_object* v_lawfulOrderLTInst_x3f_2542_; lean_object* v_isPreorderInst_x3f_2543_; lean_object* v_orderedAddInst_x3f_2544_; lean_object* v_isLinearInst_x3f_2545_; lean_object* v_noNatDivInst_x3f_2546_; lean_object* v_ringInst_x3f_2547_; lean_object* v_commRingInst_x3f_2548_; lean_object* v_orderedRingInst_x3f_2549_; lean_object* v_fieldInst_x3f_2550_; lean_object* v_charInst_x3f_2551_; lean_object* v_zero_2552_; lean_object* v_ofNatZero_2553_; lean_object* v_one_x3f_2554_; lean_object* v_leFn_x3f_2555_; lean_object* v_ltFn_x3f_2556_; lean_object* v_addFn_2557_; lean_object* v_zsmulFn_2558_; lean_object* v_nsmulFn_2559_; lean_object* v_zsmulFn_x3f_2560_; lean_object* v_nsmulFn_x3f_2561_; lean_object* v_homomulFn_x3f_2562_; lean_object* v_subFn_2563_; lean_object* v_negFn_2564_; lean_object* v_vars_2565_; lean_object* v_varMap_2566_; lean_object* v_lowers_2567_; lean_object* v_uppers_2568_; lean_object* v_diseqs_2569_; lean_object* v_assignment_2570_; uint8_t v_caseSplits_2571_; lean_object* v_conflict_x3f_2572_; lean_object* v_diseqSplits_2573_; lean_object* v_elimEqs_2574_; lean_object* v_elimStack_2575_; lean_object* v_occurs_2576_; lean_object* v_ignored_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2591_; 
v_v_2534_ = lean_array_fget(v_structs_2521_, v_a_2517_);
v_id_2535_ = lean_ctor_get(v_v_2534_, 0);
v_ringId_x3f_2536_ = lean_ctor_get(v_v_2534_, 1);
v_type_2537_ = lean_ctor_get(v_v_2534_, 2);
v_u_2538_ = lean_ctor_get(v_v_2534_, 3);
v_intModuleInst_2539_ = lean_ctor_get(v_v_2534_, 4);
v_leInst_x3f_2540_ = lean_ctor_get(v_v_2534_, 5);
v_ltInst_x3f_2541_ = lean_ctor_get(v_v_2534_, 6);
v_lawfulOrderLTInst_x3f_2542_ = lean_ctor_get(v_v_2534_, 7);
v_isPreorderInst_x3f_2543_ = lean_ctor_get(v_v_2534_, 8);
v_orderedAddInst_x3f_2544_ = lean_ctor_get(v_v_2534_, 9);
v_isLinearInst_x3f_2545_ = lean_ctor_get(v_v_2534_, 10);
v_noNatDivInst_x3f_2546_ = lean_ctor_get(v_v_2534_, 11);
v_ringInst_x3f_2547_ = lean_ctor_get(v_v_2534_, 12);
v_commRingInst_x3f_2548_ = lean_ctor_get(v_v_2534_, 13);
v_orderedRingInst_x3f_2549_ = lean_ctor_get(v_v_2534_, 14);
v_fieldInst_x3f_2550_ = lean_ctor_get(v_v_2534_, 15);
v_charInst_x3f_2551_ = lean_ctor_get(v_v_2534_, 16);
v_zero_2552_ = lean_ctor_get(v_v_2534_, 17);
v_ofNatZero_2553_ = lean_ctor_get(v_v_2534_, 18);
v_one_x3f_2554_ = lean_ctor_get(v_v_2534_, 19);
v_leFn_x3f_2555_ = lean_ctor_get(v_v_2534_, 20);
v_ltFn_x3f_2556_ = lean_ctor_get(v_v_2534_, 21);
v_addFn_2557_ = lean_ctor_get(v_v_2534_, 22);
v_zsmulFn_2558_ = lean_ctor_get(v_v_2534_, 23);
v_nsmulFn_2559_ = lean_ctor_get(v_v_2534_, 24);
v_zsmulFn_x3f_2560_ = lean_ctor_get(v_v_2534_, 25);
v_nsmulFn_x3f_2561_ = lean_ctor_get(v_v_2534_, 26);
v_homomulFn_x3f_2562_ = lean_ctor_get(v_v_2534_, 27);
v_subFn_2563_ = lean_ctor_get(v_v_2534_, 28);
v_negFn_2564_ = lean_ctor_get(v_v_2534_, 29);
v_vars_2565_ = lean_ctor_get(v_v_2534_, 30);
v_varMap_2566_ = lean_ctor_get(v_v_2534_, 31);
v_lowers_2567_ = lean_ctor_get(v_v_2534_, 32);
v_uppers_2568_ = lean_ctor_get(v_v_2534_, 33);
v_diseqs_2569_ = lean_ctor_get(v_v_2534_, 34);
v_assignment_2570_ = lean_ctor_get(v_v_2534_, 35);
v_caseSplits_2571_ = lean_ctor_get_uint8(v_v_2534_, sizeof(void*)*42);
v_conflict_x3f_2572_ = lean_ctor_get(v_v_2534_, 36);
v_diseqSplits_2573_ = lean_ctor_get(v_v_2534_, 37);
v_elimEqs_2574_ = lean_ctor_get(v_v_2534_, 38);
v_elimStack_2575_ = lean_ctor_get(v_v_2534_, 39);
v_occurs_2576_ = lean_ctor_get(v_v_2534_, 40);
v_ignored_2577_ = lean_ctor_get(v_v_2534_, 41);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_v_2534_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2579_ = v_v_2534_;
v_isShared_2580_ = v_isSharedCheck_2591_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_ignored_2577_);
lean_inc(v_occurs_2576_);
lean_inc(v_elimStack_2575_);
lean_inc(v_elimEqs_2574_);
lean_inc(v_diseqSplits_2573_);
lean_inc(v_conflict_x3f_2572_);
lean_inc(v_assignment_2570_);
lean_inc(v_diseqs_2569_);
lean_inc(v_uppers_2568_);
lean_inc(v_lowers_2567_);
lean_inc(v_varMap_2566_);
lean_inc(v_vars_2565_);
lean_inc(v_negFn_2564_);
lean_inc(v_subFn_2563_);
lean_inc(v_homomulFn_x3f_2562_);
lean_inc(v_nsmulFn_x3f_2561_);
lean_inc(v_zsmulFn_x3f_2560_);
lean_inc(v_nsmulFn_2559_);
lean_inc(v_zsmulFn_2558_);
lean_inc(v_addFn_2557_);
lean_inc(v_ltFn_x3f_2556_);
lean_inc(v_leFn_x3f_2555_);
lean_inc(v_one_x3f_2554_);
lean_inc(v_ofNatZero_2553_);
lean_inc(v_zero_2552_);
lean_inc(v_charInst_x3f_2551_);
lean_inc(v_fieldInst_x3f_2550_);
lean_inc(v_orderedRingInst_x3f_2549_);
lean_inc(v_commRingInst_x3f_2548_);
lean_inc(v_ringInst_x3f_2547_);
lean_inc(v_noNatDivInst_x3f_2546_);
lean_inc(v_isLinearInst_x3f_2545_);
lean_inc(v_orderedAddInst_x3f_2544_);
lean_inc(v_isPreorderInst_x3f_2543_);
lean_inc(v_lawfulOrderLTInst_x3f_2542_);
lean_inc(v_ltInst_x3f_2541_);
lean_inc(v_leInst_x3f_2540_);
lean_inc(v_intModuleInst_2539_);
lean_inc(v_u_2538_);
lean_inc(v_type_2537_);
lean_inc(v_ringId_x3f_2536_);
lean_inc(v_id_2535_);
lean_dec(v_v_2534_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2591_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v_xs_x27_2582_; lean_object* v___x_2583_; lean_object* v___x_2585_; 
v___x_2581_ = lean_box(0);
v_xs_x27_2582_ = lean_array_fset(v_structs_2521_, v_a_2517_, v___x_2581_);
v___x_2583_ = l_Lean_PersistentArray_set___redArg(v_uppers_2568_, v_y_2518_, v_fst_2519_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 33, v___x_2583_);
v___x_2585_ = v___x_2579_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_id_2535_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_ringId_x3f_2536_);
lean_ctor_set(v_reuseFailAlloc_2590_, 2, v_type_2537_);
lean_ctor_set(v_reuseFailAlloc_2590_, 3, v_u_2538_);
lean_ctor_set(v_reuseFailAlloc_2590_, 4, v_intModuleInst_2539_);
lean_ctor_set(v_reuseFailAlloc_2590_, 5, v_leInst_x3f_2540_);
lean_ctor_set(v_reuseFailAlloc_2590_, 6, v_ltInst_x3f_2541_);
lean_ctor_set(v_reuseFailAlloc_2590_, 7, v_lawfulOrderLTInst_x3f_2542_);
lean_ctor_set(v_reuseFailAlloc_2590_, 8, v_isPreorderInst_x3f_2543_);
lean_ctor_set(v_reuseFailAlloc_2590_, 9, v_orderedAddInst_x3f_2544_);
lean_ctor_set(v_reuseFailAlloc_2590_, 10, v_isLinearInst_x3f_2545_);
lean_ctor_set(v_reuseFailAlloc_2590_, 11, v_noNatDivInst_x3f_2546_);
lean_ctor_set(v_reuseFailAlloc_2590_, 12, v_ringInst_x3f_2547_);
lean_ctor_set(v_reuseFailAlloc_2590_, 13, v_commRingInst_x3f_2548_);
lean_ctor_set(v_reuseFailAlloc_2590_, 14, v_orderedRingInst_x3f_2549_);
lean_ctor_set(v_reuseFailAlloc_2590_, 15, v_fieldInst_x3f_2550_);
lean_ctor_set(v_reuseFailAlloc_2590_, 16, v_charInst_x3f_2551_);
lean_ctor_set(v_reuseFailAlloc_2590_, 17, v_zero_2552_);
lean_ctor_set(v_reuseFailAlloc_2590_, 18, v_ofNatZero_2553_);
lean_ctor_set(v_reuseFailAlloc_2590_, 19, v_one_x3f_2554_);
lean_ctor_set(v_reuseFailAlloc_2590_, 20, v_leFn_x3f_2555_);
lean_ctor_set(v_reuseFailAlloc_2590_, 21, v_ltFn_x3f_2556_);
lean_ctor_set(v_reuseFailAlloc_2590_, 22, v_addFn_2557_);
lean_ctor_set(v_reuseFailAlloc_2590_, 23, v_zsmulFn_2558_);
lean_ctor_set(v_reuseFailAlloc_2590_, 24, v_nsmulFn_2559_);
lean_ctor_set(v_reuseFailAlloc_2590_, 25, v_zsmulFn_x3f_2560_);
lean_ctor_set(v_reuseFailAlloc_2590_, 26, v_nsmulFn_x3f_2561_);
lean_ctor_set(v_reuseFailAlloc_2590_, 27, v_homomulFn_x3f_2562_);
lean_ctor_set(v_reuseFailAlloc_2590_, 28, v_subFn_2563_);
lean_ctor_set(v_reuseFailAlloc_2590_, 29, v_negFn_2564_);
lean_ctor_set(v_reuseFailAlloc_2590_, 30, v_vars_2565_);
lean_ctor_set(v_reuseFailAlloc_2590_, 31, v_varMap_2566_);
lean_ctor_set(v_reuseFailAlloc_2590_, 32, v_lowers_2567_);
lean_ctor_set(v_reuseFailAlloc_2590_, 33, v___x_2583_);
lean_ctor_set(v_reuseFailAlloc_2590_, 34, v_diseqs_2569_);
lean_ctor_set(v_reuseFailAlloc_2590_, 35, v_assignment_2570_);
lean_ctor_set(v_reuseFailAlloc_2590_, 36, v_conflict_x3f_2572_);
lean_ctor_set(v_reuseFailAlloc_2590_, 37, v_diseqSplits_2573_);
lean_ctor_set(v_reuseFailAlloc_2590_, 38, v_elimEqs_2574_);
lean_ctor_set(v_reuseFailAlloc_2590_, 39, v_elimStack_2575_);
lean_ctor_set(v_reuseFailAlloc_2590_, 40, v_occurs_2576_);
lean_ctor_set(v_reuseFailAlloc_2590_, 41, v_ignored_2577_);
lean_ctor_set_uint8(v_reuseFailAlloc_2590_, sizeof(void*)*42, v_caseSplits_2571_);
v___x_2585_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
lean_object* v___x_2586_; lean_object* v___x_2588_; 
v___x_2586_ = lean_array_fset(v_xs_x27_2582_, v_a_2517_, v___x_2585_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2586_);
v___x_2588_ = v___x_2532_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v_typeIdOf_2522_);
lean_ctor_set(v_reuseFailAlloc_2589_, 2, v_exprToStructId_2523_);
lean_ctor_set(v_reuseFailAlloc_2589_, 3, v_exprToStructIdEntries_2524_);
lean_ctor_set(v_reuseFailAlloc_2589_, 4, v_forbiddenNatModules_2525_);
lean_ctor_set(v_reuseFailAlloc_2589_, 5, v_natStructs_2526_);
lean_ctor_set(v_reuseFailAlloc_2589_, 6, v_natTypeIdOf_2527_);
lean_ctor_set(v_reuseFailAlloc_2589_, 7, v_exprToNatStructId_2528_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed(lean_object* v_a_2601_, lean_object* v_y_2602_, lean_object* v_fst_2603_, lean_object* v_s_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(v_a_2601_, v_y_2602_, v_fst_2603_, v_s_2604_);
lean_dec(v_y_2602_);
lean_dec(v_a_2601_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object* v_a_2606_, lean_object* v_x_2607_, lean_object* v_c_2608_, lean_object* v_y_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v___x_2622_; 
v___x_2622_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2657_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2625_ = v___x_2622_;
v_isShared_2626_ = v_isSharedCheck_2657_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2622_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2657_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
uint8_t v___x_2627_; 
v___x_2627_ = lean_unbox(v_a_2623_);
lean_dec(v_a_2623_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; 
lean_del_object(v___x_2625_);
v___x_2628_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v___y_2631_; lean_object* v_uppers_2639_; lean_object* v_size_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref(v___x_2628_);
v_uppers_2639_ = lean_ctor_get(v_a_2629_, 33);
lean_inc_ref(v_uppers_2639_);
lean_dec(v_a_2629_);
v_size_2640_ = lean_ctor_get(v_uppers_2639_, 2);
v___x_2641_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2642_ = lean_nat_dec_lt(v_y_2609_, v_size_2640_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; 
lean_dec_ref(v_uppers_2639_);
v___x_2643_ = l_outOfBounds___redArg(v___x_2641_);
v___y_2631_ = v___x_2643_;
goto v___jp_2630_;
}
else
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2641_, v_uppers_2639_, v_y_2609_);
lean_dec_ref(v_uppers_2639_);
v___y_2631_ = v___x_2644_;
goto v___jp_2630_;
}
v___jp_2630_:
{
lean_object* v___x_2632_; lean_object* v_fst_2633_; lean_object* v_snd_2634_; lean_object* v___f_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2632_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2607_, v___y_2631_);
v_fst_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_fst_2633_);
v_snd_2634_ = lean_ctor_get(v___x_2632_, 1);
lean_inc(v_snd_2634_);
lean_dec_ref(v___x_2632_);
lean_inc(v_a_2610_);
v___f_2635_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2635_, 0, v_a_2610_);
lean_closure_set(v___f_2635_, 1, v_y_2609_);
lean_closure_set(v___f_2635_, 2, v_fst_2633_);
v___x_2636_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2637_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2636_, v___f_2635_, v_a_2611_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v___x_2638_; 
lean_dec_ref(v___x_2637_);
v___x_2638_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2606_, v_x_2607_, v_c_2608_, v_snd_2634_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
lean_dec(v_snd_2634_);
return v___x_2638_;
}
else
{
lean_dec(v_snd_2634_);
lean_dec_ref(v_c_2608_);
lean_dec(v_x_2607_);
lean_dec(v_a_2606_);
return v___x_2637_;
}
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec(v_y_2609_);
lean_dec_ref(v_c_2608_);
lean_dec(v_x_2607_);
lean_dec(v_a_2606_);
v_a_2645_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2628_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2628_);
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
else
{
lean_object* v___x_2653_; lean_object* v___x_2655_; 
lean_dec(v_y_2609_);
lean_dec_ref(v_c_2608_);
lean_dec(v_x_2607_);
lean_dec(v_a_2606_);
v___x_2653_ = lean_box(0);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v___x_2653_);
v___x_2655_ = v___x_2625_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_dec(v_y_2609_);
lean_dec_ref(v_c_2608_);
lean_dec(v_x_2607_);
lean_dec(v_a_2606_);
v_a_2658_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2622_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2622_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object* v_a_2666_, lean_object* v_x_2667_, lean_object* v_c_2668_, lean_object* v_y_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_2666_, v_x_2667_, v_c_2668_, v_y_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
lean_dec_ref(v_a_2675_);
lean_dec(v_a_2674_);
lean_dec_ref(v_a_2673_);
lean_dec(v_a_2672_);
lean_dec(v_a_2671_);
lean_dec(v_a_2670_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(lean_object* v___y_2683_, lean_object* v_a_2684_, lean_object* v_s_2685_){
_start:
{
lean_object* v_structs_2686_; lean_object* v_typeIdOf_2687_; lean_object* v_exprToStructId_2688_; lean_object* v_exprToStructIdEntries_2689_; lean_object* v_forbiddenNatModules_2690_; lean_object* v_natStructs_2691_; lean_object* v_natTypeIdOf_2692_; lean_object* v_exprToNatStructId_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v_structs_2686_ = lean_ctor_get(v_s_2685_, 0);
v_typeIdOf_2687_ = lean_ctor_get(v_s_2685_, 1);
v_exprToStructId_2688_ = lean_ctor_get(v_s_2685_, 2);
v_exprToStructIdEntries_2689_ = lean_ctor_get(v_s_2685_, 3);
v_forbiddenNatModules_2690_ = lean_ctor_get(v_s_2685_, 4);
v_natStructs_2691_ = lean_ctor_get(v_s_2685_, 5);
v_natTypeIdOf_2692_ = lean_ctor_get(v_s_2685_, 6);
v_exprToNatStructId_2693_ = lean_ctor_get(v_s_2685_, 7);
v___x_2694_ = lean_array_get_size(v_structs_2686_);
v___x_2695_ = lean_nat_dec_lt(v___y_2683_, v___x_2694_);
if (v___x_2695_ == 0)
{
lean_dec_ref(v_a_2684_);
return v_s_2685_;
}
else
{
lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2757_; 
lean_inc_ref(v_exprToNatStructId_2693_);
lean_inc_ref(v_natTypeIdOf_2692_);
lean_inc_ref(v_natStructs_2691_);
lean_inc_ref(v_forbiddenNatModules_2690_);
lean_inc_ref(v_exprToStructIdEntries_2689_);
lean_inc_ref(v_exprToStructId_2688_);
lean_inc_ref(v_typeIdOf_2687_);
lean_inc_ref(v_structs_2686_);
v_isSharedCheck_2757_ = !lean_is_exclusive(v_s_2685_);
if (v_isSharedCheck_2757_ == 0)
{
lean_object* v_unused_2758_; lean_object* v_unused_2759_; lean_object* v_unused_2760_; lean_object* v_unused_2761_; lean_object* v_unused_2762_; lean_object* v_unused_2763_; lean_object* v_unused_2764_; lean_object* v_unused_2765_; 
v_unused_2758_ = lean_ctor_get(v_s_2685_, 7);
lean_dec(v_unused_2758_);
v_unused_2759_ = lean_ctor_get(v_s_2685_, 6);
lean_dec(v_unused_2759_);
v_unused_2760_ = lean_ctor_get(v_s_2685_, 5);
lean_dec(v_unused_2760_);
v_unused_2761_ = lean_ctor_get(v_s_2685_, 4);
lean_dec(v_unused_2761_);
v_unused_2762_ = lean_ctor_get(v_s_2685_, 3);
lean_dec(v_unused_2762_);
v_unused_2763_ = lean_ctor_get(v_s_2685_, 2);
lean_dec(v_unused_2763_);
v_unused_2764_ = lean_ctor_get(v_s_2685_, 1);
lean_dec(v_unused_2764_);
v_unused_2765_ = lean_ctor_get(v_s_2685_, 0);
lean_dec(v_unused_2765_);
v___x_2697_ = v_s_2685_;
v_isShared_2698_ = v_isSharedCheck_2757_;
goto v_resetjp_2696_;
}
else
{
lean_dec(v_s_2685_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2757_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v_v_2699_; lean_object* v_id_2700_; lean_object* v_ringId_x3f_2701_; lean_object* v_type_2702_; lean_object* v_u_2703_; lean_object* v_intModuleInst_2704_; lean_object* v_leInst_x3f_2705_; lean_object* v_ltInst_x3f_2706_; lean_object* v_lawfulOrderLTInst_x3f_2707_; lean_object* v_isPreorderInst_x3f_2708_; lean_object* v_orderedAddInst_x3f_2709_; lean_object* v_isLinearInst_x3f_2710_; lean_object* v_noNatDivInst_x3f_2711_; lean_object* v_ringInst_x3f_2712_; lean_object* v_commRingInst_x3f_2713_; lean_object* v_orderedRingInst_x3f_2714_; lean_object* v_fieldInst_x3f_2715_; lean_object* v_charInst_x3f_2716_; lean_object* v_zero_2717_; lean_object* v_ofNatZero_2718_; lean_object* v_one_x3f_2719_; lean_object* v_leFn_x3f_2720_; lean_object* v_ltFn_x3f_2721_; lean_object* v_addFn_2722_; lean_object* v_zsmulFn_2723_; lean_object* v_nsmulFn_2724_; lean_object* v_zsmulFn_x3f_2725_; lean_object* v_nsmulFn_x3f_2726_; lean_object* v_homomulFn_x3f_2727_; lean_object* v_subFn_2728_; lean_object* v_negFn_2729_; lean_object* v_vars_2730_; lean_object* v_varMap_2731_; lean_object* v_lowers_2732_; lean_object* v_uppers_2733_; lean_object* v_diseqs_2734_; lean_object* v_assignment_2735_; uint8_t v_caseSplits_2736_; lean_object* v_conflict_x3f_2737_; lean_object* v_diseqSplits_2738_; lean_object* v_elimEqs_2739_; lean_object* v_elimStack_2740_; lean_object* v_occurs_2741_; lean_object* v_ignored_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2756_; 
v_v_2699_ = lean_array_fget(v_structs_2686_, v___y_2683_);
v_id_2700_ = lean_ctor_get(v_v_2699_, 0);
v_ringId_x3f_2701_ = lean_ctor_get(v_v_2699_, 1);
v_type_2702_ = lean_ctor_get(v_v_2699_, 2);
v_u_2703_ = lean_ctor_get(v_v_2699_, 3);
v_intModuleInst_2704_ = lean_ctor_get(v_v_2699_, 4);
v_leInst_x3f_2705_ = lean_ctor_get(v_v_2699_, 5);
v_ltInst_x3f_2706_ = lean_ctor_get(v_v_2699_, 6);
v_lawfulOrderLTInst_x3f_2707_ = lean_ctor_get(v_v_2699_, 7);
v_isPreorderInst_x3f_2708_ = lean_ctor_get(v_v_2699_, 8);
v_orderedAddInst_x3f_2709_ = lean_ctor_get(v_v_2699_, 9);
v_isLinearInst_x3f_2710_ = lean_ctor_get(v_v_2699_, 10);
v_noNatDivInst_x3f_2711_ = lean_ctor_get(v_v_2699_, 11);
v_ringInst_x3f_2712_ = lean_ctor_get(v_v_2699_, 12);
v_commRingInst_x3f_2713_ = lean_ctor_get(v_v_2699_, 13);
v_orderedRingInst_x3f_2714_ = lean_ctor_get(v_v_2699_, 14);
v_fieldInst_x3f_2715_ = lean_ctor_get(v_v_2699_, 15);
v_charInst_x3f_2716_ = lean_ctor_get(v_v_2699_, 16);
v_zero_2717_ = lean_ctor_get(v_v_2699_, 17);
v_ofNatZero_2718_ = lean_ctor_get(v_v_2699_, 18);
v_one_x3f_2719_ = lean_ctor_get(v_v_2699_, 19);
v_leFn_x3f_2720_ = lean_ctor_get(v_v_2699_, 20);
v_ltFn_x3f_2721_ = lean_ctor_get(v_v_2699_, 21);
v_addFn_2722_ = lean_ctor_get(v_v_2699_, 22);
v_zsmulFn_2723_ = lean_ctor_get(v_v_2699_, 23);
v_nsmulFn_2724_ = lean_ctor_get(v_v_2699_, 24);
v_zsmulFn_x3f_2725_ = lean_ctor_get(v_v_2699_, 25);
v_nsmulFn_x3f_2726_ = lean_ctor_get(v_v_2699_, 26);
v_homomulFn_x3f_2727_ = lean_ctor_get(v_v_2699_, 27);
v_subFn_2728_ = lean_ctor_get(v_v_2699_, 28);
v_negFn_2729_ = lean_ctor_get(v_v_2699_, 29);
v_vars_2730_ = lean_ctor_get(v_v_2699_, 30);
v_varMap_2731_ = lean_ctor_get(v_v_2699_, 31);
v_lowers_2732_ = lean_ctor_get(v_v_2699_, 32);
v_uppers_2733_ = lean_ctor_get(v_v_2699_, 33);
v_diseqs_2734_ = lean_ctor_get(v_v_2699_, 34);
v_assignment_2735_ = lean_ctor_get(v_v_2699_, 35);
v_caseSplits_2736_ = lean_ctor_get_uint8(v_v_2699_, sizeof(void*)*42);
v_conflict_x3f_2737_ = lean_ctor_get(v_v_2699_, 36);
v_diseqSplits_2738_ = lean_ctor_get(v_v_2699_, 37);
v_elimEqs_2739_ = lean_ctor_get(v_v_2699_, 38);
v_elimStack_2740_ = lean_ctor_get(v_v_2699_, 39);
v_occurs_2741_ = lean_ctor_get(v_v_2699_, 40);
v_ignored_2742_ = lean_ctor_get(v_v_2699_, 41);
v_isSharedCheck_2756_ = !lean_is_exclusive(v_v_2699_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2744_ = v_v_2699_;
v_isShared_2745_ = v_isSharedCheck_2756_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_ignored_2742_);
lean_inc(v_occurs_2741_);
lean_inc(v_elimStack_2740_);
lean_inc(v_elimEqs_2739_);
lean_inc(v_diseqSplits_2738_);
lean_inc(v_conflict_x3f_2737_);
lean_inc(v_assignment_2735_);
lean_inc(v_diseqs_2734_);
lean_inc(v_uppers_2733_);
lean_inc(v_lowers_2732_);
lean_inc(v_varMap_2731_);
lean_inc(v_vars_2730_);
lean_inc(v_negFn_2729_);
lean_inc(v_subFn_2728_);
lean_inc(v_homomulFn_x3f_2727_);
lean_inc(v_nsmulFn_x3f_2726_);
lean_inc(v_zsmulFn_x3f_2725_);
lean_inc(v_nsmulFn_2724_);
lean_inc(v_zsmulFn_2723_);
lean_inc(v_addFn_2722_);
lean_inc(v_ltFn_x3f_2721_);
lean_inc(v_leFn_x3f_2720_);
lean_inc(v_one_x3f_2719_);
lean_inc(v_ofNatZero_2718_);
lean_inc(v_zero_2717_);
lean_inc(v_charInst_x3f_2716_);
lean_inc(v_fieldInst_x3f_2715_);
lean_inc(v_orderedRingInst_x3f_2714_);
lean_inc(v_commRingInst_x3f_2713_);
lean_inc(v_ringInst_x3f_2712_);
lean_inc(v_noNatDivInst_x3f_2711_);
lean_inc(v_isLinearInst_x3f_2710_);
lean_inc(v_orderedAddInst_x3f_2709_);
lean_inc(v_isPreorderInst_x3f_2708_);
lean_inc(v_lawfulOrderLTInst_x3f_2707_);
lean_inc(v_ltInst_x3f_2706_);
lean_inc(v_leInst_x3f_2705_);
lean_inc(v_intModuleInst_2704_);
lean_inc(v_u_2703_);
lean_inc(v_type_2702_);
lean_inc(v_ringId_x3f_2701_);
lean_inc(v_id_2700_);
lean_dec(v_v_2699_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2756_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2746_; lean_object* v_xs_x27_2747_; lean_object* v___x_2748_; lean_object* v___x_2750_; 
v___x_2746_ = lean_box(0);
v_xs_x27_2747_ = lean_array_fset(v_structs_2686_, v___y_2683_, v___x_2746_);
v___x_2748_ = l_Lean_PersistentArray_push___redArg(v_ignored_2742_, v_a_2684_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 41, v___x_2748_);
v___x_2750_ = v___x_2744_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_id_2700_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v_ringId_x3f_2701_);
lean_ctor_set(v_reuseFailAlloc_2755_, 2, v_type_2702_);
lean_ctor_set(v_reuseFailAlloc_2755_, 3, v_u_2703_);
lean_ctor_set(v_reuseFailAlloc_2755_, 4, v_intModuleInst_2704_);
lean_ctor_set(v_reuseFailAlloc_2755_, 5, v_leInst_x3f_2705_);
lean_ctor_set(v_reuseFailAlloc_2755_, 6, v_ltInst_x3f_2706_);
lean_ctor_set(v_reuseFailAlloc_2755_, 7, v_lawfulOrderLTInst_x3f_2707_);
lean_ctor_set(v_reuseFailAlloc_2755_, 8, v_isPreorderInst_x3f_2708_);
lean_ctor_set(v_reuseFailAlloc_2755_, 9, v_orderedAddInst_x3f_2709_);
lean_ctor_set(v_reuseFailAlloc_2755_, 10, v_isLinearInst_x3f_2710_);
lean_ctor_set(v_reuseFailAlloc_2755_, 11, v_noNatDivInst_x3f_2711_);
lean_ctor_set(v_reuseFailAlloc_2755_, 12, v_ringInst_x3f_2712_);
lean_ctor_set(v_reuseFailAlloc_2755_, 13, v_commRingInst_x3f_2713_);
lean_ctor_set(v_reuseFailAlloc_2755_, 14, v_orderedRingInst_x3f_2714_);
lean_ctor_set(v_reuseFailAlloc_2755_, 15, v_fieldInst_x3f_2715_);
lean_ctor_set(v_reuseFailAlloc_2755_, 16, v_charInst_x3f_2716_);
lean_ctor_set(v_reuseFailAlloc_2755_, 17, v_zero_2717_);
lean_ctor_set(v_reuseFailAlloc_2755_, 18, v_ofNatZero_2718_);
lean_ctor_set(v_reuseFailAlloc_2755_, 19, v_one_x3f_2719_);
lean_ctor_set(v_reuseFailAlloc_2755_, 20, v_leFn_x3f_2720_);
lean_ctor_set(v_reuseFailAlloc_2755_, 21, v_ltFn_x3f_2721_);
lean_ctor_set(v_reuseFailAlloc_2755_, 22, v_addFn_2722_);
lean_ctor_set(v_reuseFailAlloc_2755_, 23, v_zsmulFn_2723_);
lean_ctor_set(v_reuseFailAlloc_2755_, 24, v_nsmulFn_2724_);
lean_ctor_set(v_reuseFailAlloc_2755_, 25, v_zsmulFn_x3f_2725_);
lean_ctor_set(v_reuseFailAlloc_2755_, 26, v_nsmulFn_x3f_2726_);
lean_ctor_set(v_reuseFailAlloc_2755_, 27, v_homomulFn_x3f_2727_);
lean_ctor_set(v_reuseFailAlloc_2755_, 28, v_subFn_2728_);
lean_ctor_set(v_reuseFailAlloc_2755_, 29, v_negFn_2729_);
lean_ctor_set(v_reuseFailAlloc_2755_, 30, v_vars_2730_);
lean_ctor_set(v_reuseFailAlloc_2755_, 31, v_varMap_2731_);
lean_ctor_set(v_reuseFailAlloc_2755_, 32, v_lowers_2732_);
lean_ctor_set(v_reuseFailAlloc_2755_, 33, v_uppers_2733_);
lean_ctor_set(v_reuseFailAlloc_2755_, 34, v_diseqs_2734_);
lean_ctor_set(v_reuseFailAlloc_2755_, 35, v_assignment_2735_);
lean_ctor_set(v_reuseFailAlloc_2755_, 36, v_conflict_x3f_2737_);
lean_ctor_set(v_reuseFailAlloc_2755_, 37, v_diseqSplits_2738_);
lean_ctor_set(v_reuseFailAlloc_2755_, 38, v_elimEqs_2739_);
lean_ctor_set(v_reuseFailAlloc_2755_, 39, v_elimStack_2740_);
lean_ctor_set(v_reuseFailAlloc_2755_, 40, v_occurs_2741_);
lean_ctor_set(v_reuseFailAlloc_2755_, 41, v___x_2748_);
lean_ctor_set_uint8(v_reuseFailAlloc_2755_, sizeof(void*)*42, v_caseSplits_2736_);
v___x_2750_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2751_ = lean_array_fset(v_xs_x27_2747_, v___y_2683_, v___x_2750_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v___x_2751_);
v___x_2753_ = v___x_2697_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2751_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_typeIdOf_2687_);
lean_ctor_set(v_reuseFailAlloc_2754_, 2, v_exprToStructId_2688_);
lean_ctor_set(v_reuseFailAlloc_2754_, 3, v_exprToStructIdEntries_2689_);
lean_ctor_set(v_reuseFailAlloc_2754_, 4, v_forbiddenNatModules_2690_);
lean_ctor_set(v_reuseFailAlloc_2754_, 5, v_natStructs_2691_);
lean_ctor_set(v_reuseFailAlloc_2754_, 6, v_natTypeIdOf_2692_);
lean_ctor_set(v_reuseFailAlloc_2754_, 7, v_exprToNatStructId_2693_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed(lean_object* v___y_2766_, lean_object* v_a_2767_, lean_object* v_s_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(v___y_2766_, v_a_2767_, v_s_2768_);
lean_dec(v___y_2766_);
return v_res_2769_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3(void){
_start:
{
lean_object* v_cls_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v_cls_2777_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2778_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_2779_ = l_Lean_Name_append(v___x_2778_, v_cls_2777_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object* v_c_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v_options_2818_; uint8_t v_hasTrace_2819_; 
v_options_2818_ = lean_ctor_get(v_a_2790_, 2);
v_hasTrace_2819_ = lean_ctor_get_uint8(v_options_2818_, sizeof(void*)*1);
if (v_hasTrace_2819_ == 0)
{
v___y_2794_ = v_a_2781_;
v___y_2795_ = v_a_2782_;
v___y_2796_ = v_a_2783_;
v___y_2797_ = v_a_2784_;
v___y_2798_ = v_a_2785_;
v___y_2799_ = v_a_2786_;
v___y_2800_ = v_a_2787_;
v___y_2801_ = v_a_2788_;
v___y_2802_ = v_a_2789_;
v___y_2803_ = v_a_2790_;
v___y_2804_ = v_a_2791_;
goto v___jp_2793_;
}
else
{
lean_object* v_inheritedTraceOptions_2820_; lean_object* v_cls_2821_; lean_object* v___x_2822_; uint8_t v___x_2823_; 
v_inheritedTraceOptions_2820_ = lean_ctor_get(v_a_2790_, 13);
v_cls_2821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2822_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3);
v___x_2823_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2820_, v_options_2818_, v___x_2822_);
if (v___x_2823_ == 0)
{
v___y_2794_ = v_a_2781_;
v___y_2795_ = v_a_2782_;
v___y_2796_ = v_a_2783_;
v___y_2797_ = v_a_2784_;
v___y_2798_ = v_a_2785_;
v___y_2799_ = v_a_2786_;
v___y_2800_ = v_a_2787_;
v___y_2801_ = v_a_2788_;
v___y_2802_ = v_a_2789_;
v___y_2803_ = v_a_2790_;
v___y_2804_ = v_a_2791_;
goto v___jp_2793_;
}
else
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref(v___x_2824_);
v___x_2826_ = l_Lean_MessageData_ofExpr(v_a_2825_);
v___x_2827_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_2821_, v___x_2826_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_dec_ref(v___x_2827_);
v___y_2794_ = v_a_2781_;
v___y_2795_ = v_a_2782_;
v___y_2796_ = v_a_2783_;
v___y_2797_ = v_a_2784_;
v___y_2798_ = v_a_2785_;
v___y_2799_ = v_a_2786_;
v___y_2800_ = v_a_2787_;
v___y_2801_ = v_a_2788_;
v___y_2802_ = v_a_2789_;
v___y_2803_ = v_a_2790_;
v___y_2804_ = v_a_2791_;
goto v___jp_2793_;
}
else
{
return v___x_2827_;
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
v_a_2828_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2824_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2824_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
v___jp_2793_:
{
lean_object* v___x_2805_; 
v___x_2805_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2780_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___f_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref(v___x_2805_);
lean_inc(v___y_2794_);
v___f_2807_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2807_, 0, v___y_2794_);
lean_closure_set(v___f_2807_, 1, v_a_2806_);
v___x_2808_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2809_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2808_, v___f_2807_, v___y_2795_);
return v___x_2809_;
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
v_a_2810_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2805_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2805_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object* v_c_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
lean_dec(v_a_2847_);
lean_dec_ref(v_a_2846_);
lean_dec(v_a_2845_);
lean_dec_ref(v_a_2844_);
lean_dec(v_a_2843_);
lean_dec_ref(v_a_2842_);
lean_dec(v_a_2841_);
lean_dec_ref(v_a_2840_);
lean_dec(v_a_2839_);
lean_dec(v_a_2838_);
lean_dec(v_a_2837_);
lean_dec_ref(v_c_2836_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object* v_c_u2082_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_){
_start:
{
lean_object* v_p_2863_; lean_object* v_fileName_2864_; lean_object* v_fileMap_2865_; lean_object* v_options_2866_; lean_object* v_currRecDepth_2867_; lean_object* v_maxRecDepth_2868_; lean_object* v_ref_2869_; lean_object* v_currNamespace_2870_; lean_object* v_openDecls_2871_; lean_object* v_initHeartbeats_2872_; lean_object* v_maxHeartbeats_2873_; lean_object* v_quotContext_2874_; lean_object* v_currMacroScope_2875_; uint8_t v_diag_2876_; lean_object* v_cancelTk_x3f_2877_; uint8_t v_suppressElabErrors_2878_; lean_object* v_inheritedTraceOptions_2879_; lean_object* v___x_2931_; uint8_t v___x_2932_; 
v_p_2863_ = lean_ctor_get(v_c_u2082_2850_, 0);
v_fileName_2864_ = lean_ctor_get(v_a_2860_, 0);
lean_inc_ref(v_fileName_2864_);
v_fileMap_2865_ = lean_ctor_get(v_a_2860_, 1);
lean_inc_ref(v_fileMap_2865_);
v_options_2866_ = lean_ctor_get(v_a_2860_, 2);
lean_inc_ref(v_options_2866_);
v_currRecDepth_2867_ = lean_ctor_get(v_a_2860_, 3);
lean_inc(v_currRecDepth_2867_);
v_maxRecDepth_2868_ = lean_ctor_get(v_a_2860_, 4);
lean_inc(v_maxRecDepth_2868_);
v_ref_2869_ = lean_ctor_get(v_a_2860_, 5);
lean_inc(v_ref_2869_);
v_currNamespace_2870_ = lean_ctor_get(v_a_2860_, 6);
lean_inc(v_currNamespace_2870_);
v_openDecls_2871_ = lean_ctor_get(v_a_2860_, 7);
lean_inc(v_openDecls_2871_);
v_initHeartbeats_2872_ = lean_ctor_get(v_a_2860_, 8);
lean_inc(v_initHeartbeats_2872_);
v_maxHeartbeats_2873_ = lean_ctor_get(v_a_2860_, 9);
lean_inc(v_maxHeartbeats_2873_);
v_quotContext_2874_ = lean_ctor_get(v_a_2860_, 10);
lean_inc(v_quotContext_2874_);
v_currMacroScope_2875_ = lean_ctor_get(v_a_2860_, 11);
lean_inc(v_currMacroScope_2875_);
v_diag_2876_ = lean_ctor_get_uint8(v_a_2860_, sizeof(void*)*14);
v_cancelTk_x3f_2877_ = lean_ctor_get(v_a_2860_, 12);
lean_inc(v_cancelTk_x3f_2877_);
v_suppressElabErrors_2878_ = lean_ctor_get_uint8(v_a_2860_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2879_ = lean_ctor_get(v_a_2860_, 13);
lean_inc_ref(v_inheritedTraceOptions_2879_);
lean_dec_ref(v_a_2860_);
v___x_2931_ = lean_unsigned_to_nat(0u);
v___x_2932_ = lean_nat_dec_eq(v_maxRecDepth_2868_, v___x_2931_);
if (v___x_2932_ == 0)
{
uint8_t v___x_2933_; 
v___x_2933_ = lean_nat_dec_eq(v_currRecDepth_2867_, v_maxRecDepth_2868_);
if (v___x_2933_ == 0)
{
goto v___jp_2880_;
}
else
{
lean_object* v___x_2934_; 
lean_dec_ref(v_inheritedTraceOptions_2879_);
lean_dec(v_cancelTk_x3f_2877_);
lean_dec(v_currMacroScope_2875_);
lean_dec(v_quotContext_2874_);
lean_dec(v_maxHeartbeats_2873_);
lean_dec(v_initHeartbeats_2872_);
lean_dec(v_openDecls_2871_);
lean_dec(v_currNamespace_2870_);
lean_dec(v_maxRecDepth_2868_);
lean_dec(v_currRecDepth_2867_);
lean_dec_ref(v_options_2866_);
lean_dec_ref(v_fileMap_2865_);
lean_dec_ref(v_fileName_2864_);
lean_dec_ref(v_c_u2082_2850_);
v___x_2934_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_2869_);
return v___x_2934_;
}
}
else
{
goto v___jp_2880_;
}
v___jp_2880_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2881_ = lean_unsigned_to_nat(1u);
v___x_2882_ = lean_nat_add(v_currRecDepth_2867_, v___x_2881_);
lean_dec(v_currRecDepth_2867_);
v___x_2883_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2883_, 0, v_fileName_2864_);
lean_ctor_set(v___x_2883_, 1, v_fileMap_2865_);
lean_ctor_set(v___x_2883_, 2, v_options_2866_);
lean_ctor_set(v___x_2883_, 3, v___x_2882_);
lean_ctor_set(v___x_2883_, 4, v_maxRecDepth_2868_);
lean_ctor_set(v___x_2883_, 5, v_ref_2869_);
lean_ctor_set(v___x_2883_, 6, v_currNamespace_2870_);
lean_ctor_set(v___x_2883_, 7, v_openDecls_2871_);
lean_ctor_set(v___x_2883_, 8, v_initHeartbeats_2872_);
lean_ctor_set(v___x_2883_, 9, v_maxHeartbeats_2873_);
lean_ctor_set(v___x_2883_, 10, v_quotContext_2874_);
lean_ctor_set(v___x_2883_, 11, v_currMacroScope_2875_);
lean_ctor_set(v___x_2883_, 12, v_cancelTk_x3f_2877_);
lean_ctor_set(v___x_2883_, 13, v_inheritedTraceOptions_2879_);
lean_ctor_set_uint8(v___x_2883_, sizeof(void*)*14, v_diag_2876_);
lean_ctor_set_uint8(v___x_2883_, sizeof(void*)*14 + 1, v_suppressElabErrors_2878_);
v___x_2884_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2863_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v___x_2883_, v_a_2861_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2922_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2887_ = v___x_2884_;
v_isShared_2888_ = v_isSharedCheck_2922_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2884_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2922_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
if (lean_obj_tag(v_a_2885_) == 1)
{
lean_object* v_val_2889_; lean_object* v_snd_2890_; lean_object* v_snd_2891_; lean_object* v_fst_2892_; lean_object* v_fst_2893_; lean_object* v_p_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
lean_del_object(v___x_2887_);
v_val_2889_ = lean_ctor_get(v_a_2885_, 0);
lean_inc(v_val_2889_);
lean_dec_ref(v_a_2885_);
v_snd_2890_ = lean_ctor_get(v_val_2889_, 1);
lean_inc(v_snd_2890_);
v_snd_2891_ = lean_ctor_get(v_snd_2890_, 1);
lean_inc(v_snd_2891_);
v_fst_2892_ = lean_ctor_get(v_val_2889_, 0);
lean_inc(v_fst_2892_);
lean_dec(v_val_2889_);
v_fst_2893_ = lean_ctor_get(v_snd_2890_, 0);
lean_inc(v_fst_2893_);
lean_dec(v_snd_2890_);
v_p_2894_ = lean_ctor_get(v_snd_2891_, 0);
v___x_2895_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2894_, v_fst_2893_);
lean_inc_ref(v_c_u2082_2850_);
v___x_2896_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v___x_2895_, v_fst_2893_, v_snd_2891_, v_fst_2892_, v_c_u2082_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v___x_2883_, v_a_2861_);
lean_dec(v_fst_2893_);
lean_dec(v___x_2895_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref(v___x_2896_);
if (lean_obj_tag(v_a_2897_) == 1)
{
lean_object* v_val_2898_; 
lean_dec_ref(v_c_u2082_2850_);
v_val_2898_ = lean_ctor_get(v_a_2897_, 0);
lean_inc(v_val_2898_);
lean_dec_ref(v_a_2897_);
v_c_u2082_2850_ = v_val_2898_;
v_a_2860_ = v___x_2883_;
goto _start;
}
else
{
lean_object* v___x_2900_; 
lean_dec(v_a_2897_);
v___x_2900_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_u2082_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v___x_2883_, v_a_2861_);
lean_dec_ref(v___x_2883_);
lean_dec_ref(v_c_u2082_2850_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2908_; 
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2908_ == 0)
{
lean_object* v_unused_2909_; 
v_unused_2909_ = lean_ctor_get(v___x_2900_, 0);
lean_dec(v_unused_2909_);
v___x_2902_ = v___x_2900_;
v_isShared_2903_ = v_isSharedCheck_2908_;
goto v_resetjp_2901_;
}
else
{
lean_dec(v___x_2900_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2908_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2904_; lean_object* v___x_2906_; 
v___x_2904_ = lean_box(0);
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 0, v___x_2904_);
v___x_2906_ = v___x_2902_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2904_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
v_a_2910_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2900_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2900_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2883_);
lean_dec_ref(v_c_u2082_2850_);
return v___x_2896_;
}
}
else
{
lean_object* v___x_2918_; lean_object* v___x_2920_; 
lean_dec(v_a_2885_);
lean_dec_ref(v___x_2883_);
v___x_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2918_, 0, v_c_u2082_2850_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v___x_2918_);
v___x_2920_ = v___x_2887_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v___x_2918_);
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
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec_ref(v___x_2883_);
lean_dec_ref(v_c_u2082_2850_);
v_a_2923_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2884_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2884_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object* v_c_u2082_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_u2082_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
lean_dec(v_a_2946_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
lean_dec(v_a_2938_);
lean_dec(v_a_2937_);
lean_dec(v_a_2936_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object* v_val_2949_, lean_object* v_x_2950_, size_t v_x_2951_, size_t v_x_2952_){
_start:
{
if (lean_obj_tag(v_x_2950_) == 0)
{
lean_object* v_cs_2953_; size_t v_j_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; uint8_t v___x_2957_; 
v_cs_2953_ = lean_ctor_get(v_x_2950_, 0);
v_j_2954_ = lean_usize_shift_right(v_x_2951_, v_x_2952_);
v___x_2955_ = lean_usize_to_nat(v_j_2954_);
v___x_2956_ = lean_array_get_size(v_cs_2953_);
v___x_2957_ = lean_nat_dec_lt(v___x_2955_, v___x_2956_);
if (v___x_2957_ == 0)
{
lean_dec(v___x_2955_);
lean_dec_ref(v_val_2949_);
return v_x_2950_;
}
else
{
lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2975_; 
lean_inc_ref(v_cs_2953_);
v_isSharedCheck_2975_ = !lean_is_exclusive(v_x_2950_);
if (v_isSharedCheck_2975_ == 0)
{
lean_object* v_unused_2976_; 
v_unused_2976_ = lean_ctor_get(v_x_2950_, 0);
lean_dec(v_unused_2976_);
v___x_2959_ = v_x_2950_;
v_isShared_2960_ = v_isSharedCheck_2975_;
goto v_resetjp_2958_;
}
else
{
lean_dec(v_x_2950_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2975_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
size_t v___x_2961_; size_t v___x_2962_; size_t v___x_2963_; size_t v_i_2964_; size_t v___x_2965_; size_t v_shift_2966_; lean_object* v_v_2967_; lean_object* v___x_2968_; lean_object* v_xs_x27_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2961_ = ((size_t)1ULL);
v___x_2962_ = lean_usize_shift_left(v___x_2961_, v_x_2952_);
v___x_2963_ = lean_usize_sub(v___x_2962_, v___x_2961_);
v_i_2964_ = lean_usize_land(v_x_2951_, v___x_2963_);
v___x_2965_ = ((size_t)5ULL);
v_shift_2966_ = lean_usize_sub(v_x_2952_, v___x_2965_);
v_v_2967_ = lean_array_fget(v_cs_2953_, v___x_2955_);
v___x_2968_ = lean_box(0);
v_xs_x27_2969_ = lean_array_fset(v_cs_2953_, v___x_2955_, v___x_2968_);
v___x_2970_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2949_, v_v_2967_, v_i_2964_, v_shift_2966_);
v___x_2971_ = lean_array_fset(v_xs_x27_2969_, v___x_2955_, v___x_2970_);
lean_dec(v___x_2955_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 0, v___x_2971_);
v___x_2973_ = v___x_2959_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
else
{
lean_object* v_vs_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; uint8_t v___x_2980_; 
v_vs_2977_ = lean_ctor_get(v_x_2950_, 0);
v___x_2978_ = lean_usize_to_nat(v_x_2951_);
v___x_2979_ = lean_array_get_size(v_vs_2977_);
v___x_2980_ = lean_nat_dec_lt(v___x_2978_, v___x_2979_);
if (v___x_2980_ == 0)
{
lean_dec(v___x_2978_);
lean_dec_ref(v_val_2949_);
return v_x_2950_;
}
else
{
lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2992_; 
lean_inc_ref(v_vs_2977_);
v_isSharedCheck_2992_ = !lean_is_exclusive(v_x_2950_);
if (v_isSharedCheck_2992_ == 0)
{
lean_object* v_unused_2993_; 
v_unused_2993_ = lean_ctor_get(v_x_2950_, 0);
lean_dec(v_unused_2993_);
v___x_2982_ = v_x_2950_;
v_isShared_2983_ = v_isSharedCheck_2992_;
goto v_resetjp_2981_;
}
else
{
lean_dec(v_x_2950_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2992_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v_v_2984_; lean_object* v___x_2985_; lean_object* v_xs_x27_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2990_; 
v_v_2984_ = lean_array_fget(v_vs_2977_, v___x_2978_);
v___x_2985_ = lean_box(0);
v_xs_x27_2986_ = lean_array_fset(v_vs_2977_, v___x_2978_, v___x_2985_);
v___x_2987_ = l_Lean_PersistentArray_push___redArg(v_v_2984_, v_val_2949_);
v___x_2988_ = lean_array_fset(v_xs_x27_2986_, v___x_2978_, v___x_2987_);
lean_dec(v___x_2978_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 0, v___x_2988_);
v___x_2990_ = v___x_2982_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2988_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_val_2994_, lean_object* v_x_2995_, lean_object* v_x_2996_, lean_object* v_x_2997_){
_start:
{
size_t v_x_53643__boxed_2998_; size_t v_x_53644__boxed_2999_; lean_object* v_res_3000_; 
v_x_53643__boxed_2998_ = lean_unbox_usize(v_x_2996_);
lean_dec(v_x_2996_);
v_x_53644__boxed_2999_ = lean_unbox_usize(v_x_2997_);
lean_dec(v_x_2997_);
v_res_3000_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2994_, v_x_2995_, v_x_53643__boxed_2998_, v_x_53644__boxed_2999_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object* v_val_3001_, lean_object* v_t_3002_, lean_object* v_i_3003_){
_start:
{
lean_object* v_root_3004_; lean_object* v_tail_3005_; lean_object* v_size_3006_; size_t v_shift_3007_; lean_object* v_tailOff_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3032_; 
v_root_3004_ = lean_ctor_get(v_t_3002_, 0);
v_tail_3005_ = lean_ctor_get(v_t_3002_, 1);
v_size_3006_ = lean_ctor_get(v_t_3002_, 2);
v_shift_3007_ = lean_ctor_get_usize(v_t_3002_, 4);
v_tailOff_3008_ = lean_ctor_get(v_t_3002_, 3);
v_isSharedCheck_3032_ = !lean_is_exclusive(v_t_3002_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3010_ = v_t_3002_;
v_isShared_3011_ = v_isSharedCheck_3032_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_tailOff_3008_);
lean_inc(v_size_3006_);
lean_inc(v_tail_3005_);
lean_inc(v_root_3004_);
lean_dec(v_t_3002_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3032_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
uint8_t v___x_3012_; 
v___x_3012_ = lean_nat_dec_le(v_tailOff_3008_, v_i_3003_);
if (v___x_3012_ == 0)
{
size_t v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3016_; 
v___x_3013_ = lean_usize_of_nat(v_i_3003_);
v___x_3014_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_3001_, v_root_3004_, v___x_3013_, v_shift_3007_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 0, v___x_3014_);
v___x_3016_ = v___x_3010_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_3014_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v_tail_3005_);
lean_ctor_set(v_reuseFailAlloc_3017_, 2, v_size_3006_);
lean_ctor_set(v_reuseFailAlloc_3017_, 3, v_tailOff_3008_);
lean_ctor_set_usize(v_reuseFailAlloc_3017_, 4, v_shift_3007_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
else
{
lean_object* v___x_3018_; lean_object* v___x_3019_; uint8_t v___x_3020_; 
v___x_3018_ = lean_nat_sub(v_i_3003_, v_tailOff_3008_);
v___x_3019_ = lean_array_get_size(v_tail_3005_);
v___x_3020_ = lean_nat_dec_lt(v___x_3018_, v___x_3019_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3022_; 
lean_dec(v___x_3018_);
lean_dec_ref(v_val_3001_);
if (v_isShared_3011_ == 0)
{
v___x_3022_ = v___x_3010_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_root_3004_);
lean_ctor_set(v_reuseFailAlloc_3023_, 1, v_tail_3005_);
lean_ctor_set(v_reuseFailAlloc_3023_, 2, v_size_3006_);
lean_ctor_set(v_reuseFailAlloc_3023_, 3, v_tailOff_3008_);
lean_ctor_set_usize(v_reuseFailAlloc_3023_, 4, v_shift_3007_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
else
{
lean_object* v_v_3024_; lean_object* v___x_3025_; lean_object* v_xs_x27_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3030_; 
v_v_3024_ = lean_array_fget(v_tail_3005_, v___x_3018_);
v___x_3025_ = lean_box(0);
v_xs_x27_3026_ = lean_array_fset(v_tail_3005_, v___x_3018_, v___x_3025_);
v___x_3027_ = l_Lean_PersistentArray_push___redArg(v_v_3024_, v_val_3001_);
v___x_3028_ = lean_array_fset(v_xs_x27_3026_, v___x_3018_, v___x_3027_);
lean_dec(v___x_3018_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 1, v___x_3028_);
v___x_3030_ = v___x_3010_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_root_3004_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v___x_3028_);
lean_ctor_set(v_reuseFailAlloc_3031_, 2, v_size_3006_);
lean_ctor_set(v_reuseFailAlloc_3031_, 3, v_tailOff_3008_);
lean_ctor_set_usize(v_reuseFailAlloc_3031_, 4, v_shift_3007_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object* v_val_3033_, lean_object* v_t_3034_, lean_object* v_i_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3033_, v_t_3034_, v_i_3035_);
lean_dec(v_i_3035_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(lean_object* v___y_3037_, lean_object* v_val_3038_, lean_object* v_v_3039_, lean_object* v_s_3040_){
_start:
{
lean_object* v_structs_3041_; lean_object* v_typeIdOf_3042_; lean_object* v_exprToStructId_3043_; lean_object* v_exprToStructIdEntries_3044_; lean_object* v_forbiddenNatModules_3045_; lean_object* v_natStructs_3046_; lean_object* v_natTypeIdOf_3047_; lean_object* v_exprToNatStructId_3048_; lean_object* v___x_3049_; uint8_t v___x_3050_; 
v_structs_3041_ = lean_ctor_get(v_s_3040_, 0);
v_typeIdOf_3042_ = lean_ctor_get(v_s_3040_, 1);
v_exprToStructId_3043_ = lean_ctor_get(v_s_3040_, 2);
v_exprToStructIdEntries_3044_ = lean_ctor_get(v_s_3040_, 3);
v_forbiddenNatModules_3045_ = lean_ctor_get(v_s_3040_, 4);
v_natStructs_3046_ = lean_ctor_get(v_s_3040_, 5);
v_natTypeIdOf_3047_ = lean_ctor_get(v_s_3040_, 6);
v_exprToNatStructId_3048_ = lean_ctor_get(v_s_3040_, 7);
v___x_3049_ = lean_array_get_size(v_structs_3041_);
v___x_3050_ = lean_nat_dec_lt(v___y_3037_, v___x_3049_);
if (v___x_3050_ == 0)
{
lean_dec_ref(v_val_3038_);
return v_s_3040_;
}
else
{
lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3112_; 
lean_inc_ref(v_exprToNatStructId_3048_);
lean_inc_ref(v_natTypeIdOf_3047_);
lean_inc_ref(v_natStructs_3046_);
lean_inc_ref(v_forbiddenNatModules_3045_);
lean_inc_ref(v_exprToStructIdEntries_3044_);
lean_inc_ref(v_exprToStructId_3043_);
lean_inc_ref(v_typeIdOf_3042_);
lean_inc_ref(v_structs_3041_);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_s_3040_);
if (v_isSharedCheck_3112_ == 0)
{
lean_object* v_unused_3113_; lean_object* v_unused_3114_; lean_object* v_unused_3115_; lean_object* v_unused_3116_; lean_object* v_unused_3117_; lean_object* v_unused_3118_; lean_object* v_unused_3119_; lean_object* v_unused_3120_; 
v_unused_3113_ = lean_ctor_get(v_s_3040_, 7);
lean_dec(v_unused_3113_);
v_unused_3114_ = lean_ctor_get(v_s_3040_, 6);
lean_dec(v_unused_3114_);
v_unused_3115_ = lean_ctor_get(v_s_3040_, 5);
lean_dec(v_unused_3115_);
v_unused_3116_ = lean_ctor_get(v_s_3040_, 4);
lean_dec(v_unused_3116_);
v_unused_3117_ = lean_ctor_get(v_s_3040_, 3);
lean_dec(v_unused_3117_);
v_unused_3118_ = lean_ctor_get(v_s_3040_, 2);
lean_dec(v_unused_3118_);
v_unused_3119_ = lean_ctor_get(v_s_3040_, 1);
lean_dec(v_unused_3119_);
v_unused_3120_ = lean_ctor_get(v_s_3040_, 0);
lean_dec(v_unused_3120_);
v___x_3052_ = v_s_3040_;
v_isShared_3053_ = v_isSharedCheck_3112_;
goto v_resetjp_3051_;
}
else
{
lean_dec(v_s_3040_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3112_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v_v_3054_; lean_object* v_id_3055_; lean_object* v_ringId_x3f_3056_; lean_object* v_type_3057_; lean_object* v_u_3058_; lean_object* v_intModuleInst_3059_; lean_object* v_leInst_x3f_3060_; lean_object* v_ltInst_x3f_3061_; lean_object* v_lawfulOrderLTInst_x3f_3062_; lean_object* v_isPreorderInst_x3f_3063_; lean_object* v_orderedAddInst_x3f_3064_; lean_object* v_isLinearInst_x3f_3065_; lean_object* v_noNatDivInst_x3f_3066_; lean_object* v_ringInst_x3f_3067_; lean_object* v_commRingInst_x3f_3068_; lean_object* v_orderedRingInst_x3f_3069_; lean_object* v_fieldInst_x3f_3070_; lean_object* v_charInst_x3f_3071_; lean_object* v_zero_3072_; lean_object* v_ofNatZero_3073_; lean_object* v_one_x3f_3074_; lean_object* v_leFn_x3f_3075_; lean_object* v_ltFn_x3f_3076_; lean_object* v_addFn_3077_; lean_object* v_zsmulFn_3078_; lean_object* v_nsmulFn_3079_; lean_object* v_zsmulFn_x3f_3080_; lean_object* v_nsmulFn_x3f_3081_; lean_object* v_homomulFn_x3f_3082_; lean_object* v_subFn_3083_; lean_object* v_negFn_3084_; lean_object* v_vars_3085_; lean_object* v_varMap_3086_; lean_object* v_lowers_3087_; lean_object* v_uppers_3088_; lean_object* v_diseqs_3089_; lean_object* v_assignment_3090_; uint8_t v_caseSplits_3091_; lean_object* v_conflict_x3f_3092_; lean_object* v_diseqSplits_3093_; lean_object* v_elimEqs_3094_; lean_object* v_elimStack_3095_; lean_object* v_occurs_3096_; lean_object* v_ignored_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3111_; 
v_v_3054_ = lean_array_fget(v_structs_3041_, v___y_3037_);
v_id_3055_ = lean_ctor_get(v_v_3054_, 0);
v_ringId_x3f_3056_ = lean_ctor_get(v_v_3054_, 1);
v_type_3057_ = lean_ctor_get(v_v_3054_, 2);
v_u_3058_ = lean_ctor_get(v_v_3054_, 3);
v_intModuleInst_3059_ = lean_ctor_get(v_v_3054_, 4);
v_leInst_x3f_3060_ = lean_ctor_get(v_v_3054_, 5);
v_ltInst_x3f_3061_ = lean_ctor_get(v_v_3054_, 6);
v_lawfulOrderLTInst_x3f_3062_ = lean_ctor_get(v_v_3054_, 7);
v_isPreorderInst_x3f_3063_ = lean_ctor_get(v_v_3054_, 8);
v_orderedAddInst_x3f_3064_ = lean_ctor_get(v_v_3054_, 9);
v_isLinearInst_x3f_3065_ = lean_ctor_get(v_v_3054_, 10);
v_noNatDivInst_x3f_3066_ = lean_ctor_get(v_v_3054_, 11);
v_ringInst_x3f_3067_ = lean_ctor_get(v_v_3054_, 12);
v_commRingInst_x3f_3068_ = lean_ctor_get(v_v_3054_, 13);
v_orderedRingInst_x3f_3069_ = lean_ctor_get(v_v_3054_, 14);
v_fieldInst_x3f_3070_ = lean_ctor_get(v_v_3054_, 15);
v_charInst_x3f_3071_ = lean_ctor_get(v_v_3054_, 16);
v_zero_3072_ = lean_ctor_get(v_v_3054_, 17);
v_ofNatZero_3073_ = lean_ctor_get(v_v_3054_, 18);
v_one_x3f_3074_ = lean_ctor_get(v_v_3054_, 19);
v_leFn_x3f_3075_ = lean_ctor_get(v_v_3054_, 20);
v_ltFn_x3f_3076_ = lean_ctor_get(v_v_3054_, 21);
v_addFn_3077_ = lean_ctor_get(v_v_3054_, 22);
v_zsmulFn_3078_ = lean_ctor_get(v_v_3054_, 23);
v_nsmulFn_3079_ = lean_ctor_get(v_v_3054_, 24);
v_zsmulFn_x3f_3080_ = lean_ctor_get(v_v_3054_, 25);
v_nsmulFn_x3f_3081_ = lean_ctor_get(v_v_3054_, 26);
v_homomulFn_x3f_3082_ = lean_ctor_get(v_v_3054_, 27);
v_subFn_3083_ = lean_ctor_get(v_v_3054_, 28);
v_negFn_3084_ = lean_ctor_get(v_v_3054_, 29);
v_vars_3085_ = lean_ctor_get(v_v_3054_, 30);
v_varMap_3086_ = lean_ctor_get(v_v_3054_, 31);
v_lowers_3087_ = lean_ctor_get(v_v_3054_, 32);
v_uppers_3088_ = lean_ctor_get(v_v_3054_, 33);
v_diseqs_3089_ = lean_ctor_get(v_v_3054_, 34);
v_assignment_3090_ = lean_ctor_get(v_v_3054_, 35);
v_caseSplits_3091_ = lean_ctor_get_uint8(v_v_3054_, sizeof(void*)*42);
v_conflict_x3f_3092_ = lean_ctor_get(v_v_3054_, 36);
v_diseqSplits_3093_ = lean_ctor_get(v_v_3054_, 37);
v_elimEqs_3094_ = lean_ctor_get(v_v_3054_, 38);
v_elimStack_3095_ = lean_ctor_get(v_v_3054_, 39);
v_occurs_3096_ = lean_ctor_get(v_v_3054_, 40);
v_ignored_3097_ = lean_ctor_get(v_v_3054_, 41);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_v_3054_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3099_ = v_v_3054_;
v_isShared_3100_ = v_isSharedCheck_3111_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_ignored_3097_);
lean_inc(v_occurs_3096_);
lean_inc(v_elimStack_3095_);
lean_inc(v_elimEqs_3094_);
lean_inc(v_diseqSplits_3093_);
lean_inc(v_conflict_x3f_3092_);
lean_inc(v_assignment_3090_);
lean_inc(v_diseqs_3089_);
lean_inc(v_uppers_3088_);
lean_inc(v_lowers_3087_);
lean_inc(v_varMap_3086_);
lean_inc(v_vars_3085_);
lean_inc(v_negFn_3084_);
lean_inc(v_subFn_3083_);
lean_inc(v_homomulFn_x3f_3082_);
lean_inc(v_nsmulFn_x3f_3081_);
lean_inc(v_zsmulFn_x3f_3080_);
lean_inc(v_nsmulFn_3079_);
lean_inc(v_zsmulFn_3078_);
lean_inc(v_addFn_3077_);
lean_inc(v_ltFn_x3f_3076_);
lean_inc(v_leFn_x3f_3075_);
lean_inc(v_one_x3f_3074_);
lean_inc(v_ofNatZero_3073_);
lean_inc(v_zero_3072_);
lean_inc(v_charInst_x3f_3071_);
lean_inc(v_fieldInst_x3f_3070_);
lean_inc(v_orderedRingInst_x3f_3069_);
lean_inc(v_commRingInst_x3f_3068_);
lean_inc(v_ringInst_x3f_3067_);
lean_inc(v_noNatDivInst_x3f_3066_);
lean_inc(v_isLinearInst_x3f_3065_);
lean_inc(v_orderedAddInst_x3f_3064_);
lean_inc(v_isPreorderInst_x3f_3063_);
lean_inc(v_lawfulOrderLTInst_x3f_3062_);
lean_inc(v_ltInst_x3f_3061_);
lean_inc(v_leInst_x3f_3060_);
lean_inc(v_intModuleInst_3059_);
lean_inc(v_u_3058_);
lean_inc(v_type_3057_);
lean_inc(v_ringId_x3f_3056_);
lean_inc(v_id_3055_);
lean_dec(v_v_3054_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3111_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v_xs_x27_3102_; lean_object* v___x_3103_; lean_object* v___x_3105_; 
v___x_3101_ = lean_box(0);
v_xs_x27_3102_ = lean_array_fset(v_structs_3041_, v___y_3037_, v___x_3101_);
v___x_3103_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3038_, v_diseqs_3089_, v_v_3039_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 34, v___x_3103_);
v___x_3105_ = v___x_3099_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_id_3055_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_ringId_x3f_3056_);
lean_ctor_set(v_reuseFailAlloc_3110_, 2, v_type_3057_);
lean_ctor_set(v_reuseFailAlloc_3110_, 3, v_u_3058_);
lean_ctor_set(v_reuseFailAlloc_3110_, 4, v_intModuleInst_3059_);
lean_ctor_set(v_reuseFailAlloc_3110_, 5, v_leInst_x3f_3060_);
lean_ctor_set(v_reuseFailAlloc_3110_, 6, v_ltInst_x3f_3061_);
lean_ctor_set(v_reuseFailAlloc_3110_, 7, v_lawfulOrderLTInst_x3f_3062_);
lean_ctor_set(v_reuseFailAlloc_3110_, 8, v_isPreorderInst_x3f_3063_);
lean_ctor_set(v_reuseFailAlloc_3110_, 9, v_orderedAddInst_x3f_3064_);
lean_ctor_set(v_reuseFailAlloc_3110_, 10, v_isLinearInst_x3f_3065_);
lean_ctor_set(v_reuseFailAlloc_3110_, 11, v_noNatDivInst_x3f_3066_);
lean_ctor_set(v_reuseFailAlloc_3110_, 12, v_ringInst_x3f_3067_);
lean_ctor_set(v_reuseFailAlloc_3110_, 13, v_commRingInst_x3f_3068_);
lean_ctor_set(v_reuseFailAlloc_3110_, 14, v_orderedRingInst_x3f_3069_);
lean_ctor_set(v_reuseFailAlloc_3110_, 15, v_fieldInst_x3f_3070_);
lean_ctor_set(v_reuseFailAlloc_3110_, 16, v_charInst_x3f_3071_);
lean_ctor_set(v_reuseFailAlloc_3110_, 17, v_zero_3072_);
lean_ctor_set(v_reuseFailAlloc_3110_, 18, v_ofNatZero_3073_);
lean_ctor_set(v_reuseFailAlloc_3110_, 19, v_one_x3f_3074_);
lean_ctor_set(v_reuseFailAlloc_3110_, 20, v_leFn_x3f_3075_);
lean_ctor_set(v_reuseFailAlloc_3110_, 21, v_ltFn_x3f_3076_);
lean_ctor_set(v_reuseFailAlloc_3110_, 22, v_addFn_3077_);
lean_ctor_set(v_reuseFailAlloc_3110_, 23, v_zsmulFn_3078_);
lean_ctor_set(v_reuseFailAlloc_3110_, 24, v_nsmulFn_3079_);
lean_ctor_set(v_reuseFailAlloc_3110_, 25, v_zsmulFn_x3f_3080_);
lean_ctor_set(v_reuseFailAlloc_3110_, 26, v_nsmulFn_x3f_3081_);
lean_ctor_set(v_reuseFailAlloc_3110_, 27, v_homomulFn_x3f_3082_);
lean_ctor_set(v_reuseFailAlloc_3110_, 28, v_subFn_3083_);
lean_ctor_set(v_reuseFailAlloc_3110_, 29, v_negFn_3084_);
lean_ctor_set(v_reuseFailAlloc_3110_, 30, v_vars_3085_);
lean_ctor_set(v_reuseFailAlloc_3110_, 31, v_varMap_3086_);
lean_ctor_set(v_reuseFailAlloc_3110_, 32, v_lowers_3087_);
lean_ctor_set(v_reuseFailAlloc_3110_, 33, v_uppers_3088_);
lean_ctor_set(v_reuseFailAlloc_3110_, 34, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3110_, 35, v_assignment_3090_);
lean_ctor_set(v_reuseFailAlloc_3110_, 36, v_conflict_x3f_3092_);
lean_ctor_set(v_reuseFailAlloc_3110_, 37, v_diseqSplits_3093_);
lean_ctor_set(v_reuseFailAlloc_3110_, 38, v_elimEqs_3094_);
lean_ctor_set(v_reuseFailAlloc_3110_, 39, v_elimStack_3095_);
lean_ctor_set(v_reuseFailAlloc_3110_, 40, v_occurs_3096_);
lean_ctor_set(v_reuseFailAlloc_3110_, 41, v_ignored_3097_);
lean_ctor_set_uint8(v_reuseFailAlloc_3110_, sizeof(void*)*42, v_caseSplits_3091_);
v___x_3105_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3106_ = lean_array_fset(v_xs_x27_3102_, v___y_3037_, v___x_3105_);
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 0, v___x_3106_);
v___x_3108_ = v___x_3052_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3106_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_typeIdOf_3042_);
lean_ctor_set(v_reuseFailAlloc_3109_, 2, v_exprToStructId_3043_);
lean_ctor_set(v_reuseFailAlloc_3109_, 3, v_exprToStructIdEntries_3044_);
lean_ctor_set(v_reuseFailAlloc_3109_, 4, v_forbiddenNatModules_3045_);
lean_ctor_set(v_reuseFailAlloc_3109_, 5, v_natStructs_3046_);
lean_ctor_set(v_reuseFailAlloc_3109_, 6, v_natTypeIdOf_3047_);
lean_ctor_set(v_reuseFailAlloc_3109_, 7, v_exprToNatStructId_3048_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed(lean_object* v___y_3121_, lean_object* v_val_3122_, lean_object* v_v_3123_, lean_object* v_s_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(v___y_3121_, v_val_3122_, v_v_3123_, v_s_3124_);
lean_dec(v_v_3123_);
lean_dec(v___y_3121_);
return v_res_3125_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2(void){
_start:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3133_ = l_Lean_Name_append(v___x_3132_, v___x_3131_);
return v___x_3133_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3140_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3141_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3142_ = l_Lean_Name_append(v___x_3141_, v___x_3140_);
return v___x_3142_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7(void){
_start:
{
lean_object* v_cls_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v_cls_3147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3148_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3149_ = l_Lean_Name_append(v___x_3148_, v_cls_3147_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object* v_c_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_){
_start:
{
lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v_options_3221_; lean_object* v_inheritedTraceOptions_3222_; uint8_t v_hasTrace_3223_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; 
v_options_3221_ = lean_ctor_get(v_a_3160_, 2);
v_inheritedTraceOptions_3222_ = lean_ctor_get(v_a_3160_, 13);
v_hasTrace_3223_ = lean_ctor_get_uint8(v_options_3221_, sizeof(void*)*1);
if (v_hasTrace_3223_ == 0)
{
v___y_3225_ = v_a_3151_;
v___y_3226_ = v_a_3152_;
v___y_3227_ = v_a_3153_;
v___y_3228_ = v_a_3154_;
v___y_3229_ = v_a_3155_;
v___y_3230_ = v_a_3156_;
v___y_3231_ = v_a_3157_;
v___y_3232_ = v_a_3158_;
v___y_3233_ = v_a_3159_;
v___y_3234_ = v_a_3160_;
v___y_3235_ = v_a_3161_;
goto v___jp_3224_;
}
else
{
lean_object* v_cls_3294_; lean_object* v___x_3295_; uint8_t v___x_3296_; 
v_cls_3294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3295_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_3296_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3222_, v_options_3221_, v___x_3295_);
if (v___x_3296_ == 0)
{
v___y_3225_ = v_a_3151_;
v___y_3226_ = v_a_3152_;
v___y_3227_ = v_a_3153_;
v___y_3228_ = v_a_3154_;
v___y_3229_ = v_a_3155_;
v___y_3230_ = v_a_3156_;
v___y_3231_ = v_a_3157_;
v___y_3232_ = v_a_3158_;
v___y_3233_ = v_a_3159_;
v___y_3234_ = v_a_3160_;
v___y_3235_ = v_a_3161_;
goto v___jp_3224_;
}
else
{
lean_object* v___x_3297_; 
v___x_3297_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref(v___x_3297_);
v___x_3299_ = l_Lean_MessageData_ofExpr(v_a_3298_);
v___x_3300_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_3294_, v___x_3299_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_dec_ref(v___x_3300_);
v___y_3225_ = v_a_3151_;
v___y_3226_ = v_a_3152_;
v___y_3227_ = v_a_3153_;
v___y_3228_ = v_a_3154_;
v___y_3229_ = v_a_3155_;
v___y_3230_ = v_a_3156_;
v___y_3231_ = v_a_3157_;
v___y_3232_ = v_a_3158_;
v___y_3233_ = v_a_3159_;
v___y_3234_ = v_a_3160_;
v___y_3235_ = v_a_3161_;
goto v___jp_3224_;
}
else
{
lean_dec_ref(v_c_3150_);
return v___x_3300_;
}
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
lean_dec_ref(v_c_3150_);
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
v___jp_3163_:
{
lean_object* v___x_3180_; 
v___x_3180_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_3167_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v___f_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
lean_dec_ref(v___x_3180_);
lean_inc(v___y_3169_);
v___f_3181_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3181_, 0, v___y_3169_);
lean_closure_set(v___f_3181_, 1, v___y_3165_);
lean_closure_set(v___f_3181_, 2, v___y_3164_);
v___x_3182_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3183_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3182_, v___f_3181_, v___y_3170_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v___x_3184_; 
lean_dec_ref(v___x_3183_);
v___x_3184_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3197_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3187_ = v___x_3184_;
v_isShared_3188_ = v_isSharedCheck_3197_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3184_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3197_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
uint8_t v___x_3189_; uint8_t v___x_3190_; uint8_t v___x_3191_; 
v___x_3189_ = 0;
v___x_3190_ = lean_unbox(v_a_3185_);
lean_dec(v_a_3185_);
v___x_3191_ = l_Lean_instBEqLBool_beq(v___x_3190_, v___x_3189_);
if (v___x_3191_ == 0)
{
lean_object* v___x_3192_; lean_object* v___x_3194_; 
lean_dec(v___y_3166_);
v___x_3192_ = lean_box(0);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 0, v___x_3192_);
v___x_3194_ = v___x_3187_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3192_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
else
{
lean_object* v___x_3196_; 
lean_del_object(v___x_3187_);
v___x_3196_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_3166_, v___y_3169_, v___y_3170_);
return v___x_3196_;
}
}
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_dec(v___y_3166_);
v_a_3198_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3184_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3184_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
else
{
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3166_);
return v___x_3183_;
}
}
else
{
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
return v___x_3180_;
}
}
v___jp_3206_:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3219_, 0, v___y_3207_);
v___x_3220_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(v___x_3219_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
return v___x_3220_;
}
v___jp_3224_:
{
lean_object* v___x_3236_; 
lean_inc_ref(v___y_3234_);
v___x_3236_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_3150_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3285_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3239_ = v___x_3236_;
v_isShared_3240_ = v_isSharedCheck_3285_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3236_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3285_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
if (lean_obj_tag(v_a_3237_) == 1)
{
lean_object* v_val_3241_; lean_object* v_p_3242_; 
lean_del_object(v___x_3239_);
v_val_3241_ = lean_ctor_get(v_a_3237_, 0);
lean_inc(v_val_3241_);
lean_dec_ref(v_a_3237_);
v_p_3242_ = lean_ctor_get(v_val_3241_, 0);
if (lean_obj_tag(v_p_3242_) == 0)
{
lean_object* v_options_3243_; uint8_t v_hasTrace_3244_; 
v_options_3243_ = lean_ctor_get(v___y_3234_, 2);
v_hasTrace_3244_ = lean_ctor_get_uint8(v_options_3243_, sizeof(void*)*1);
if (v_hasTrace_3244_ == 0)
{
v___y_3207_ = v_val_3241_;
v___y_3208_ = v___y_3225_;
v___y_3209_ = v___y_3226_;
v___y_3210_ = v___y_3227_;
v___y_3211_ = v___y_3228_;
v___y_3212_ = v___y_3229_;
v___y_3213_ = v___y_3230_;
v___y_3214_ = v___y_3231_;
v___y_3215_ = v___y_3232_;
v___y_3216_ = v___y_3233_;
v___y_3217_ = v___y_3234_;
v___y_3218_ = v___y_3235_;
goto v___jp_3206_;
}
else
{
lean_object* v_inheritedTraceOptions_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; uint8_t v___x_3248_; 
v_inheritedTraceOptions_3245_ = lean_ctor_get(v___y_3234_, 13);
v___x_3246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3247_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2);
v___x_3248_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3245_, v_options_3243_, v___x_3247_);
if (v___x_3248_ == 0)
{
v___y_3207_ = v_val_3241_;
v___y_3208_ = v___y_3225_;
v___y_3209_ = v___y_3226_;
v___y_3210_ = v___y_3227_;
v___y_3211_ = v___y_3228_;
v___y_3212_ = v___y_3229_;
v___y_3213_ = v___y_3230_;
v___y_3214_ = v___y_3231_;
v___y_3215_ = v___y_3232_;
v___y_3216_ = v___y_3233_;
v___y_3217_ = v___y_3234_;
v___y_3218_ = v___y_3235_;
goto v___jp_3206_;
}
else
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3241_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_a_3250_);
lean_dec_ref(v___x_3249_);
v___x_3251_ = l_Lean_MessageData_ofExpr(v_a_3250_);
v___x_3252_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3246_, v___x_3251_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_dec_ref(v___x_3252_);
v___y_3207_ = v_val_3241_;
v___y_3208_ = v___y_3225_;
v___y_3209_ = v___y_3226_;
v___y_3210_ = v___y_3227_;
v___y_3211_ = v___y_3228_;
v___y_3212_ = v___y_3229_;
v___y_3213_ = v___y_3230_;
v___y_3214_ = v___y_3231_;
v___y_3215_ = v___y_3232_;
v___y_3216_ = v___y_3233_;
v___y_3217_ = v___y_3234_;
v___y_3218_ = v___y_3235_;
goto v___jp_3206_;
}
else
{
lean_dec(v_val_3241_);
return v___x_3252_;
}
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec(v_val_3241_);
v_a_3253_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3249_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3249_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
}
}
else
{
lean_object* v_options_3261_; uint8_t v_hasTrace_3262_; 
lean_inc_ref(v_p_3242_);
v_options_3261_ = lean_ctor_get(v___y_3234_, 2);
v_hasTrace_3262_ = lean_ctor_get_uint8(v_options_3261_, sizeof(void*)*1);
if (v_hasTrace_3262_ == 0)
{
lean_object* v_v_3263_; 
v_v_3263_ = lean_ctor_get(v_p_3242_, 1);
lean_inc_n(v_v_3263_, 2);
lean_inc(v_val_3241_);
v___y_3164_ = v_v_3263_;
v___y_3165_ = v_val_3241_;
v___y_3166_ = v_v_3263_;
v___y_3167_ = v_p_3242_;
v___y_3168_ = v_val_3241_;
v___y_3169_ = v___y_3225_;
v___y_3170_ = v___y_3226_;
v___y_3171_ = v___y_3227_;
v___y_3172_ = v___y_3228_;
v___y_3173_ = v___y_3229_;
v___y_3174_ = v___y_3230_;
v___y_3175_ = v___y_3231_;
v___y_3176_ = v___y_3232_;
v___y_3177_ = v___y_3233_;
v___y_3178_ = v___y_3234_;
v___y_3179_ = v___y_3235_;
goto v___jp_3163_;
}
else
{
lean_object* v_v_3264_; lean_object* v_inheritedTraceOptions_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; uint8_t v___x_3268_; 
v_v_3264_ = lean_ctor_get(v_p_3242_, 1);
lean_inc(v_v_3264_);
v_inheritedTraceOptions_3265_ = lean_ctor_get(v___y_3234_, 13);
v___x_3266_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3267_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_3268_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3265_, v_options_3261_, v___x_3267_);
if (v___x_3268_ == 0)
{
lean_inc(v_val_3241_);
lean_inc(v_v_3264_);
v___y_3164_ = v_v_3264_;
v___y_3165_ = v_val_3241_;
v___y_3166_ = v_v_3264_;
v___y_3167_ = v_p_3242_;
v___y_3168_ = v_val_3241_;
v___y_3169_ = v___y_3225_;
v___y_3170_ = v___y_3226_;
v___y_3171_ = v___y_3227_;
v___y_3172_ = v___y_3228_;
v___y_3173_ = v___y_3229_;
v___y_3174_ = v___y_3230_;
v___y_3175_ = v___y_3231_;
v___y_3176_ = v___y_3232_;
v___y_3177_ = v___y_3233_;
v___y_3178_ = v___y_3234_;
v___y_3179_ = v___y_3235_;
goto v___jp_3163_;
}
else
{
lean_object* v___x_3269_; 
v___x_3269_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3241_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_a_3270_);
lean_dec_ref(v___x_3269_);
v___x_3271_ = l_Lean_MessageData_ofExpr(v_a_3270_);
v___x_3272_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3266_, v___x_3271_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_dec_ref(v___x_3272_);
lean_inc(v_val_3241_);
lean_inc(v_v_3264_);
v___y_3164_ = v_v_3264_;
v___y_3165_ = v_val_3241_;
v___y_3166_ = v_v_3264_;
v___y_3167_ = v_p_3242_;
v___y_3168_ = v_val_3241_;
v___y_3169_ = v___y_3225_;
v___y_3170_ = v___y_3226_;
v___y_3171_ = v___y_3227_;
v___y_3172_ = v___y_3228_;
v___y_3173_ = v___y_3229_;
v___y_3174_ = v___y_3230_;
v___y_3175_ = v___y_3231_;
v___y_3176_ = v___y_3232_;
v___y_3177_ = v___y_3233_;
v___y_3178_ = v___y_3234_;
v___y_3179_ = v___y_3235_;
goto v___jp_3163_;
}
else
{
lean_dec(v_v_3264_);
lean_dec_ref(v_p_3242_);
lean_dec(v_val_3241_);
return v___x_3272_;
}
}
else
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
lean_dec(v_v_3264_);
lean_dec_ref(v_p_3242_);
lean_dec(v_val_3241_);
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
lean_dec(v_a_3237_);
v___x_3281_ = lean_box(0);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 0, v___x_3281_);
v___x_3283_ = v___x_3239_;
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
v_a_3286_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3236_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3236_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___boxed(lean_object* v_c_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_c_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
lean_dec(v_a_3318_);
lean_dec_ref(v_a_3317_);
lean_dec(v_a_3316_);
lean_dec_ref(v_a_3315_);
lean_dec(v_a_3314_);
lean_dec_ref(v_a_3313_);
lean_dec(v_a_3312_);
lean_dec(v_a_3311_);
lean_dec(v_a_3310_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_3323_, lean_object* v_as_3324_, size_t v_sz_3325_, size_t v_i_3326_, lean_object* v_b_3327_){
_start:
{
uint8_t v___x_3328_; 
v___x_3328_ = lean_usize_dec_lt(v_i_3326_, v_sz_3325_);
if (v___x_3328_ == 0)
{
return v_b_3327_;
}
else
{
lean_object* v_snd_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3370_; 
v_snd_3329_ = lean_ctor_get(v_b_3327_, 1);
v_isSharedCheck_3370_ = !lean_is_exclusive(v_b_3327_);
if (v_isSharedCheck_3370_ == 0)
{
lean_object* v_unused_3371_; 
v_unused_3371_ = lean_ctor_get(v_b_3327_, 0);
lean_dec(v_unused_3371_);
v___x_3331_ = v_b_3327_;
v_isShared_3332_ = v_isSharedCheck_3370_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_snd_3329_);
lean_dec(v_b_3327_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3370_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v_fst_3333_; lean_object* v_snd_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3369_; 
v_fst_3333_ = lean_ctor_get(v_snd_3329_, 0);
v_snd_3334_ = lean_ctor_get(v_snd_3329_, 1);
v_isSharedCheck_3369_ = !lean_is_exclusive(v_snd_3329_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3336_ = v_snd_3329_;
v_isShared_3337_ = v_isSharedCheck_3369_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_snd_3334_);
lean_inc(v_fst_3333_);
lean_dec(v_snd_3329_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3369_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v_a_3338_; lean_object* v_p_3339_; lean_object* v___x_3340_; lean_object* v_a_3342_; lean_object* v_b_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; 
v_a_3338_ = lean_array_uget(v_as_3324_, v_i_3326_);
v_p_3339_ = lean_ctor_get(v_a_3338_, 0);
v___x_3340_ = lean_box(0);
v_b_3349_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3339_, v_x_3323_);
v___x_3350_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3351_ = lean_int_dec_eq(v_b_3349_, v___x_3350_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3353_; 
lean_inc(v_a_3338_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 1, v_a_3338_);
lean_ctor_set(v___x_3331_, 0, v_b_3349_);
v___x_3353_ = v___x_3331_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_b_3349_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v_a_3338_);
v___x_3353_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3361_; 
v_isSharedCheck_3361_ = !lean_is_exclusive(v_a_3338_);
if (v_isSharedCheck_3361_ == 0)
{
lean_object* v_unused_3362_; lean_object* v_unused_3363_; 
v_unused_3362_ = lean_ctor_get(v_a_3338_, 1);
lean_dec(v_unused_3362_);
v_unused_3363_ = lean_ctor_get(v_a_3338_, 0);
lean_dec(v_unused_3363_);
v___x_3355_ = v_a_3338_;
v_isShared_3356_ = v_isSharedCheck_3361_;
goto v_resetjp_3354_;
}
else
{
lean_dec(v_a_3338_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3361_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v_todo_3357_; lean_object* v___x_3359_; 
v_todo_3357_ = lean_array_push(v_snd_3334_, v___x_3353_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 1, v_todo_3357_);
lean_ctor_set(v___x_3355_, 0, v_fst_3333_);
v___x_3359_ = v___x_3355_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_fst_3333_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v_todo_3357_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
v_a_3342_ = v___x_3359_;
goto v___jp_3341_;
}
}
}
}
else
{
lean_object* v_cs_x27_3365_; lean_object* v___x_3367_; 
lean_dec(v_b_3349_);
v_cs_x27_3365_ = l_Lean_PersistentArray_push___redArg(v_fst_3333_, v_a_3338_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 1, v_snd_3334_);
lean_ctor_set(v___x_3331_, 0, v_cs_x27_3365_);
v___x_3367_ = v___x_3331_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_cs_x27_3365_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_snd_3334_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
v_a_3342_ = v___x_3367_;
goto v___jp_3341_;
}
}
v___jp_3341_:
{
lean_object* v___x_3344_; 
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 1, v_a_3342_);
lean_ctor_set(v___x_3336_, 0, v___x_3340_);
v___x_3344_ = v___x_3336_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3340_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v_a_3342_);
v___x_3344_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
size_t v___x_3345_; size_t v___x_3346_; 
v___x_3345_ = ((size_t)1ULL);
v___x_3346_ = lean_usize_add(v_i_3326_, v___x_3345_);
v_i_3326_ = v___x_3346_;
v_b_3327_ = v___x_3344_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_3372_, lean_object* v_as_3373_, lean_object* v_sz_3374_, lean_object* v_i_3375_, lean_object* v_b_3376_){
_start:
{
size_t v_sz_boxed_3377_; size_t v_i_boxed_3378_; lean_object* v_res_3379_; 
v_sz_boxed_3377_ = lean_unbox_usize(v_sz_3374_);
lean_dec(v_sz_3374_);
v_i_boxed_3378_ = lean_unbox_usize(v_i_3375_);
lean_dec(v_i_3375_);
v_res_3379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3372_, v_as_3373_, v_sz_boxed_3377_, v_i_boxed_3378_, v_b_3376_);
lean_dec_ref(v_as_3373_);
lean_dec(v_x_3372_);
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(lean_object* v_x_3380_, lean_object* v_as_3381_, size_t v_sz_3382_, size_t v_i_3383_, lean_object* v_b_3384_){
_start:
{
uint8_t v___x_3385_; 
v___x_3385_ = lean_usize_dec_lt(v_i_3383_, v_sz_3382_);
if (v___x_3385_ == 0)
{
return v_b_3384_;
}
else
{
lean_object* v_snd_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3427_; 
v_snd_3386_ = lean_ctor_get(v_b_3384_, 1);
v_isSharedCheck_3427_ = !lean_is_exclusive(v_b_3384_);
if (v_isSharedCheck_3427_ == 0)
{
lean_object* v_unused_3428_; 
v_unused_3428_ = lean_ctor_get(v_b_3384_, 0);
lean_dec(v_unused_3428_);
v___x_3388_ = v_b_3384_;
v_isShared_3389_ = v_isSharedCheck_3427_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_snd_3386_);
lean_dec(v_b_3384_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3427_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v_fst_3390_; lean_object* v_snd_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3426_; 
v_fst_3390_ = lean_ctor_get(v_snd_3386_, 0);
v_snd_3391_ = lean_ctor_get(v_snd_3386_, 1);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_snd_3386_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3393_ = v_snd_3386_;
v_isShared_3394_ = v_isSharedCheck_3426_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_snd_3391_);
lean_inc(v_fst_3390_);
lean_dec(v_snd_3386_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3426_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v_a_3395_; lean_object* v_p_3396_; lean_object* v___x_3397_; lean_object* v_a_3399_; lean_object* v_b_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; 
v_a_3395_ = lean_array_uget(v_as_3381_, v_i_3383_);
v_p_3396_ = lean_ctor_get(v_a_3395_, 0);
v___x_3397_ = lean_box(0);
v_b_3406_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3396_, v_x_3380_);
v___x_3407_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3408_ = lean_int_dec_eq(v_b_3406_, v___x_3407_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3410_; 
lean_inc(v_a_3395_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 1, v_a_3395_);
lean_ctor_set(v___x_3388_, 0, v_b_3406_);
v___x_3410_ = v___x_3388_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_b_3406_);
lean_ctor_set(v_reuseFailAlloc_3421_, 1, v_a_3395_);
v___x_3410_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3418_; 
v_isSharedCheck_3418_ = !lean_is_exclusive(v_a_3395_);
if (v_isSharedCheck_3418_ == 0)
{
lean_object* v_unused_3419_; lean_object* v_unused_3420_; 
v_unused_3419_ = lean_ctor_get(v_a_3395_, 1);
lean_dec(v_unused_3419_);
v_unused_3420_ = lean_ctor_get(v_a_3395_, 0);
lean_dec(v_unused_3420_);
v___x_3412_ = v_a_3395_;
v_isShared_3413_ = v_isSharedCheck_3418_;
goto v_resetjp_3411_;
}
else
{
lean_dec(v_a_3395_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3418_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v_todo_3414_; lean_object* v___x_3416_; 
v_todo_3414_ = lean_array_push(v_snd_3391_, v___x_3410_);
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 1, v_todo_3414_);
lean_ctor_set(v___x_3412_, 0, v_fst_3390_);
v___x_3416_ = v___x_3412_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_fst_3390_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v_todo_3414_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
v_a_3399_ = v___x_3416_;
goto v___jp_3398_;
}
}
}
}
else
{
lean_object* v_cs_x27_3422_; lean_object* v___x_3424_; 
lean_dec(v_b_3406_);
v_cs_x27_3422_ = l_Lean_PersistentArray_push___redArg(v_fst_3390_, v_a_3395_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 1, v_snd_3391_);
lean_ctor_set(v___x_3388_, 0, v_cs_x27_3422_);
v___x_3424_ = v___x_3388_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_cs_x27_3422_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v_snd_3391_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
v_a_3399_ = v___x_3424_;
goto v___jp_3398_;
}
}
v___jp_3398_:
{
lean_object* v___x_3401_; 
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 1, v_a_3399_);
lean_ctor_set(v___x_3393_, 0, v___x_3397_);
v___x_3401_ = v___x_3393_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3397_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v_a_3399_);
v___x_3401_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
size_t v___x_3402_; size_t v___x_3403_; lean_object* v___x_3404_; 
v___x_3402_ = ((size_t)1ULL);
v___x_3403_ = lean_usize_add(v_i_3383_, v___x_3402_);
v___x_3404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3380_, v_as_3381_, v_sz_3382_, v___x_3403_, v___x_3401_);
return v___x_3404_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_3429_, lean_object* v_as_3430_, lean_object* v_sz_3431_, lean_object* v_i_3432_, lean_object* v_b_3433_){
_start:
{
size_t v_sz_boxed_3434_; size_t v_i_boxed_3435_; lean_object* v_res_3436_; 
v_sz_boxed_3434_ = lean_unbox_usize(v_sz_3431_);
lean_dec(v_sz_3431_);
v_i_boxed_3435_ = lean_unbox_usize(v_i_3432_);
lean_dec(v_i_3432_);
v_res_3436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3429_, v_as_3430_, v_sz_boxed_3434_, v_i_boxed_3435_, v_b_3433_);
lean_dec_ref(v_as_3430_);
lean_dec(v_x_3429_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_3437_, lean_object* v_as_3438_, size_t v_sz_3439_, size_t v_i_3440_, lean_object* v_b_3441_){
_start:
{
uint8_t v___x_3442_; 
v___x_3442_ = lean_usize_dec_lt(v_i_3440_, v_sz_3439_);
if (v___x_3442_ == 0)
{
return v_b_3441_;
}
else
{
lean_object* v_snd_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3484_; 
v_snd_3443_ = lean_ctor_get(v_b_3441_, 1);
v_isSharedCheck_3484_ = !lean_is_exclusive(v_b_3441_);
if (v_isSharedCheck_3484_ == 0)
{
lean_object* v_unused_3485_; 
v_unused_3485_ = lean_ctor_get(v_b_3441_, 0);
lean_dec(v_unused_3485_);
v___x_3445_ = v_b_3441_;
v_isShared_3446_ = v_isSharedCheck_3484_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_snd_3443_);
lean_dec(v_b_3441_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3484_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v_fst_3447_; lean_object* v_snd_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3483_; 
v_fst_3447_ = lean_ctor_get(v_snd_3443_, 0);
v_snd_3448_ = lean_ctor_get(v_snd_3443_, 1);
v_isSharedCheck_3483_ = !lean_is_exclusive(v_snd_3443_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3450_ = v_snd_3443_;
v_isShared_3451_ = v_isSharedCheck_3483_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_snd_3448_);
lean_inc(v_fst_3447_);
lean_dec(v_snd_3443_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3483_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v_a_3452_; lean_object* v_p_3453_; lean_object* v___x_3454_; lean_object* v_a_3456_; lean_object* v_b_3463_; lean_object* v___x_3464_; uint8_t v___x_3465_; 
v_a_3452_ = lean_array_uget(v_as_3438_, v_i_3440_);
v_p_3453_ = lean_ctor_get(v_a_3452_, 0);
v___x_3454_ = lean_box(0);
v_b_3463_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3453_, v_x_3437_);
v___x_3464_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3465_ = lean_int_dec_eq(v_b_3463_, v___x_3464_);
if (v___x_3465_ == 0)
{
lean_object* v___x_3467_; 
lean_inc(v_a_3452_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 1, v_a_3452_);
lean_ctor_set(v___x_3445_, 0, v_b_3463_);
v___x_3467_ = v___x_3445_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_b_3463_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_a_3452_);
v___x_3467_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3475_; 
v_isSharedCheck_3475_ = !lean_is_exclusive(v_a_3452_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; lean_object* v_unused_3477_; 
v_unused_3476_ = lean_ctor_get(v_a_3452_, 1);
lean_dec(v_unused_3476_);
v_unused_3477_ = lean_ctor_get(v_a_3452_, 0);
lean_dec(v_unused_3477_);
v___x_3469_ = v_a_3452_;
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
else
{
lean_dec(v_a_3452_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v_todo_3471_; lean_object* v___x_3473_; 
v_todo_3471_ = lean_array_push(v_snd_3448_, v___x_3467_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 1, v_todo_3471_);
lean_ctor_set(v___x_3469_, 0, v_fst_3447_);
v___x_3473_ = v___x_3469_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_fst_3447_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v_todo_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
v_a_3456_ = v___x_3473_;
goto v___jp_3455_;
}
}
}
}
else
{
lean_object* v_cs_x27_3479_; lean_object* v___x_3481_; 
lean_dec(v_b_3463_);
v_cs_x27_3479_ = l_Lean_PersistentArray_push___redArg(v_fst_3447_, v_a_3452_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 1, v_snd_3448_);
lean_ctor_set(v___x_3445_, 0, v_cs_x27_3479_);
v___x_3481_ = v___x_3445_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_cs_x27_3479_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v_snd_3448_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
v_a_3456_ = v___x_3481_;
goto v___jp_3455_;
}
}
v___jp_3455_:
{
lean_object* v___x_3458_; 
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 1, v_a_3456_);
lean_ctor_set(v___x_3450_, 0, v___x_3454_);
v___x_3458_ = v___x_3450_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3454_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v_a_3456_);
v___x_3458_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
size_t v___x_3459_; size_t v___x_3460_; 
v___x_3459_ = ((size_t)1ULL);
v___x_3460_ = lean_usize_add(v_i_3440_, v___x_3459_);
v_i_3440_ = v___x_3460_;
v_b_3441_ = v___x_3458_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3486_, lean_object* v_as_3487_, lean_object* v_sz_3488_, lean_object* v_i_3489_, lean_object* v_b_3490_){
_start:
{
size_t v_sz_boxed_3491_; size_t v_i_boxed_3492_; lean_object* v_res_3493_; 
v_sz_boxed_3491_ = lean_unbox_usize(v_sz_3488_);
lean_dec(v_sz_3488_);
v_i_boxed_3492_ = lean_unbox_usize(v_i_3489_);
lean_dec(v_i_3489_);
v_res_3493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3486_, v_as_3487_, v_sz_boxed_3491_, v_i_boxed_3492_, v_b_3490_);
lean_dec_ref(v_as_3487_);
lean_dec(v_x_3486_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_3494_, lean_object* v_as_3495_, size_t v_sz_3496_, size_t v_i_3497_, lean_object* v_b_3498_){
_start:
{
uint8_t v___x_3499_; 
v___x_3499_ = lean_usize_dec_lt(v_i_3497_, v_sz_3496_);
if (v___x_3499_ == 0)
{
return v_b_3498_;
}
else
{
lean_object* v_snd_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3541_; 
v_snd_3500_ = lean_ctor_get(v_b_3498_, 1);
v_isSharedCheck_3541_ = !lean_is_exclusive(v_b_3498_);
if (v_isSharedCheck_3541_ == 0)
{
lean_object* v_unused_3542_; 
v_unused_3542_ = lean_ctor_get(v_b_3498_, 0);
lean_dec(v_unused_3542_);
v___x_3502_ = v_b_3498_;
v_isShared_3503_ = v_isSharedCheck_3541_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_snd_3500_);
lean_dec(v_b_3498_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3541_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v_fst_3504_; lean_object* v_snd_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3540_; 
v_fst_3504_ = lean_ctor_get(v_snd_3500_, 0);
v_snd_3505_ = lean_ctor_get(v_snd_3500_, 1);
v_isSharedCheck_3540_ = !lean_is_exclusive(v_snd_3500_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3507_ = v_snd_3500_;
v_isShared_3508_ = v_isSharedCheck_3540_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_snd_3505_);
lean_inc(v_fst_3504_);
lean_dec(v_snd_3500_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3540_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v_a_3509_; lean_object* v_p_3510_; lean_object* v___x_3511_; lean_object* v_a_3513_; lean_object* v_b_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v_a_3509_ = lean_array_uget(v_as_3495_, v_i_3497_);
v_p_3510_ = lean_ctor_get(v_a_3509_, 0);
v___x_3511_ = lean_box(0);
v_b_3520_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3510_, v_x_3494_);
v___x_3521_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3522_ = lean_int_dec_eq(v_b_3520_, v___x_3521_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3524_; 
lean_inc(v_a_3509_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 1, v_a_3509_);
lean_ctor_set(v___x_3502_, 0, v_b_3520_);
v___x_3524_ = v___x_3502_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_b_3520_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v_a_3509_);
v___x_3524_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3532_; 
v_isSharedCheck_3532_ = !lean_is_exclusive(v_a_3509_);
if (v_isSharedCheck_3532_ == 0)
{
lean_object* v_unused_3533_; lean_object* v_unused_3534_; 
v_unused_3533_ = lean_ctor_get(v_a_3509_, 1);
lean_dec(v_unused_3533_);
v_unused_3534_ = lean_ctor_get(v_a_3509_, 0);
lean_dec(v_unused_3534_);
v___x_3526_ = v_a_3509_;
v_isShared_3527_ = v_isSharedCheck_3532_;
goto v_resetjp_3525_;
}
else
{
lean_dec(v_a_3509_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3532_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v_todo_3528_; lean_object* v___x_3530_; 
v_todo_3528_ = lean_array_push(v_snd_3505_, v___x_3524_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 1, v_todo_3528_);
lean_ctor_set(v___x_3526_, 0, v_fst_3504_);
v___x_3530_ = v___x_3526_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_fst_3504_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v_todo_3528_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
v_a_3513_ = v___x_3530_;
goto v___jp_3512_;
}
}
}
}
else
{
lean_object* v_cs_x27_3536_; lean_object* v___x_3538_; 
lean_dec(v_b_3520_);
v_cs_x27_3536_ = l_Lean_PersistentArray_push___redArg(v_fst_3504_, v_a_3509_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 1, v_snd_3505_);
lean_ctor_set(v___x_3502_, 0, v_cs_x27_3536_);
v___x_3538_ = v___x_3502_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_cs_x27_3536_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_snd_3505_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
v_a_3513_ = v___x_3538_;
goto v___jp_3512_;
}
}
v___jp_3512_:
{
lean_object* v___x_3515_; 
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 1, v_a_3513_);
lean_ctor_set(v___x_3507_, 0, v___x_3511_);
v___x_3515_ = v___x_3507_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3511_);
lean_ctor_set(v_reuseFailAlloc_3519_, 1, v_a_3513_);
v___x_3515_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
size_t v___x_3516_; size_t v___x_3517_; lean_object* v___x_3518_; 
v___x_3516_ = ((size_t)1ULL);
v___x_3517_ = lean_usize_add(v_i_3497_, v___x_3516_);
v___x_3518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3494_, v_as_3495_, v_sz_3496_, v___x_3517_, v___x_3515_);
return v___x_3518_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_3543_, lean_object* v_as_3544_, lean_object* v_sz_3545_, lean_object* v_i_3546_, lean_object* v_b_3547_){
_start:
{
size_t v_sz_boxed_3548_; size_t v_i_boxed_3549_; lean_object* v_res_3550_; 
v_sz_boxed_3548_ = lean_unbox_usize(v_sz_3545_);
lean_dec(v_sz_3545_);
v_i_boxed_3549_ = lean_unbox_usize(v_i_3546_);
lean_dec(v_i_3546_);
v_res_3550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3543_, v_as_3544_, v_sz_boxed_3548_, v_i_boxed_3549_, v_b_3547_);
lean_dec_ref(v_as_3544_);
lean_dec(v_x_3543_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(lean_object* v_init_3551_, lean_object* v_x_3552_, lean_object* v_n_3553_, lean_object* v_b_3554_){
_start:
{
if (lean_obj_tag(v_n_3553_) == 0)
{
lean_object* v_cs_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3570_; 
v_cs_3555_ = lean_ctor_get(v_n_3553_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v_n_3553_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3557_ = v_n_3553_;
v_isShared_3558_ = v_isSharedCheck_3570_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_cs_3555_);
lean_dec(v_n_3553_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3570_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; size_t v_sz_3561_; size_t v___x_3562_; lean_object* v___x_3563_; lean_object* v_fst_3564_; 
v___x_3559_ = lean_box(0);
v___x_3560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3559_);
lean_ctor_set(v___x_3560_, 1, v_b_3554_);
v_sz_3561_ = lean_array_size(v_cs_3555_);
v___x_3562_ = ((size_t)0ULL);
v___x_3563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3551_, v_x_3552_, v_cs_3555_, v_sz_3561_, v___x_3562_, v___x_3560_);
lean_dec_ref(v_cs_3555_);
v_fst_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_fst_3564_);
if (lean_obj_tag(v_fst_3564_) == 0)
{
lean_object* v_snd_3565_; lean_object* v___x_3567_; 
v_snd_3565_ = lean_ctor_get(v___x_3563_, 1);
lean_inc(v_snd_3565_);
lean_dec_ref(v___x_3563_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set_tag(v___x_3557_, 1);
lean_ctor_set(v___x_3557_, 0, v_snd_3565_);
v___x_3567_ = v___x_3557_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_snd_3565_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
else
{
lean_object* v_val_3569_; 
lean_dec_ref(v___x_3563_);
lean_del_object(v___x_3557_);
v_val_3569_ = lean_ctor_get(v_fst_3564_, 0);
lean_inc(v_val_3569_);
lean_dec_ref(v_fst_3564_);
return v_val_3569_;
}
}
}
else
{
lean_object* v_vs_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3586_; 
v_vs_3571_ = lean_ctor_get(v_n_3553_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v_n_3553_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3573_ = v_n_3553_;
v_isShared_3574_ = v_isSharedCheck_3586_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_vs_3571_);
lean_dec(v_n_3553_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3586_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; size_t v_sz_3577_; size_t v___x_3578_; lean_object* v___x_3579_; lean_object* v_fst_3580_; 
v___x_3575_ = lean_box(0);
v___x_3576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3575_);
lean_ctor_set(v___x_3576_, 1, v_b_3554_);
v_sz_3577_ = lean_array_size(v_vs_3571_);
v___x_3578_ = ((size_t)0ULL);
v___x_3579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3552_, v_vs_3571_, v_sz_3577_, v___x_3578_, v___x_3576_);
lean_dec_ref(v_vs_3571_);
v_fst_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_fst_3580_);
if (lean_obj_tag(v_fst_3580_) == 0)
{
lean_object* v_snd_3581_; lean_object* v___x_3583_; 
v_snd_3581_ = lean_ctor_get(v___x_3579_, 1);
lean_inc(v_snd_3581_);
lean_dec_ref(v___x_3579_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v_snd_3581_);
v___x_3583_ = v___x_3573_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_snd_3581_);
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
lean_object* v_val_3585_; 
lean_dec_ref(v___x_3579_);
lean_del_object(v___x_3573_);
v_val_3585_ = lean_ctor_get(v_fst_3580_, 0);
lean_inc(v_val_3585_);
lean_dec_ref(v_fst_3580_);
return v_val_3585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3587_, lean_object* v_x_3588_, lean_object* v_as_3589_, size_t v_sz_3590_, size_t v_i_3591_, lean_object* v_b_3592_){
_start:
{
uint8_t v___x_3593_; 
v___x_3593_ = lean_usize_dec_lt(v_i_3591_, v_sz_3590_);
if (v___x_3593_ == 0)
{
return v_b_3592_;
}
else
{
lean_object* v_snd_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3612_; 
v_snd_3594_ = lean_ctor_get(v_b_3592_, 1);
v_isSharedCheck_3612_ = !lean_is_exclusive(v_b_3592_);
if (v_isSharedCheck_3612_ == 0)
{
lean_object* v_unused_3613_; 
v_unused_3613_ = lean_ctor_get(v_b_3592_, 0);
lean_dec(v_unused_3613_);
v___x_3596_ = v_b_3592_;
v_isShared_3597_ = v_isSharedCheck_3612_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_snd_3594_);
lean_dec(v_b_3592_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3612_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v_a_3598_; lean_object* v___x_3599_; 
v_a_3598_ = lean_array_uget_borrowed(v_as_3589_, v_i_3591_);
lean_inc(v_snd_3594_);
lean_inc(v_a_3598_);
v___x_3599_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3587_, v_x_3588_, v_a_3598_, v_snd_3594_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v___x_3600_; lean_object* v___x_3602_; 
v___x_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3599_);
if (v_isShared_3597_ == 0)
{
lean_ctor_set(v___x_3596_, 0, v___x_3600_);
v___x_3602_ = v___x_3596_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v___x_3600_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v_snd_3594_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
else
{
lean_object* v_a_3604_; lean_object* v___x_3605_; lean_object* v___x_3607_; 
lean_dec(v_snd_3594_);
v_a_3604_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_a_3604_);
lean_dec_ref(v___x_3599_);
v___x_3605_ = lean_box(0);
if (v_isShared_3597_ == 0)
{
lean_ctor_set(v___x_3596_, 1, v_a_3604_);
lean_ctor_set(v___x_3596_, 0, v___x_3605_);
v___x_3607_ = v___x_3596_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3605_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_a_3604_);
v___x_3607_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
size_t v___x_3608_; size_t v___x_3609_; 
v___x_3608_ = ((size_t)1ULL);
v___x_3609_ = lean_usize_add(v_i_3591_, v___x_3608_);
v_i_3591_ = v___x_3609_;
v_b_3592_ = v___x_3607_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3614_, lean_object* v_x_3615_, lean_object* v_as_3616_, lean_object* v_sz_3617_, lean_object* v_i_3618_, lean_object* v_b_3619_){
_start:
{
size_t v_sz_boxed_3620_; size_t v_i_boxed_3621_; lean_object* v_res_3622_; 
v_sz_boxed_3620_ = lean_unbox_usize(v_sz_3617_);
lean_dec(v_sz_3617_);
v_i_boxed_3621_ = lean_unbox_usize(v_i_3618_);
lean_dec(v_i_3618_);
v_res_3622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3614_, v_x_3615_, v_as_3616_, v_sz_boxed_3620_, v_i_boxed_3621_, v_b_3619_);
lean_dec_ref(v_as_3616_);
lean_dec(v_x_3615_);
lean_dec_ref(v_init_3614_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3623_, lean_object* v_x_3624_, lean_object* v_n_3625_, lean_object* v_b_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3623_, v_x_3624_, v_n_3625_, v_b_3626_);
lean_dec(v_x_3624_);
lean_dec_ref(v_init_3623_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object* v_x_3628_, lean_object* v_t_3629_, lean_object* v_init_3630_){
_start:
{
lean_object* v_root_3631_; lean_object* v_tail_3632_; lean_object* v___x_3633_; 
v_root_3631_ = lean_ctor_get(v_t_3629_, 0);
lean_inc_ref(v_root_3631_);
v_tail_3632_ = lean_ctor_get(v_t_3629_, 1);
lean_inc_ref(v_tail_3632_);
lean_dec_ref(v_t_3629_);
lean_inc_ref(v_init_3630_);
v___x_3633_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3630_, v_x_3628_, v_root_3631_, v_init_3630_);
lean_dec_ref(v_init_3630_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; 
lean_dec_ref(v_tail_3632_);
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref(v___x_3633_);
return v_a_3634_;
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; size_t v_sz_3638_; size_t v___x_3639_; lean_object* v___x_3640_; lean_object* v_fst_3641_; 
v_a_3635_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3635_);
lean_dec_ref(v___x_3633_);
v___x_3636_ = lean_box(0);
v___x_3637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3637_, 0, v___x_3636_);
lean_ctor_set(v___x_3637_, 1, v_a_3635_);
v_sz_3638_ = lean_array_size(v_tail_3632_);
v___x_3639_ = ((size_t)0ULL);
v___x_3640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3628_, v_tail_3632_, v_sz_3638_, v___x_3639_, v___x_3637_);
lean_dec_ref(v_tail_3632_);
v_fst_3641_ = lean_ctor_get(v___x_3640_, 0);
lean_inc(v_fst_3641_);
if (lean_obj_tag(v_fst_3641_) == 0)
{
lean_object* v_snd_3642_; 
v_snd_3642_ = lean_ctor_get(v___x_3640_, 1);
lean_inc(v_snd_3642_);
lean_dec_ref(v___x_3640_);
return v_snd_3642_;
}
else
{
lean_object* v_val_3643_; 
lean_dec_ref(v___x_3640_);
v_val_3643_ = lean_ctor_get(v_fst_3641_, 0);
lean_inc(v_val_3643_);
lean_dec_ref(v_fst_3641_);
return v_val_3643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object* v_x_3644_, lean_object* v_t_3645_, lean_object* v_init_3646_){
_start:
{
lean_object* v_res_3647_; 
v_res_3647_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3644_, v_t_3645_, v_init_3646_);
lean_dec(v_x_3644_);
return v_res_3647_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3648_ = lean_unsigned_to_nat(32u);
v___x_3649_ = lean_mk_empty_array_with_capacity(v___x_3648_);
v___x_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3649_);
return v___x_3650_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1(void){
_start:
{
size_t v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v_cs_x27_3656_; 
v___x_3651_ = ((size_t)5ULL);
v___x_3652_ = lean_unsigned_to_nat(0u);
v___x_3653_ = lean_unsigned_to_nat(32u);
v___x_3654_ = lean_mk_empty_array_with_capacity(v___x_3653_);
v___x_3655_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0);
v_cs_x27_3656_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_3656_, 0, v___x_3655_);
lean_ctor_set(v_cs_x27_3656_, 1, v___x_3654_);
lean_ctor_set(v_cs_x27_3656_, 2, v___x_3652_);
lean_ctor_set(v_cs_x27_3656_, 3, v___x_3652_);
lean_ctor_set_usize(v_cs_x27_3656_, 4, v___x_3651_);
return v_cs_x27_3656_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_3659_; lean_object* v_cs_x27_3660_; lean_object* v___x_3661_; 
v_todo_3659_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2));
v_cs_x27_3660_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1);
v___x_3661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3661_, 0, v_cs_x27_3660_);
lean_ctor_set(v___x_3661_, 1, v_todo_3659_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object* v_x_3662_, lean_object* v_cs_3663_){
_start:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v_fst_3666_; lean_object* v_snd_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
v___x_3664_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3);
v___x_3665_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3662_, v_cs_3663_, v___x_3664_);
v_fst_3666_ = lean_ctor_get(v___x_3665_, 0);
v_snd_3667_ = lean_ctor_get(v___x_3665_, 1);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___x_3665_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_snd_3667_);
lean_inc(v_fst_3666_);
lean_dec(v___x_3665_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_fst_3666_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v_snd_3667_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object* v_x_3675_, lean_object* v_cs_3676_){
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3675_, v_cs_3676_);
lean_dec(v_x_3675_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object* v_x_3678_, lean_object* v_cs_3679_){
_start:
{
lean_object* v___x_3680_; 
v___x_3680_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3678_, v_cs_3679_);
return v___x_3680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object* v_x_3681_, lean_object* v_cs_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(v_x_3681_, v_cs_3682_);
lean_dec(v_x_3681_);
return v_res_3683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(lean_object* v_a_3684_, lean_object* v_y_3685_, lean_object* v_fst_3686_, lean_object* v_s_3687_){
_start:
{
lean_object* v_structs_3688_; lean_object* v_typeIdOf_3689_; lean_object* v_exprToStructId_3690_; lean_object* v_exprToStructIdEntries_3691_; lean_object* v_forbiddenNatModules_3692_; lean_object* v_natStructs_3693_; lean_object* v_natTypeIdOf_3694_; lean_object* v_exprToNatStructId_3695_; lean_object* v___x_3696_; uint8_t v___x_3697_; 
v_structs_3688_ = lean_ctor_get(v_s_3687_, 0);
v_typeIdOf_3689_ = lean_ctor_get(v_s_3687_, 1);
v_exprToStructId_3690_ = lean_ctor_get(v_s_3687_, 2);
v_exprToStructIdEntries_3691_ = lean_ctor_get(v_s_3687_, 3);
v_forbiddenNatModules_3692_ = lean_ctor_get(v_s_3687_, 4);
v_natStructs_3693_ = lean_ctor_get(v_s_3687_, 5);
v_natTypeIdOf_3694_ = lean_ctor_get(v_s_3687_, 6);
v_exprToNatStructId_3695_ = lean_ctor_get(v_s_3687_, 7);
v___x_3696_ = lean_array_get_size(v_structs_3688_);
v___x_3697_ = lean_nat_dec_lt(v_a_3684_, v___x_3696_);
if (v___x_3697_ == 0)
{
lean_dec_ref(v_fst_3686_);
return v_s_3687_;
}
else
{
lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3759_; 
lean_inc_ref(v_exprToNatStructId_3695_);
lean_inc_ref(v_natTypeIdOf_3694_);
lean_inc_ref(v_natStructs_3693_);
lean_inc_ref(v_forbiddenNatModules_3692_);
lean_inc_ref(v_exprToStructIdEntries_3691_);
lean_inc_ref(v_exprToStructId_3690_);
lean_inc_ref(v_typeIdOf_3689_);
lean_inc_ref(v_structs_3688_);
v_isSharedCheck_3759_ = !lean_is_exclusive(v_s_3687_);
if (v_isSharedCheck_3759_ == 0)
{
lean_object* v_unused_3760_; lean_object* v_unused_3761_; lean_object* v_unused_3762_; lean_object* v_unused_3763_; lean_object* v_unused_3764_; lean_object* v_unused_3765_; lean_object* v_unused_3766_; lean_object* v_unused_3767_; 
v_unused_3760_ = lean_ctor_get(v_s_3687_, 7);
lean_dec(v_unused_3760_);
v_unused_3761_ = lean_ctor_get(v_s_3687_, 6);
lean_dec(v_unused_3761_);
v_unused_3762_ = lean_ctor_get(v_s_3687_, 5);
lean_dec(v_unused_3762_);
v_unused_3763_ = lean_ctor_get(v_s_3687_, 4);
lean_dec(v_unused_3763_);
v_unused_3764_ = lean_ctor_get(v_s_3687_, 3);
lean_dec(v_unused_3764_);
v_unused_3765_ = lean_ctor_get(v_s_3687_, 2);
lean_dec(v_unused_3765_);
v_unused_3766_ = lean_ctor_get(v_s_3687_, 1);
lean_dec(v_unused_3766_);
v_unused_3767_ = lean_ctor_get(v_s_3687_, 0);
lean_dec(v_unused_3767_);
v___x_3699_ = v_s_3687_;
v_isShared_3700_ = v_isSharedCheck_3759_;
goto v_resetjp_3698_;
}
else
{
lean_dec(v_s_3687_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3759_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v_v_3701_; lean_object* v_id_3702_; lean_object* v_ringId_x3f_3703_; lean_object* v_type_3704_; lean_object* v_u_3705_; lean_object* v_intModuleInst_3706_; lean_object* v_leInst_x3f_3707_; lean_object* v_ltInst_x3f_3708_; lean_object* v_lawfulOrderLTInst_x3f_3709_; lean_object* v_isPreorderInst_x3f_3710_; lean_object* v_orderedAddInst_x3f_3711_; lean_object* v_isLinearInst_x3f_3712_; lean_object* v_noNatDivInst_x3f_3713_; lean_object* v_ringInst_x3f_3714_; lean_object* v_commRingInst_x3f_3715_; lean_object* v_orderedRingInst_x3f_3716_; lean_object* v_fieldInst_x3f_3717_; lean_object* v_charInst_x3f_3718_; lean_object* v_zero_3719_; lean_object* v_ofNatZero_3720_; lean_object* v_one_x3f_3721_; lean_object* v_leFn_x3f_3722_; lean_object* v_ltFn_x3f_3723_; lean_object* v_addFn_3724_; lean_object* v_zsmulFn_3725_; lean_object* v_nsmulFn_3726_; lean_object* v_zsmulFn_x3f_3727_; lean_object* v_nsmulFn_x3f_3728_; lean_object* v_homomulFn_x3f_3729_; lean_object* v_subFn_3730_; lean_object* v_negFn_3731_; lean_object* v_vars_3732_; lean_object* v_varMap_3733_; lean_object* v_lowers_3734_; lean_object* v_uppers_3735_; lean_object* v_diseqs_3736_; lean_object* v_assignment_3737_; uint8_t v_caseSplits_3738_; lean_object* v_conflict_x3f_3739_; lean_object* v_diseqSplits_3740_; lean_object* v_elimEqs_3741_; lean_object* v_elimStack_3742_; lean_object* v_occurs_3743_; lean_object* v_ignored_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3758_; 
v_v_3701_ = lean_array_fget(v_structs_3688_, v_a_3684_);
v_id_3702_ = lean_ctor_get(v_v_3701_, 0);
v_ringId_x3f_3703_ = lean_ctor_get(v_v_3701_, 1);
v_type_3704_ = lean_ctor_get(v_v_3701_, 2);
v_u_3705_ = lean_ctor_get(v_v_3701_, 3);
v_intModuleInst_3706_ = lean_ctor_get(v_v_3701_, 4);
v_leInst_x3f_3707_ = lean_ctor_get(v_v_3701_, 5);
v_ltInst_x3f_3708_ = lean_ctor_get(v_v_3701_, 6);
v_lawfulOrderLTInst_x3f_3709_ = lean_ctor_get(v_v_3701_, 7);
v_isPreorderInst_x3f_3710_ = lean_ctor_get(v_v_3701_, 8);
v_orderedAddInst_x3f_3711_ = lean_ctor_get(v_v_3701_, 9);
v_isLinearInst_x3f_3712_ = lean_ctor_get(v_v_3701_, 10);
v_noNatDivInst_x3f_3713_ = lean_ctor_get(v_v_3701_, 11);
v_ringInst_x3f_3714_ = lean_ctor_get(v_v_3701_, 12);
v_commRingInst_x3f_3715_ = lean_ctor_get(v_v_3701_, 13);
v_orderedRingInst_x3f_3716_ = lean_ctor_get(v_v_3701_, 14);
v_fieldInst_x3f_3717_ = lean_ctor_get(v_v_3701_, 15);
v_charInst_x3f_3718_ = lean_ctor_get(v_v_3701_, 16);
v_zero_3719_ = lean_ctor_get(v_v_3701_, 17);
v_ofNatZero_3720_ = lean_ctor_get(v_v_3701_, 18);
v_one_x3f_3721_ = lean_ctor_get(v_v_3701_, 19);
v_leFn_x3f_3722_ = lean_ctor_get(v_v_3701_, 20);
v_ltFn_x3f_3723_ = lean_ctor_get(v_v_3701_, 21);
v_addFn_3724_ = lean_ctor_get(v_v_3701_, 22);
v_zsmulFn_3725_ = lean_ctor_get(v_v_3701_, 23);
v_nsmulFn_3726_ = lean_ctor_get(v_v_3701_, 24);
v_zsmulFn_x3f_3727_ = lean_ctor_get(v_v_3701_, 25);
v_nsmulFn_x3f_3728_ = lean_ctor_get(v_v_3701_, 26);
v_homomulFn_x3f_3729_ = lean_ctor_get(v_v_3701_, 27);
v_subFn_3730_ = lean_ctor_get(v_v_3701_, 28);
v_negFn_3731_ = lean_ctor_get(v_v_3701_, 29);
v_vars_3732_ = lean_ctor_get(v_v_3701_, 30);
v_varMap_3733_ = lean_ctor_get(v_v_3701_, 31);
v_lowers_3734_ = lean_ctor_get(v_v_3701_, 32);
v_uppers_3735_ = lean_ctor_get(v_v_3701_, 33);
v_diseqs_3736_ = lean_ctor_get(v_v_3701_, 34);
v_assignment_3737_ = lean_ctor_get(v_v_3701_, 35);
v_caseSplits_3738_ = lean_ctor_get_uint8(v_v_3701_, sizeof(void*)*42);
v_conflict_x3f_3739_ = lean_ctor_get(v_v_3701_, 36);
v_diseqSplits_3740_ = lean_ctor_get(v_v_3701_, 37);
v_elimEqs_3741_ = lean_ctor_get(v_v_3701_, 38);
v_elimStack_3742_ = lean_ctor_get(v_v_3701_, 39);
v_occurs_3743_ = lean_ctor_get(v_v_3701_, 40);
v_ignored_3744_ = lean_ctor_get(v_v_3701_, 41);
v_isSharedCheck_3758_ = !lean_is_exclusive(v_v_3701_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3746_ = v_v_3701_;
v_isShared_3747_ = v_isSharedCheck_3758_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_ignored_3744_);
lean_inc(v_occurs_3743_);
lean_inc(v_elimStack_3742_);
lean_inc(v_elimEqs_3741_);
lean_inc(v_diseqSplits_3740_);
lean_inc(v_conflict_x3f_3739_);
lean_inc(v_assignment_3737_);
lean_inc(v_diseqs_3736_);
lean_inc(v_uppers_3735_);
lean_inc(v_lowers_3734_);
lean_inc(v_varMap_3733_);
lean_inc(v_vars_3732_);
lean_inc(v_negFn_3731_);
lean_inc(v_subFn_3730_);
lean_inc(v_homomulFn_x3f_3729_);
lean_inc(v_nsmulFn_x3f_3728_);
lean_inc(v_zsmulFn_x3f_3727_);
lean_inc(v_nsmulFn_3726_);
lean_inc(v_zsmulFn_3725_);
lean_inc(v_addFn_3724_);
lean_inc(v_ltFn_x3f_3723_);
lean_inc(v_leFn_x3f_3722_);
lean_inc(v_one_x3f_3721_);
lean_inc(v_ofNatZero_3720_);
lean_inc(v_zero_3719_);
lean_inc(v_charInst_x3f_3718_);
lean_inc(v_fieldInst_x3f_3717_);
lean_inc(v_orderedRingInst_x3f_3716_);
lean_inc(v_commRingInst_x3f_3715_);
lean_inc(v_ringInst_x3f_3714_);
lean_inc(v_noNatDivInst_x3f_3713_);
lean_inc(v_isLinearInst_x3f_3712_);
lean_inc(v_orderedAddInst_x3f_3711_);
lean_inc(v_isPreorderInst_x3f_3710_);
lean_inc(v_lawfulOrderLTInst_x3f_3709_);
lean_inc(v_ltInst_x3f_3708_);
lean_inc(v_leInst_x3f_3707_);
lean_inc(v_intModuleInst_3706_);
lean_inc(v_u_3705_);
lean_inc(v_type_3704_);
lean_inc(v_ringId_x3f_3703_);
lean_inc(v_id_3702_);
lean_dec(v_v_3701_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3758_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3748_; lean_object* v_xs_x27_3749_; lean_object* v___x_3750_; lean_object* v___x_3752_; 
v___x_3748_ = lean_box(0);
v_xs_x27_3749_ = lean_array_fset(v_structs_3688_, v_a_3684_, v___x_3748_);
v___x_3750_ = l_Lean_PersistentArray_set___redArg(v_diseqs_3736_, v_y_3685_, v_fst_3686_);
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 34, v___x_3750_);
v___x_3752_ = v___x_3746_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_id_3702_);
lean_ctor_set(v_reuseFailAlloc_3757_, 1, v_ringId_x3f_3703_);
lean_ctor_set(v_reuseFailAlloc_3757_, 2, v_type_3704_);
lean_ctor_set(v_reuseFailAlloc_3757_, 3, v_u_3705_);
lean_ctor_set(v_reuseFailAlloc_3757_, 4, v_intModuleInst_3706_);
lean_ctor_set(v_reuseFailAlloc_3757_, 5, v_leInst_x3f_3707_);
lean_ctor_set(v_reuseFailAlloc_3757_, 6, v_ltInst_x3f_3708_);
lean_ctor_set(v_reuseFailAlloc_3757_, 7, v_lawfulOrderLTInst_x3f_3709_);
lean_ctor_set(v_reuseFailAlloc_3757_, 8, v_isPreorderInst_x3f_3710_);
lean_ctor_set(v_reuseFailAlloc_3757_, 9, v_orderedAddInst_x3f_3711_);
lean_ctor_set(v_reuseFailAlloc_3757_, 10, v_isLinearInst_x3f_3712_);
lean_ctor_set(v_reuseFailAlloc_3757_, 11, v_noNatDivInst_x3f_3713_);
lean_ctor_set(v_reuseFailAlloc_3757_, 12, v_ringInst_x3f_3714_);
lean_ctor_set(v_reuseFailAlloc_3757_, 13, v_commRingInst_x3f_3715_);
lean_ctor_set(v_reuseFailAlloc_3757_, 14, v_orderedRingInst_x3f_3716_);
lean_ctor_set(v_reuseFailAlloc_3757_, 15, v_fieldInst_x3f_3717_);
lean_ctor_set(v_reuseFailAlloc_3757_, 16, v_charInst_x3f_3718_);
lean_ctor_set(v_reuseFailAlloc_3757_, 17, v_zero_3719_);
lean_ctor_set(v_reuseFailAlloc_3757_, 18, v_ofNatZero_3720_);
lean_ctor_set(v_reuseFailAlloc_3757_, 19, v_one_x3f_3721_);
lean_ctor_set(v_reuseFailAlloc_3757_, 20, v_leFn_x3f_3722_);
lean_ctor_set(v_reuseFailAlloc_3757_, 21, v_ltFn_x3f_3723_);
lean_ctor_set(v_reuseFailAlloc_3757_, 22, v_addFn_3724_);
lean_ctor_set(v_reuseFailAlloc_3757_, 23, v_zsmulFn_3725_);
lean_ctor_set(v_reuseFailAlloc_3757_, 24, v_nsmulFn_3726_);
lean_ctor_set(v_reuseFailAlloc_3757_, 25, v_zsmulFn_x3f_3727_);
lean_ctor_set(v_reuseFailAlloc_3757_, 26, v_nsmulFn_x3f_3728_);
lean_ctor_set(v_reuseFailAlloc_3757_, 27, v_homomulFn_x3f_3729_);
lean_ctor_set(v_reuseFailAlloc_3757_, 28, v_subFn_3730_);
lean_ctor_set(v_reuseFailAlloc_3757_, 29, v_negFn_3731_);
lean_ctor_set(v_reuseFailAlloc_3757_, 30, v_vars_3732_);
lean_ctor_set(v_reuseFailAlloc_3757_, 31, v_varMap_3733_);
lean_ctor_set(v_reuseFailAlloc_3757_, 32, v_lowers_3734_);
lean_ctor_set(v_reuseFailAlloc_3757_, 33, v_uppers_3735_);
lean_ctor_set(v_reuseFailAlloc_3757_, 34, v___x_3750_);
lean_ctor_set(v_reuseFailAlloc_3757_, 35, v_assignment_3737_);
lean_ctor_set(v_reuseFailAlloc_3757_, 36, v_conflict_x3f_3739_);
lean_ctor_set(v_reuseFailAlloc_3757_, 37, v_diseqSplits_3740_);
lean_ctor_set(v_reuseFailAlloc_3757_, 38, v_elimEqs_3741_);
lean_ctor_set(v_reuseFailAlloc_3757_, 39, v_elimStack_3742_);
lean_ctor_set(v_reuseFailAlloc_3757_, 40, v_occurs_3743_);
lean_ctor_set(v_reuseFailAlloc_3757_, 41, v_ignored_3744_);
lean_ctor_set_uint8(v_reuseFailAlloc_3757_, sizeof(void*)*42, v_caseSplits_3738_);
v___x_3752_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
lean_object* v___x_3753_; lean_object* v___x_3755_; 
v___x_3753_ = lean_array_fset(v_xs_x27_3749_, v_a_3684_, v___x_3752_);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 0, v___x_3753_);
v___x_3755_ = v___x_3699_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3753_);
lean_ctor_set(v_reuseFailAlloc_3756_, 1, v_typeIdOf_3689_);
lean_ctor_set(v_reuseFailAlloc_3756_, 2, v_exprToStructId_3690_);
lean_ctor_set(v_reuseFailAlloc_3756_, 3, v_exprToStructIdEntries_3691_);
lean_ctor_set(v_reuseFailAlloc_3756_, 4, v_forbiddenNatModules_3692_);
lean_ctor_set(v_reuseFailAlloc_3756_, 5, v_natStructs_3693_);
lean_ctor_set(v_reuseFailAlloc_3756_, 6, v_natTypeIdOf_3694_);
lean_ctor_set(v_reuseFailAlloc_3756_, 7, v_exprToNatStructId_3695_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed(lean_object* v_a_3768_, lean_object* v_y_3769_, lean_object* v_fst_3770_, lean_object* v_s_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(v_a_3768_, v_y_3769_, v_fst_3770_, v_s_3771_);
lean_dec(v_y_3769_);
lean_dec(v_a_3768_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object* v_a_3773_, lean_object* v_x_3774_, lean_object* v_c_3775_, lean_object* v_as_3776_, size_t v_sz_3777_, size_t v_i_3778_, lean_object* v_b_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
lean_object* v_a_3793_; uint8_t v___x_3797_; 
v___x_3797_ = lean_usize_dec_lt(v_i_3778_, v_sz_3777_);
if (v___x_3797_ == 0)
{
lean_object* v___x_3798_; 
lean_dec_ref(v_c_3775_);
v___x_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3798_, 0, v_b_3779_);
return v___x_3798_;
}
else
{
lean_object* v_a_3799_; lean_object* v_fst_3800_; lean_object* v_snd_3801_; lean_object* v___x_3802_; 
lean_dec_ref(v_b_3779_);
v_a_3799_ = lean_array_uget_borrowed(v_as_3776_, v_i_3778_);
v_fst_3800_ = lean_ctor_get(v_a_3799_, 0);
v_snd_3801_ = lean_ctor_get(v_a_3799_, 1);
lean_inc(v_snd_3801_);
lean_inc(v_fst_3800_);
lean_inc_ref(v_c_3775_);
v___x_3802_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_3773_, v_x_3774_, v_c_3775_, v_fst_3800_, v_snd_3801_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v___x_3804_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_a_3803_);
lean_dec_ref(v___x_3802_);
v___x_3804_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
if (lean_obj_tag(v_a_3803_) == 1)
{
lean_object* v_val_3805_; lean_object* v___x_3806_; 
v_val_3805_ = lean_ctor_get(v_a_3803_, 0);
lean_inc(v_val_3805_);
lean_dec_ref(v_a_3803_);
v___x_3806_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_val_3805_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v___x_3807_; 
lean_dec_ref(v___x_3806_);
v___x_3807_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3817_; 
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3810_ = v___x_3807_;
v_isShared_3811_ = v_isSharedCheck_3817_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3807_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3817_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
uint8_t v___x_3812_; 
v___x_3812_ = lean_unbox(v_a_3808_);
lean_dec(v_a_3808_);
if (v___x_3812_ == 0)
{
lean_del_object(v___x_3810_);
v_a_3793_ = v___x_3804_;
goto v___jp_3792_;
}
else
{
lean_object* v___x_3813_; lean_object* v___x_3815_; 
lean_dec_ref(v_c_3775_);
v___x_3813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 0, v___x_3813_);
v___x_3815_ = v___x_3810_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3813_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec_ref(v_c_3775_);
v_a_3818_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3807_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3807_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_dec_ref(v_c_3775_);
v_a_3826_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3806_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3806_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
else
{
lean_object* v___x_3834_; 
lean_dec(v_a_3803_);
v___x_3834_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_snd_3801_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_dec_ref(v___x_3834_);
v_a_3793_ = v___x_3804_;
goto v___jp_3792_;
}
else
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3842_; 
lean_dec_ref(v_c_3775_);
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3837_ = v___x_3834_;
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3834_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3840_; 
if (v_isShared_3838_ == 0)
{
v___x_3840_ = v___x_3837_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3835_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
lean_dec_ref(v_c_3775_);
v_a_3843_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___x_3802_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3802_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
}
v___jp_3792_:
{
size_t v___x_3794_; size_t v___x_3795_; 
v___x_3794_ = ((size_t)1ULL);
v___x_3795_ = lean_usize_add(v_i_3778_, v___x_3794_);
lean_inc_ref(v_a_3793_);
v_i_3778_ = v___x_3795_;
v_b_3779_ = v_a_3793_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object** _args){
lean_object* v_a_3851_ = _args[0];
lean_object* v_x_3852_ = _args[1];
lean_object* v_c_3853_ = _args[2];
lean_object* v_as_3854_ = _args[3];
lean_object* v_sz_3855_ = _args[4];
lean_object* v_i_3856_ = _args[5];
lean_object* v_b_3857_ = _args[6];
lean_object* v___y_3858_ = _args[7];
lean_object* v___y_3859_ = _args[8];
lean_object* v___y_3860_ = _args[9];
lean_object* v___y_3861_ = _args[10];
lean_object* v___y_3862_ = _args[11];
lean_object* v___y_3863_ = _args[12];
lean_object* v___y_3864_ = _args[13];
lean_object* v___y_3865_ = _args[14];
lean_object* v___y_3866_ = _args[15];
lean_object* v___y_3867_ = _args[16];
lean_object* v___y_3868_ = _args[17];
lean_object* v___y_3869_ = _args[18];
_start:
{
size_t v_sz_boxed_3870_; size_t v_i_boxed_3871_; lean_object* v_res_3872_; 
v_sz_boxed_3870_ = lean_unbox_usize(v_sz_3855_);
lean_dec(v_sz_3855_);
v_i_boxed_3871_ = lean_unbox_usize(v_i_3856_);
lean_dec(v_i_3856_);
v_res_3872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3851_, v_x_3852_, v_c_3853_, v_as_3854_, v_sz_boxed_3870_, v_i_boxed_3871_, v_b_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v_as_3854_);
lean_dec(v_x_3852_);
lean_dec(v_a_3851_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object* v_a_3873_, lean_object* v_x_3874_, lean_object* v_c_3875_, lean_object* v_y_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3949_; 
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3892_ = v___x_3889_;
v_isShared_3893_ = v_isSharedCheck_3949_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v___x_3889_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3949_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
uint8_t v___x_3894_; 
v___x_3894_ = lean_unbox(v_a_3890_);
lean_dec(v_a_3890_);
if (v___x_3894_ == 0)
{
lean_object* v___x_3895_; 
lean_del_object(v___x_3892_);
v___x_3895_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3896_; lean_object* v___y_3898_; lean_object* v_diseqs_3931_; lean_object* v_size_3932_; lean_object* v___x_3933_; uint8_t v___x_3934_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3896_);
lean_dec_ref(v___x_3895_);
v_diseqs_3931_ = lean_ctor_get(v_a_3896_, 34);
lean_inc_ref(v_diseqs_3931_);
lean_dec(v_a_3896_);
v_size_3932_ = lean_ctor_get(v_diseqs_3931_, 2);
v___x_3933_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_3934_ = lean_nat_dec_lt(v_y_3876_, v_size_3932_);
if (v___x_3934_ == 0)
{
lean_object* v___x_3935_; 
lean_dec_ref(v_diseqs_3931_);
v___x_3935_ = l_outOfBounds___redArg(v___x_3933_);
v___y_3898_ = v___x_3935_;
goto v___jp_3897_;
}
else
{
lean_object* v___x_3936_; 
v___x_3936_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3933_, v_diseqs_3931_, v_y_3876_);
lean_dec_ref(v_diseqs_3931_);
v___y_3898_ = v___x_3936_;
goto v___jp_3897_;
}
v___jp_3897_:
{
lean_object* v___x_3899_; lean_object* v_fst_3900_; lean_object* v_snd_3901_; lean_object* v___f_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3899_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3874_, v___y_3898_);
v_fst_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_fst_3900_);
v_snd_3901_ = lean_ctor_get(v___x_3899_, 1);
lean_inc(v_snd_3901_);
lean_dec_ref(v___x_3899_);
lean_inc(v_a_3877_);
v___f_3902_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3902_, 0, v_a_3877_);
lean_closure_set(v___f_3902_, 1, v_y_3876_);
lean_closure_set(v___f_3902_, 2, v_fst_3900_);
v___x_3903_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3904_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3903_, v___f_3902_, v_a_3878_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v___x_3905_; lean_object* v___x_3906_; size_t v_sz_3907_; size_t v___x_3908_; lean_object* v___x_3909_; 
lean_dec_ref(v___x_3904_);
v___x_3905_ = lean_box(0);
v___x_3906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_3907_ = lean_array_size(v_snd_3901_);
v___x_3908_ = ((size_t)0ULL);
v___x_3909_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3873_, v_x_3874_, v_c_3875_, v_snd_3901_, v_sz_3907_, v___x_3908_, v___x_3906_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_);
lean_dec(v_snd_3901_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3922_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3912_ = v___x_3909_;
v_isShared_3913_ = v_isSharedCheck_3922_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3909_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3922_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v_fst_3914_; 
v_fst_3914_ = lean_ctor_get(v_a_3910_, 0);
lean_inc(v_fst_3914_);
lean_dec(v_a_3910_);
if (lean_obj_tag(v_fst_3914_) == 0)
{
lean_object* v___x_3916_; 
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 0, v___x_3905_);
v___x_3916_ = v___x_3912_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3905_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
else
{
lean_object* v_val_3918_; lean_object* v___x_3920_; 
v_val_3918_ = lean_ctor_get(v_fst_3914_, 0);
lean_inc(v_val_3918_);
lean_dec_ref(v_fst_3914_);
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 0, v_val_3918_);
v___x_3920_ = v___x_3912_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_val_3918_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
v_a_3923_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3909_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3909_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
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
lean_dec(v_snd_3901_);
lean_dec_ref(v_c_3875_);
return v___x_3904_;
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_dec(v_y_3876_);
lean_dec_ref(v_c_3875_);
v_a_3937_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3895_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3895_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
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
lean_object* v___x_3945_; lean_object* v___x_3947_; 
lean_dec(v_y_3876_);
lean_dec_ref(v_c_3875_);
v___x_3945_ = lean_box(0);
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 0, v___x_3945_);
v___x_3947_ = v___x_3892_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3945_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
else
{
lean_object* v_a_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3957_; 
lean_dec(v_y_3876_);
lean_dec_ref(v_c_3875_);
v_a_3950_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3952_ = v___x_3889_;
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_a_3950_);
lean_dec(v___x_3889_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3955_; 
if (v_isShared_3953_ == 0)
{
v___x_3955_ = v___x_3952_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_a_3950_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object* v_a_3958_, lean_object* v_x_3959_, lean_object* v_c_3960_, lean_object* v_y_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v_a_3958_, v_x_3959_, v_c_3960_, v_y_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_);
lean_dec(v_a_3972_);
lean_dec_ref(v_a_3971_);
lean_dec(v_a_3970_);
lean_dec_ref(v_a_3969_);
lean_dec(v_a_3968_);
lean_dec_ref(v_a_3967_);
lean_dec(v_a_3966_);
lean_dec_ref(v_a_3965_);
lean_dec(v_a_3964_);
lean_dec(v_a_3963_);
lean_dec(v_a_3962_);
lean_dec(v_x_3959_);
lean_dec(v_a_3958_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object* v_a_3975_, lean_object* v_x_3976_, lean_object* v_c_3977_, lean_object* v_y_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v___x_3991_; 
lean_inc(v_y_3978_);
lean_inc_ref(v_c_3977_);
lean_inc(v_x_3976_);
lean_inc(v_a_3975_);
v___x_3991_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_3975_, v_x_3976_, v_c_3977_, v_y_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_object* v___x_3992_; 
lean_dec_ref(v___x_3991_);
lean_inc(v_y_3978_);
lean_inc_ref(v_c_3977_);
lean_inc(v_x_3976_);
lean_inc(v_a_3975_);
v___x_3992_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_3975_, v_x_3976_, v_c_3977_, v_y_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_);
if (lean_obj_tag(v___x_3992_) == 0)
{
lean_object* v___x_3993_; lean_object* v___x_3994_; 
lean_dec_ref(v___x_3992_);
v___x_3993_ = lean_nat_to_int(v_a_3975_);
v___x_3994_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v___x_3993_, v_x_3976_, v_c_3977_, v_y_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_);
lean_dec(v_x_3976_);
lean_dec(v___x_3993_);
return v___x_3994_;
}
else
{
lean_dec(v_y_3978_);
lean_dec_ref(v_c_3977_);
lean_dec(v_x_3976_);
lean_dec(v_a_3975_);
return v___x_3992_;
}
}
else
{
lean_dec(v_y_3978_);
lean_dec_ref(v_c_3977_);
lean_dec(v_x_3976_);
lean_dec(v_a_3975_);
return v___x_3991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object* v_a_3995_, lean_object* v_x_3996_, lean_object* v_c_3997_, lean_object* v_y_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_3995_, v_x_3996_, v_c_3997_, v_y_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
lean_dec(v_a_4009_);
lean_dec_ref(v_a_4008_);
lean_dec(v_a_4007_);
lean_dec_ref(v_a_4006_);
lean_dec(v_a_4005_);
lean_dec_ref(v_a_4004_);
lean_dec(v_a_4003_);
lean_dec_ref(v_a_4002_);
lean_dec(v_a_4001_);
lean_dec(v_a_4000_);
lean_dec(v_a_3999_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(lean_object* v_a_4012_, lean_object* v_x_4013_, lean_object* v_s_4014_){
_start:
{
lean_object* v_structs_4015_; lean_object* v_typeIdOf_4016_; lean_object* v_exprToStructId_4017_; lean_object* v_exprToStructIdEntries_4018_; lean_object* v_forbiddenNatModules_4019_; lean_object* v_natStructs_4020_; lean_object* v_natTypeIdOf_4021_; lean_object* v_exprToNatStructId_4022_; lean_object* v___x_4023_; uint8_t v___x_4024_; 
v_structs_4015_ = lean_ctor_get(v_s_4014_, 0);
v_typeIdOf_4016_ = lean_ctor_get(v_s_4014_, 1);
v_exprToStructId_4017_ = lean_ctor_get(v_s_4014_, 2);
v_exprToStructIdEntries_4018_ = lean_ctor_get(v_s_4014_, 3);
v_forbiddenNatModules_4019_ = lean_ctor_get(v_s_4014_, 4);
v_natStructs_4020_ = lean_ctor_get(v_s_4014_, 5);
v_natTypeIdOf_4021_ = lean_ctor_get(v_s_4014_, 6);
v_exprToNatStructId_4022_ = lean_ctor_get(v_s_4014_, 7);
v___x_4023_ = lean_array_get_size(v_structs_4015_);
v___x_4024_ = lean_nat_dec_lt(v_a_4012_, v___x_4023_);
if (v___x_4024_ == 0)
{
return v_s_4014_;
}
else
{
lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4087_; 
lean_inc_ref(v_exprToNatStructId_4022_);
lean_inc_ref(v_natTypeIdOf_4021_);
lean_inc_ref(v_natStructs_4020_);
lean_inc_ref(v_forbiddenNatModules_4019_);
lean_inc_ref(v_exprToStructIdEntries_4018_);
lean_inc_ref(v_exprToStructId_4017_);
lean_inc_ref(v_typeIdOf_4016_);
lean_inc_ref(v_structs_4015_);
v_isSharedCheck_4087_ = !lean_is_exclusive(v_s_4014_);
if (v_isSharedCheck_4087_ == 0)
{
lean_object* v_unused_4088_; lean_object* v_unused_4089_; lean_object* v_unused_4090_; lean_object* v_unused_4091_; lean_object* v_unused_4092_; lean_object* v_unused_4093_; lean_object* v_unused_4094_; lean_object* v_unused_4095_; 
v_unused_4088_ = lean_ctor_get(v_s_4014_, 7);
lean_dec(v_unused_4088_);
v_unused_4089_ = lean_ctor_get(v_s_4014_, 6);
lean_dec(v_unused_4089_);
v_unused_4090_ = lean_ctor_get(v_s_4014_, 5);
lean_dec(v_unused_4090_);
v_unused_4091_ = lean_ctor_get(v_s_4014_, 4);
lean_dec(v_unused_4091_);
v_unused_4092_ = lean_ctor_get(v_s_4014_, 3);
lean_dec(v_unused_4092_);
v_unused_4093_ = lean_ctor_get(v_s_4014_, 2);
lean_dec(v_unused_4093_);
v_unused_4094_ = lean_ctor_get(v_s_4014_, 1);
lean_dec(v_unused_4094_);
v_unused_4095_ = lean_ctor_get(v_s_4014_, 0);
lean_dec(v_unused_4095_);
v___x_4026_ = v_s_4014_;
v_isShared_4027_ = v_isSharedCheck_4087_;
goto v_resetjp_4025_;
}
else
{
lean_dec(v_s_4014_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4087_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v_v_4028_; lean_object* v_id_4029_; lean_object* v_ringId_x3f_4030_; lean_object* v_type_4031_; lean_object* v_u_4032_; lean_object* v_intModuleInst_4033_; lean_object* v_leInst_x3f_4034_; lean_object* v_ltInst_x3f_4035_; lean_object* v_lawfulOrderLTInst_x3f_4036_; lean_object* v_isPreorderInst_x3f_4037_; lean_object* v_orderedAddInst_x3f_4038_; lean_object* v_isLinearInst_x3f_4039_; lean_object* v_noNatDivInst_x3f_4040_; lean_object* v_ringInst_x3f_4041_; lean_object* v_commRingInst_x3f_4042_; lean_object* v_orderedRingInst_x3f_4043_; lean_object* v_fieldInst_x3f_4044_; lean_object* v_charInst_x3f_4045_; lean_object* v_zero_4046_; lean_object* v_ofNatZero_4047_; lean_object* v_one_x3f_4048_; lean_object* v_leFn_x3f_4049_; lean_object* v_ltFn_x3f_4050_; lean_object* v_addFn_4051_; lean_object* v_zsmulFn_4052_; lean_object* v_nsmulFn_4053_; lean_object* v_zsmulFn_x3f_4054_; lean_object* v_nsmulFn_x3f_4055_; lean_object* v_homomulFn_x3f_4056_; lean_object* v_subFn_4057_; lean_object* v_negFn_4058_; lean_object* v_vars_4059_; lean_object* v_varMap_4060_; lean_object* v_lowers_4061_; lean_object* v_uppers_4062_; lean_object* v_diseqs_4063_; lean_object* v_assignment_4064_; uint8_t v_caseSplits_4065_; lean_object* v_conflict_x3f_4066_; lean_object* v_diseqSplits_4067_; lean_object* v_elimEqs_4068_; lean_object* v_elimStack_4069_; lean_object* v_occurs_4070_; lean_object* v_ignored_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4086_; 
v_v_4028_ = lean_array_fget(v_structs_4015_, v_a_4012_);
v_id_4029_ = lean_ctor_get(v_v_4028_, 0);
v_ringId_x3f_4030_ = lean_ctor_get(v_v_4028_, 1);
v_type_4031_ = lean_ctor_get(v_v_4028_, 2);
v_u_4032_ = lean_ctor_get(v_v_4028_, 3);
v_intModuleInst_4033_ = lean_ctor_get(v_v_4028_, 4);
v_leInst_x3f_4034_ = lean_ctor_get(v_v_4028_, 5);
v_ltInst_x3f_4035_ = lean_ctor_get(v_v_4028_, 6);
v_lawfulOrderLTInst_x3f_4036_ = lean_ctor_get(v_v_4028_, 7);
v_isPreorderInst_x3f_4037_ = lean_ctor_get(v_v_4028_, 8);
v_orderedAddInst_x3f_4038_ = lean_ctor_get(v_v_4028_, 9);
v_isLinearInst_x3f_4039_ = lean_ctor_get(v_v_4028_, 10);
v_noNatDivInst_x3f_4040_ = lean_ctor_get(v_v_4028_, 11);
v_ringInst_x3f_4041_ = lean_ctor_get(v_v_4028_, 12);
v_commRingInst_x3f_4042_ = lean_ctor_get(v_v_4028_, 13);
v_orderedRingInst_x3f_4043_ = lean_ctor_get(v_v_4028_, 14);
v_fieldInst_x3f_4044_ = lean_ctor_get(v_v_4028_, 15);
v_charInst_x3f_4045_ = lean_ctor_get(v_v_4028_, 16);
v_zero_4046_ = lean_ctor_get(v_v_4028_, 17);
v_ofNatZero_4047_ = lean_ctor_get(v_v_4028_, 18);
v_one_x3f_4048_ = lean_ctor_get(v_v_4028_, 19);
v_leFn_x3f_4049_ = lean_ctor_get(v_v_4028_, 20);
v_ltFn_x3f_4050_ = lean_ctor_get(v_v_4028_, 21);
v_addFn_4051_ = lean_ctor_get(v_v_4028_, 22);
v_zsmulFn_4052_ = lean_ctor_get(v_v_4028_, 23);
v_nsmulFn_4053_ = lean_ctor_get(v_v_4028_, 24);
v_zsmulFn_x3f_4054_ = lean_ctor_get(v_v_4028_, 25);
v_nsmulFn_x3f_4055_ = lean_ctor_get(v_v_4028_, 26);
v_homomulFn_x3f_4056_ = lean_ctor_get(v_v_4028_, 27);
v_subFn_4057_ = lean_ctor_get(v_v_4028_, 28);
v_negFn_4058_ = lean_ctor_get(v_v_4028_, 29);
v_vars_4059_ = lean_ctor_get(v_v_4028_, 30);
v_varMap_4060_ = lean_ctor_get(v_v_4028_, 31);
v_lowers_4061_ = lean_ctor_get(v_v_4028_, 32);
v_uppers_4062_ = lean_ctor_get(v_v_4028_, 33);
v_diseqs_4063_ = lean_ctor_get(v_v_4028_, 34);
v_assignment_4064_ = lean_ctor_get(v_v_4028_, 35);
v_caseSplits_4065_ = lean_ctor_get_uint8(v_v_4028_, sizeof(void*)*42);
v_conflict_x3f_4066_ = lean_ctor_get(v_v_4028_, 36);
v_diseqSplits_4067_ = lean_ctor_get(v_v_4028_, 37);
v_elimEqs_4068_ = lean_ctor_get(v_v_4028_, 38);
v_elimStack_4069_ = lean_ctor_get(v_v_4028_, 39);
v_occurs_4070_ = lean_ctor_get(v_v_4028_, 40);
v_ignored_4071_ = lean_ctor_get(v_v_4028_, 41);
v_isSharedCheck_4086_ = !lean_is_exclusive(v_v_4028_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4073_ = v_v_4028_;
v_isShared_4074_ = v_isSharedCheck_4086_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_ignored_4071_);
lean_inc(v_occurs_4070_);
lean_inc(v_elimStack_4069_);
lean_inc(v_elimEqs_4068_);
lean_inc(v_diseqSplits_4067_);
lean_inc(v_conflict_x3f_4066_);
lean_inc(v_assignment_4064_);
lean_inc(v_diseqs_4063_);
lean_inc(v_uppers_4062_);
lean_inc(v_lowers_4061_);
lean_inc(v_varMap_4060_);
lean_inc(v_vars_4059_);
lean_inc(v_negFn_4058_);
lean_inc(v_subFn_4057_);
lean_inc(v_homomulFn_x3f_4056_);
lean_inc(v_nsmulFn_x3f_4055_);
lean_inc(v_zsmulFn_x3f_4054_);
lean_inc(v_nsmulFn_4053_);
lean_inc(v_zsmulFn_4052_);
lean_inc(v_addFn_4051_);
lean_inc(v_ltFn_x3f_4050_);
lean_inc(v_leFn_x3f_4049_);
lean_inc(v_one_x3f_4048_);
lean_inc(v_ofNatZero_4047_);
lean_inc(v_zero_4046_);
lean_inc(v_charInst_x3f_4045_);
lean_inc(v_fieldInst_x3f_4044_);
lean_inc(v_orderedRingInst_x3f_4043_);
lean_inc(v_commRingInst_x3f_4042_);
lean_inc(v_ringInst_x3f_4041_);
lean_inc(v_noNatDivInst_x3f_4040_);
lean_inc(v_isLinearInst_x3f_4039_);
lean_inc(v_orderedAddInst_x3f_4038_);
lean_inc(v_isPreorderInst_x3f_4037_);
lean_inc(v_lawfulOrderLTInst_x3f_4036_);
lean_inc(v_ltInst_x3f_4035_);
lean_inc(v_leInst_x3f_4034_);
lean_inc(v_intModuleInst_4033_);
lean_inc(v_u_4032_);
lean_inc(v_type_4031_);
lean_inc(v_ringId_x3f_4030_);
lean_inc(v_id_4029_);
lean_dec(v_v_4028_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4086_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4075_; lean_object* v_xs_x27_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4080_; 
v___x_4075_ = lean_box(0);
v_xs_x27_4076_ = lean_array_fset(v_structs_4015_, v_a_4012_, v___x_4075_);
v___x_4077_ = lean_box(1);
v___x_4078_ = l_Lean_PersistentArray_set___redArg(v_occurs_4070_, v_x_4013_, v___x_4077_);
if (v_isShared_4074_ == 0)
{
lean_ctor_set(v___x_4073_, 40, v___x_4078_);
v___x_4080_ = v___x_4073_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_id_4029_);
lean_ctor_set(v_reuseFailAlloc_4085_, 1, v_ringId_x3f_4030_);
lean_ctor_set(v_reuseFailAlloc_4085_, 2, v_type_4031_);
lean_ctor_set(v_reuseFailAlloc_4085_, 3, v_u_4032_);
lean_ctor_set(v_reuseFailAlloc_4085_, 4, v_intModuleInst_4033_);
lean_ctor_set(v_reuseFailAlloc_4085_, 5, v_leInst_x3f_4034_);
lean_ctor_set(v_reuseFailAlloc_4085_, 6, v_ltInst_x3f_4035_);
lean_ctor_set(v_reuseFailAlloc_4085_, 7, v_lawfulOrderLTInst_x3f_4036_);
lean_ctor_set(v_reuseFailAlloc_4085_, 8, v_isPreorderInst_x3f_4037_);
lean_ctor_set(v_reuseFailAlloc_4085_, 9, v_orderedAddInst_x3f_4038_);
lean_ctor_set(v_reuseFailAlloc_4085_, 10, v_isLinearInst_x3f_4039_);
lean_ctor_set(v_reuseFailAlloc_4085_, 11, v_noNatDivInst_x3f_4040_);
lean_ctor_set(v_reuseFailAlloc_4085_, 12, v_ringInst_x3f_4041_);
lean_ctor_set(v_reuseFailAlloc_4085_, 13, v_commRingInst_x3f_4042_);
lean_ctor_set(v_reuseFailAlloc_4085_, 14, v_orderedRingInst_x3f_4043_);
lean_ctor_set(v_reuseFailAlloc_4085_, 15, v_fieldInst_x3f_4044_);
lean_ctor_set(v_reuseFailAlloc_4085_, 16, v_charInst_x3f_4045_);
lean_ctor_set(v_reuseFailAlloc_4085_, 17, v_zero_4046_);
lean_ctor_set(v_reuseFailAlloc_4085_, 18, v_ofNatZero_4047_);
lean_ctor_set(v_reuseFailAlloc_4085_, 19, v_one_x3f_4048_);
lean_ctor_set(v_reuseFailAlloc_4085_, 20, v_leFn_x3f_4049_);
lean_ctor_set(v_reuseFailAlloc_4085_, 21, v_ltFn_x3f_4050_);
lean_ctor_set(v_reuseFailAlloc_4085_, 22, v_addFn_4051_);
lean_ctor_set(v_reuseFailAlloc_4085_, 23, v_zsmulFn_4052_);
lean_ctor_set(v_reuseFailAlloc_4085_, 24, v_nsmulFn_4053_);
lean_ctor_set(v_reuseFailAlloc_4085_, 25, v_zsmulFn_x3f_4054_);
lean_ctor_set(v_reuseFailAlloc_4085_, 26, v_nsmulFn_x3f_4055_);
lean_ctor_set(v_reuseFailAlloc_4085_, 27, v_homomulFn_x3f_4056_);
lean_ctor_set(v_reuseFailAlloc_4085_, 28, v_subFn_4057_);
lean_ctor_set(v_reuseFailAlloc_4085_, 29, v_negFn_4058_);
lean_ctor_set(v_reuseFailAlloc_4085_, 30, v_vars_4059_);
lean_ctor_set(v_reuseFailAlloc_4085_, 31, v_varMap_4060_);
lean_ctor_set(v_reuseFailAlloc_4085_, 32, v_lowers_4061_);
lean_ctor_set(v_reuseFailAlloc_4085_, 33, v_uppers_4062_);
lean_ctor_set(v_reuseFailAlloc_4085_, 34, v_diseqs_4063_);
lean_ctor_set(v_reuseFailAlloc_4085_, 35, v_assignment_4064_);
lean_ctor_set(v_reuseFailAlloc_4085_, 36, v_conflict_x3f_4066_);
lean_ctor_set(v_reuseFailAlloc_4085_, 37, v_diseqSplits_4067_);
lean_ctor_set(v_reuseFailAlloc_4085_, 38, v_elimEqs_4068_);
lean_ctor_set(v_reuseFailAlloc_4085_, 39, v_elimStack_4069_);
lean_ctor_set(v_reuseFailAlloc_4085_, 40, v___x_4078_);
lean_ctor_set(v_reuseFailAlloc_4085_, 41, v_ignored_4071_);
lean_ctor_set_uint8(v_reuseFailAlloc_4085_, sizeof(void*)*42, v_caseSplits_4065_);
v___x_4080_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
lean_object* v___x_4081_; lean_object* v___x_4083_; 
v___x_4081_ = lean_array_fset(v_xs_x27_4076_, v_a_4012_, v___x_4080_);
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 0, v___x_4081_);
v___x_4083_ = v___x_4026_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v___x_4081_);
lean_ctor_set(v_reuseFailAlloc_4084_, 1, v_typeIdOf_4016_);
lean_ctor_set(v_reuseFailAlloc_4084_, 2, v_exprToStructId_4017_);
lean_ctor_set(v_reuseFailAlloc_4084_, 3, v_exprToStructIdEntries_4018_);
lean_ctor_set(v_reuseFailAlloc_4084_, 4, v_forbiddenNatModules_4019_);
lean_ctor_set(v_reuseFailAlloc_4084_, 5, v_natStructs_4020_);
lean_ctor_set(v_reuseFailAlloc_4084_, 6, v_natTypeIdOf_4021_);
lean_ctor_set(v_reuseFailAlloc_4084_, 7, v_exprToNatStructId_4022_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed(lean_object* v_a_4096_, lean_object* v_x_4097_, lean_object* v_s_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(v_a_4096_, v_x_4097_, v_s_4098_);
lean_dec(v_x_4097_);
lean_dec(v_a_4096_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object* v_a_4100_, lean_object* v_x_4101_, lean_object* v_c_4102_, lean_object* v_init_4103_, lean_object* v_x_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
if (lean_obj_tag(v_x_4104_) == 0)
{
lean_object* v_k_4117_; lean_object* v_l_4118_; lean_object* v_r_4119_; lean_object* v___x_4120_; 
v_k_4117_ = lean_ctor_get(v_x_4104_, 1);
lean_inc(v_k_4117_);
v_l_4118_ = lean_ctor_get(v_x_4104_, 3);
lean_inc(v_l_4118_);
v_r_4119_ = lean_ctor_get(v_x_4104_, 4);
lean_inc(v_r_4119_);
lean_dec_ref(v_x_4104_);
lean_inc_ref(v_c_4102_);
lean_inc(v_x_4101_);
lean_inc(v_a_4100_);
v___x_4120_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4100_, v_x_4101_, v_c_4102_, v_init_4103_, v_l_4118_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_object* v___x_4121_; 
lean_dec_ref(v___x_4120_);
lean_inc_ref(v_c_4102_);
lean_inc(v_x_4101_);
lean_inc(v_a_4100_);
v___x_4121_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4100_, v_x_4101_, v_c_4102_, v_k_4117_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4121_) == 0)
{
lean_object* v___x_4122_; 
lean_dec_ref(v___x_4121_);
v___x_4122_ = lean_box(0);
v_init_4103_ = v___x_4122_;
v_x_4104_ = v_r_4119_;
goto _start;
}
else
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
lean_dec(v_r_4119_);
lean_dec_ref(v_c_4102_);
lean_dec(v_x_4101_);
lean_dec(v_a_4100_);
v_a_4124_ = lean_ctor_get(v___x_4121_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4121_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4126_ = v___x_4121_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4121_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
else
{
lean_dec(v_r_4119_);
lean_dec(v_k_4117_);
lean_dec_ref(v_c_4102_);
lean_dec(v_x_4101_);
lean_dec(v_a_4100_);
return v___x_4120_;
}
}
else
{
lean_object* v___x_4132_; lean_object* v___x_4133_; 
lean_dec_ref(v_c_4102_);
lean_dec(v_x_4101_);
lean_dec(v_a_4100_);
v___x_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4132_, 0, v_init_4103_);
v___x_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4133_, 0, v___x_4132_);
return v___x_4133_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object** _args){
lean_object* v_a_4134_ = _args[0];
lean_object* v_x_4135_ = _args[1];
lean_object* v_c_4136_ = _args[2];
lean_object* v_init_4137_ = _args[3];
lean_object* v_x_4138_ = _args[4];
lean_object* v___y_4139_ = _args[5];
lean_object* v___y_4140_ = _args[6];
lean_object* v___y_4141_ = _args[7];
lean_object* v___y_4142_ = _args[8];
lean_object* v___y_4143_ = _args[9];
lean_object* v___y_4144_ = _args[10];
lean_object* v___y_4145_ = _args[11];
lean_object* v___y_4146_ = _args[12];
lean_object* v___y_4147_ = _args[13];
lean_object* v___y_4148_ = _args[14];
lean_object* v___y_4149_ = _args[15];
lean_object* v___y_4150_ = _args[16];
_start:
{
lean_object* v_res_4151_; 
v_res_4151_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4134_, v_x_4135_, v_c_4136_, v_init_4137_, v_x_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec(v___y_4140_);
lean_dec(v___y_4139_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object* v_a_4152_, lean_object* v_x_4153_, lean_object* v_c_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_){
_start:
{
lean_object* v___x_4167_; 
v___x_4167_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_object* v_a_4168_; lean_object* v_occurs_4169_; lean_object* v_size_4170_; lean_object* v___f_4171_; lean_object* v___y_4173_; lean_object* v___x_4195_; uint8_t v___x_4196_; 
v_a_4168_ = lean_ctor_get(v___x_4167_, 0);
lean_inc(v_a_4168_);
lean_dec_ref(v___x_4167_);
v_occurs_4169_ = lean_ctor_get(v_a_4168_, 40);
lean_inc_ref(v_occurs_4169_);
lean_dec(v_a_4168_);
v_size_4170_ = lean_ctor_get(v_occurs_4169_, 2);
lean_inc(v_x_4153_);
lean_inc(v_a_4155_);
v___f_4171_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4171_, 0, v_a_4155_);
lean_closure_set(v___f_4171_, 1, v_x_4153_);
v___x_4195_ = lean_box(1);
v___x_4196_ = lean_nat_dec_lt(v_x_4153_, v_size_4170_);
if (v___x_4196_ == 0)
{
lean_object* v___x_4197_; 
lean_dec_ref(v_occurs_4169_);
v___x_4197_ = l_outOfBounds___redArg(v___x_4195_);
v___y_4173_ = v___x_4197_;
goto v___jp_4172_;
}
else
{
lean_object* v___x_4198_; 
v___x_4198_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4195_, v_occurs_4169_, v_x_4153_);
lean_dec_ref(v_occurs_4169_);
v___y_4173_ = v___x_4198_;
goto v___jp_4172_;
}
v___jp_4172_:
{
lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4174_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4175_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4174_, v___f_4171_, v_a_4156_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v___x_4176_; 
lean_dec_ref(v___x_4175_);
lean_inc_ref(v_c_4154_);
lean_inc_n(v_x_4153_, 2);
lean_inc(v_a_4152_);
v___x_4176_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4152_, v_x_4153_, v_c_4154_, v_x_4153_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_object* v___x_4177_; lean_object* v___x_4178_; 
lean_dec_ref(v___x_4176_);
v___x_4177_ = lean_box(0);
v___x_4178_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4152_, v_x_4153_, v_c_4154_, v___x_4177_, v___y_4173_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4185_; 
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4178_);
if (v_isSharedCheck_4185_ == 0)
{
lean_object* v_unused_4186_; 
v_unused_4186_ = lean_ctor_get(v___x_4178_, 0);
lean_dec(v_unused_4186_);
v___x_4180_ = v___x_4178_;
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
else
{
lean_dec(v___x_4178_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v___x_4183_; 
if (v_isShared_4181_ == 0)
{
lean_ctor_set(v___x_4180_, 0, v___x_4177_);
v___x_4183_ = v___x_4180_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___x_4177_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
}
}
}
else
{
lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4194_; 
v_a_4187_ = lean_ctor_get(v___x_4178_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v___x_4178_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4189_ = v___x_4178_;
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4178_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
lean_object* v___x_4192_; 
if (v_isShared_4190_ == 0)
{
v___x_4192_ = v___x_4189_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4187_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
}
else
{
lean_dec(v___y_4173_);
lean_dec_ref(v_c_4154_);
lean_dec(v_x_4153_);
lean_dec(v_a_4152_);
return v___x_4176_;
}
}
else
{
lean_dec(v___y_4173_);
lean_dec_ref(v_c_4154_);
lean_dec(v_x_4153_);
lean_dec(v_a_4152_);
return v___x_4175_;
}
}
}
else
{
lean_object* v_a_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4206_; 
lean_dec_ref(v_c_4154_);
lean_dec(v_x_4153_);
lean_dec(v_a_4152_);
v_a_4199_ = lean_ctor_get(v___x_4167_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4201_ = v___x_4167_;
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_a_4199_);
lean_dec(v___x_4167_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4204_; 
if (v_isShared_4202_ == 0)
{
v___x_4204_ = v___x_4201_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_a_4199_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___boxed(lean_object* v_a_4207_, lean_object* v_x_4208_, lean_object* v_c_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v_a_4207_, v_x_4208_, v_c_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
lean_dec(v_a_4220_);
lean_dec_ref(v_a_4219_);
lean_dec(v_a_4218_);
lean_dec_ref(v_a_4217_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec(v_a_4211_);
lean_dec(v_a_4210_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(lean_object* v_c_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_){
_start:
{
lean_object* v_p_4240_; 
v_p_4240_ = lean_ctor_get(v_c_4223_, 0);
if (lean_obj_tag(v_p_4240_) == 1)
{
lean_object* v_k_4241_; lean_object* v_v_4242_; lean_object* v_p_4243_; lean_object* v_y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___x_4294_; lean_object* v___x_4295_; uint8_t v___x_4296_; 
v_k_4241_ = lean_ctor_get(v_p_4240_, 0);
v_v_4242_ = lean_ctor_get(v_p_4240_, 1);
v_p_4243_ = lean_ctor_get(v_p_4240_, 2);
v___x_4294_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_4295_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4296_ = lean_int_dec_eq(v_k_4241_, v___x_4295_);
if (v___x_4296_ == 0)
{
uint8_t v___x_4297_; 
v___x_4297_ = lean_int_dec_eq(v_k_4241_, v___x_4294_);
if (v___x_4297_ == 0)
{
goto v___jp_4236_;
}
else
{
if (lean_obj_tag(v_p_4243_) == 1)
{
lean_object* v_k_4298_; lean_object* v_v_4299_; lean_object* v_p_4300_; uint8_t v___x_4301_; 
v_k_4298_ = lean_ctor_get(v_p_4243_, 0);
v_v_4299_ = lean_ctor_get(v_p_4243_, 1);
v_p_4300_ = lean_ctor_get(v_p_4243_, 2);
v___x_4301_ = lean_int_dec_eq(v_k_4298_, v___x_4295_);
if (v___x_4301_ == 0)
{
goto v___jp_4236_;
}
else
{
if (lean_obj_tag(v_p_4300_) == 0)
{
v_y_4245_ = v_v_4299_;
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
v___y_4256_ = v_a_4234_;
goto v___jp_4244_;
}
else
{
goto v___jp_4236_;
}
}
}
else
{
goto v___jp_4236_;
}
}
}
else
{
if (lean_obj_tag(v_p_4243_) == 1)
{
lean_object* v_k_4302_; lean_object* v_v_4303_; lean_object* v_p_4304_; uint8_t v___x_4305_; 
v_k_4302_ = lean_ctor_get(v_p_4243_, 0);
v_v_4303_ = lean_ctor_get(v_p_4243_, 1);
v_p_4304_ = lean_ctor_get(v_p_4243_, 2);
v___x_4305_ = lean_int_dec_eq(v_k_4302_, v___x_4294_);
if (v___x_4305_ == 0)
{
goto v___jp_4236_;
}
else
{
if (lean_obj_tag(v_p_4304_) == 0)
{
v_y_4245_ = v_v_4303_;
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
v___y_4256_ = v_a_4234_;
goto v___jp_4244_;
}
else
{
goto v___jp_4236_;
}
}
}
else
{
goto v___jp_4236_;
}
}
v___jp_4244_:
{
lean_object* v___x_4257_; 
v___x_4257_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_v_4242_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_a_4258_; lean_object* v___x_4259_; 
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
lean_inc(v_a_4258_);
lean_dec_ref(v___x_4257_);
v___x_4259_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; lean_object* v___x_4261_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
lean_inc(v_a_4260_);
lean_dec_ref(v___x_4259_);
v___x_4261_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_4258_, v_a_4260_, v___y_4247_);
lean_dec(v_a_4260_);
lean_dec(v_a_4258_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v_a_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4277_; 
v_a_4262_ = lean_ctor_get(v___x_4261_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4261_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4264_ = v___x_4261_;
v_isShared_4265_ = v_isSharedCheck_4277_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_a_4262_);
lean_dec(v___x_4261_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4277_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
uint8_t v___x_4266_; 
v___x_4266_ = lean_unbox(v_a_4262_);
lean_dec(v_a_4262_);
if (v___x_4266_ == 0)
{
uint8_t v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4270_; 
v___x_4267_ = 1;
v___x_4268_ = lean_box(v___x_4267_);
if (v_isShared_4265_ == 0)
{
lean_ctor_set(v___x_4264_, 0, v___x_4268_);
v___x_4270_ = v___x_4264_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v___x_4268_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
else
{
uint8_t v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4275_; 
v___x_4272_ = 0;
v___x_4273_ = lean_box(v___x_4272_);
if (v_isShared_4265_ == 0)
{
lean_ctor_set(v___x_4264_, 0, v___x_4273_);
v___x_4275_ = v___x_4264_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v___x_4273_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
}
}
else
{
return v___x_4261_;
}
}
else
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
lean_dec(v_a_4258_);
v_a_4278_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4280_ = v___x_4259_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___x_4259_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4283_; 
if (v_isShared_4281_ == 0)
{
v___x_4283_ = v___x_4280_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_a_4278_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
}
}
else
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4293_; 
v_a_4286_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4293_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4288_ = v___x_4257_;
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v___x_4257_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4291_; 
if (v_isShared_4289_ == 0)
{
v___x_4291_ = v___x_4288_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_a_4286_);
v___x_4291_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
return v___x_4291_;
}
}
}
}
}
else
{
goto v___jp_4236_;
}
v___jp_4236_:
{
uint8_t v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; 
v___x_4237_ = 0;
v___x_4238_ = lean_box(v___x_4237_);
v___x_4239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4238_);
return v___x_4239_;
}
}
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(lean_object* v_c_4320_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg___boxed(lean_object* v_c_4333_, lean_object* v_a_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4333_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(lean_object* v_c_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_){
_start:
{
lean_object* v___x_4349_; 
v___x_4349_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4336_);
return v___x_4349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___boxed(lean_object* v_c_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(v_c_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_);
lean_dec(v_a_4361_);
lean_dec_ref(v_a_4360_);
lean_dec(v_a_4359_);
lean_dec_ref(v_a_4358_);
lean_dec(v_a_4357_);
lean_dec_ref(v_a_4356_);
lean_dec(v_a_4355_);
lean_dec_ref(v_a_4354_);
lean_dec(v_a_4353_);
lean_dec(v_a_4352_);
lean_dec(v_a_4351_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(lean_object* v___y_4364_, lean_object* v_snd_4365_, lean_object* v_fst_4366_, lean_object* v_s_4367_){
_start:
{
lean_object* v_structs_4368_; lean_object* v_typeIdOf_4369_; lean_object* v_exprToStructId_4370_; lean_object* v_exprToStructIdEntries_4371_; lean_object* v_forbiddenNatModules_4372_; lean_object* v_natStructs_4373_; lean_object* v_natTypeIdOf_4374_; lean_object* v_exprToNatStructId_4375_; lean_object* v___x_4376_; uint8_t v___x_4377_; 
v_structs_4368_ = lean_ctor_get(v_s_4367_, 0);
v_typeIdOf_4369_ = lean_ctor_get(v_s_4367_, 1);
v_exprToStructId_4370_ = lean_ctor_get(v_s_4367_, 2);
v_exprToStructIdEntries_4371_ = lean_ctor_get(v_s_4367_, 3);
v_forbiddenNatModules_4372_ = lean_ctor_get(v_s_4367_, 4);
v_natStructs_4373_ = lean_ctor_get(v_s_4367_, 5);
v_natTypeIdOf_4374_ = lean_ctor_get(v_s_4367_, 6);
v_exprToNatStructId_4375_ = lean_ctor_get(v_s_4367_, 7);
v___x_4376_ = lean_array_get_size(v_structs_4368_);
v___x_4377_ = lean_nat_dec_lt(v___y_4364_, v___x_4376_);
if (v___x_4377_ == 0)
{
lean_dec(v_fst_4366_);
lean_dec_ref(v_snd_4365_);
return v_s_4367_;
}
else
{
lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4441_; 
lean_inc_ref(v_exprToNatStructId_4375_);
lean_inc_ref(v_natTypeIdOf_4374_);
lean_inc_ref(v_natStructs_4373_);
lean_inc_ref(v_forbiddenNatModules_4372_);
lean_inc_ref(v_exprToStructIdEntries_4371_);
lean_inc_ref(v_exprToStructId_4370_);
lean_inc_ref(v_typeIdOf_4369_);
lean_inc_ref(v_structs_4368_);
v_isSharedCheck_4441_ = !lean_is_exclusive(v_s_4367_);
if (v_isSharedCheck_4441_ == 0)
{
lean_object* v_unused_4442_; lean_object* v_unused_4443_; lean_object* v_unused_4444_; lean_object* v_unused_4445_; lean_object* v_unused_4446_; lean_object* v_unused_4447_; lean_object* v_unused_4448_; lean_object* v_unused_4449_; 
v_unused_4442_ = lean_ctor_get(v_s_4367_, 7);
lean_dec(v_unused_4442_);
v_unused_4443_ = lean_ctor_get(v_s_4367_, 6);
lean_dec(v_unused_4443_);
v_unused_4444_ = lean_ctor_get(v_s_4367_, 5);
lean_dec(v_unused_4444_);
v_unused_4445_ = lean_ctor_get(v_s_4367_, 4);
lean_dec(v_unused_4445_);
v_unused_4446_ = lean_ctor_get(v_s_4367_, 3);
lean_dec(v_unused_4446_);
v_unused_4447_ = lean_ctor_get(v_s_4367_, 2);
lean_dec(v_unused_4447_);
v_unused_4448_ = lean_ctor_get(v_s_4367_, 1);
lean_dec(v_unused_4448_);
v_unused_4449_ = lean_ctor_get(v_s_4367_, 0);
lean_dec(v_unused_4449_);
v___x_4379_ = v_s_4367_;
v_isShared_4380_ = v_isSharedCheck_4441_;
goto v_resetjp_4378_;
}
else
{
lean_dec(v_s_4367_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4441_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v_v_4381_; lean_object* v_id_4382_; lean_object* v_ringId_x3f_4383_; lean_object* v_type_4384_; lean_object* v_u_4385_; lean_object* v_intModuleInst_4386_; lean_object* v_leInst_x3f_4387_; lean_object* v_ltInst_x3f_4388_; lean_object* v_lawfulOrderLTInst_x3f_4389_; lean_object* v_isPreorderInst_x3f_4390_; lean_object* v_orderedAddInst_x3f_4391_; lean_object* v_isLinearInst_x3f_4392_; lean_object* v_noNatDivInst_x3f_4393_; lean_object* v_ringInst_x3f_4394_; lean_object* v_commRingInst_x3f_4395_; lean_object* v_orderedRingInst_x3f_4396_; lean_object* v_fieldInst_x3f_4397_; lean_object* v_charInst_x3f_4398_; lean_object* v_zero_4399_; lean_object* v_ofNatZero_4400_; lean_object* v_one_x3f_4401_; lean_object* v_leFn_x3f_4402_; lean_object* v_ltFn_x3f_4403_; lean_object* v_addFn_4404_; lean_object* v_zsmulFn_4405_; lean_object* v_nsmulFn_4406_; lean_object* v_zsmulFn_x3f_4407_; lean_object* v_nsmulFn_x3f_4408_; lean_object* v_homomulFn_x3f_4409_; lean_object* v_subFn_4410_; lean_object* v_negFn_4411_; lean_object* v_vars_4412_; lean_object* v_varMap_4413_; lean_object* v_lowers_4414_; lean_object* v_uppers_4415_; lean_object* v_diseqs_4416_; lean_object* v_assignment_4417_; uint8_t v_caseSplits_4418_; lean_object* v_conflict_x3f_4419_; lean_object* v_diseqSplits_4420_; lean_object* v_elimEqs_4421_; lean_object* v_elimStack_4422_; lean_object* v_occurs_4423_; lean_object* v_ignored_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4440_; 
v_v_4381_ = lean_array_fget(v_structs_4368_, v___y_4364_);
v_id_4382_ = lean_ctor_get(v_v_4381_, 0);
v_ringId_x3f_4383_ = lean_ctor_get(v_v_4381_, 1);
v_type_4384_ = lean_ctor_get(v_v_4381_, 2);
v_u_4385_ = lean_ctor_get(v_v_4381_, 3);
v_intModuleInst_4386_ = lean_ctor_get(v_v_4381_, 4);
v_leInst_x3f_4387_ = lean_ctor_get(v_v_4381_, 5);
v_ltInst_x3f_4388_ = lean_ctor_get(v_v_4381_, 6);
v_lawfulOrderLTInst_x3f_4389_ = lean_ctor_get(v_v_4381_, 7);
v_isPreorderInst_x3f_4390_ = lean_ctor_get(v_v_4381_, 8);
v_orderedAddInst_x3f_4391_ = lean_ctor_get(v_v_4381_, 9);
v_isLinearInst_x3f_4392_ = lean_ctor_get(v_v_4381_, 10);
v_noNatDivInst_x3f_4393_ = lean_ctor_get(v_v_4381_, 11);
v_ringInst_x3f_4394_ = lean_ctor_get(v_v_4381_, 12);
v_commRingInst_x3f_4395_ = lean_ctor_get(v_v_4381_, 13);
v_orderedRingInst_x3f_4396_ = lean_ctor_get(v_v_4381_, 14);
v_fieldInst_x3f_4397_ = lean_ctor_get(v_v_4381_, 15);
v_charInst_x3f_4398_ = lean_ctor_get(v_v_4381_, 16);
v_zero_4399_ = lean_ctor_get(v_v_4381_, 17);
v_ofNatZero_4400_ = lean_ctor_get(v_v_4381_, 18);
v_one_x3f_4401_ = lean_ctor_get(v_v_4381_, 19);
v_leFn_x3f_4402_ = lean_ctor_get(v_v_4381_, 20);
v_ltFn_x3f_4403_ = lean_ctor_get(v_v_4381_, 21);
v_addFn_4404_ = lean_ctor_get(v_v_4381_, 22);
v_zsmulFn_4405_ = lean_ctor_get(v_v_4381_, 23);
v_nsmulFn_4406_ = lean_ctor_get(v_v_4381_, 24);
v_zsmulFn_x3f_4407_ = lean_ctor_get(v_v_4381_, 25);
v_nsmulFn_x3f_4408_ = lean_ctor_get(v_v_4381_, 26);
v_homomulFn_x3f_4409_ = lean_ctor_get(v_v_4381_, 27);
v_subFn_4410_ = lean_ctor_get(v_v_4381_, 28);
v_negFn_4411_ = lean_ctor_get(v_v_4381_, 29);
v_vars_4412_ = lean_ctor_get(v_v_4381_, 30);
v_varMap_4413_ = lean_ctor_get(v_v_4381_, 31);
v_lowers_4414_ = lean_ctor_get(v_v_4381_, 32);
v_uppers_4415_ = lean_ctor_get(v_v_4381_, 33);
v_diseqs_4416_ = lean_ctor_get(v_v_4381_, 34);
v_assignment_4417_ = lean_ctor_get(v_v_4381_, 35);
v_caseSplits_4418_ = lean_ctor_get_uint8(v_v_4381_, sizeof(void*)*42);
v_conflict_x3f_4419_ = lean_ctor_get(v_v_4381_, 36);
v_diseqSplits_4420_ = lean_ctor_get(v_v_4381_, 37);
v_elimEqs_4421_ = lean_ctor_get(v_v_4381_, 38);
v_elimStack_4422_ = lean_ctor_get(v_v_4381_, 39);
v_occurs_4423_ = lean_ctor_get(v_v_4381_, 40);
v_ignored_4424_ = lean_ctor_get(v_v_4381_, 41);
v_isSharedCheck_4440_ = !lean_is_exclusive(v_v_4381_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4426_ = v_v_4381_;
v_isShared_4427_ = v_isSharedCheck_4440_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_ignored_4424_);
lean_inc(v_occurs_4423_);
lean_inc(v_elimStack_4422_);
lean_inc(v_elimEqs_4421_);
lean_inc(v_diseqSplits_4420_);
lean_inc(v_conflict_x3f_4419_);
lean_inc(v_assignment_4417_);
lean_inc(v_diseqs_4416_);
lean_inc(v_uppers_4415_);
lean_inc(v_lowers_4414_);
lean_inc(v_varMap_4413_);
lean_inc(v_vars_4412_);
lean_inc(v_negFn_4411_);
lean_inc(v_subFn_4410_);
lean_inc(v_homomulFn_x3f_4409_);
lean_inc(v_nsmulFn_x3f_4408_);
lean_inc(v_zsmulFn_x3f_4407_);
lean_inc(v_nsmulFn_4406_);
lean_inc(v_zsmulFn_4405_);
lean_inc(v_addFn_4404_);
lean_inc(v_ltFn_x3f_4403_);
lean_inc(v_leFn_x3f_4402_);
lean_inc(v_one_x3f_4401_);
lean_inc(v_ofNatZero_4400_);
lean_inc(v_zero_4399_);
lean_inc(v_charInst_x3f_4398_);
lean_inc(v_fieldInst_x3f_4397_);
lean_inc(v_orderedRingInst_x3f_4396_);
lean_inc(v_commRingInst_x3f_4395_);
lean_inc(v_ringInst_x3f_4394_);
lean_inc(v_noNatDivInst_x3f_4393_);
lean_inc(v_isLinearInst_x3f_4392_);
lean_inc(v_orderedAddInst_x3f_4391_);
lean_inc(v_isPreorderInst_x3f_4390_);
lean_inc(v_lawfulOrderLTInst_x3f_4389_);
lean_inc(v_ltInst_x3f_4388_);
lean_inc(v_leInst_x3f_4387_);
lean_inc(v_intModuleInst_4386_);
lean_inc(v_u_4385_);
lean_inc(v_type_4384_);
lean_inc(v_ringId_x3f_4383_);
lean_inc(v_id_4382_);
lean_dec(v_v_4381_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4440_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4428_; lean_object* v_xs_x27_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4434_; 
v___x_4428_ = lean_box(0);
v_xs_x27_4429_ = lean_array_fset(v_structs_4368_, v___y_4364_, v___x_4428_);
v___x_4430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4430_, 0, v_snd_4365_);
v___x_4431_ = l_Lean_PersistentArray_set___redArg(v_elimEqs_4421_, v_fst_4366_, v___x_4430_);
v___x_4432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4432_, 0, v_fst_4366_);
lean_ctor_set(v___x_4432_, 1, v_elimStack_4422_);
if (v_isShared_4427_ == 0)
{
lean_ctor_set(v___x_4426_, 39, v___x_4432_);
lean_ctor_set(v___x_4426_, 38, v___x_4431_);
v___x_4434_ = v___x_4426_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_id_4382_);
lean_ctor_set(v_reuseFailAlloc_4439_, 1, v_ringId_x3f_4383_);
lean_ctor_set(v_reuseFailAlloc_4439_, 2, v_type_4384_);
lean_ctor_set(v_reuseFailAlloc_4439_, 3, v_u_4385_);
lean_ctor_set(v_reuseFailAlloc_4439_, 4, v_intModuleInst_4386_);
lean_ctor_set(v_reuseFailAlloc_4439_, 5, v_leInst_x3f_4387_);
lean_ctor_set(v_reuseFailAlloc_4439_, 6, v_ltInst_x3f_4388_);
lean_ctor_set(v_reuseFailAlloc_4439_, 7, v_lawfulOrderLTInst_x3f_4389_);
lean_ctor_set(v_reuseFailAlloc_4439_, 8, v_isPreorderInst_x3f_4390_);
lean_ctor_set(v_reuseFailAlloc_4439_, 9, v_orderedAddInst_x3f_4391_);
lean_ctor_set(v_reuseFailAlloc_4439_, 10, v_isLinearInst_x3f_4392_);
lean_ctor_set(v_reuseFailAlloc_4439_, 11, v_noNatDivInst_x3f_4393_);
lean_ctor_set(v_reuseFailAlloc_4439_, 12, v_ringInst_x3f_4394_);
lean_ctor_set(v_reuseFailAlloc_4439_, 13, v_commRingInst_x3f_4395_);
lean_ctor_set(v_reuseFailAlloc_4439_, 14, v_orderedRingInst_x3f_4396_);
lean_ctor_set(v_reuseFailAlloc_4439_, 15, v_fieldInst_x3f_4397_);
lean_ctor_set(v_reuseFailAlloc_4439_, 16, v_charInst_x3f_4398_);
lean_ctor_set(v_reuseFailAlloc_4439_, 17, v_zero_4399_);
lean_ctor_set(v_reuseFailAlloc_4439_, 18, v_ofNatZero_4400_);
lean_ctor_set(v_reuseFailAlloc_4439_, 19, v_one_x3f_4401_);
lean_ctor_set(v_reuseFailAlloc_4439_, 20, v_leFn_x3f_4402_);
lean_ctor_set(v_reuseFailAlloc_4439_, 21, v_ltFn_x3f_4403_);
lean_ctor_set(v_reuseFailAlloc_4439_, 22, v_addFn_4404_);
lean_ctor_set(v_reuseFailAlloc_4439_, 23, v_zsmulFn_4405_);
lean_ctor_set(v_reuseFailAlloc_4439_, 24, v_nsmulFn_4406_);
lean_ctor_set(v_reuseFailAlloc_4439_, 25, v_zsmulFn_x3f_4407_);
lean_ctor_set(v_reuseFailAlloc_4439_, 26, v_nsmulFn_x3f_4408_);
lean_ctor_set(v_reuseFailAlloc_4439_, 27, v_homomulFn_x3f_4409_);
lean_ctor_set(v_reuseFailAlloc_4439_, 28, v_subFn_4410_);
lean_ctor_set(v_reuseFailAlloc_4439_, 29, v_negFn_4411_);
lean_ctor_set(v_reuseFailAlloc_4439_, 30, v_vars_4412_);
lean_ctor_set(v_reuseFailAlloc_4439_, 31, v_varMap_4413_);
lean_ctor_set(v_reuseFailAlloc_4439_, 32, v_lowers_4414_);
lean_ctor_set(v_reuseFailAlloc_4439_, 33, v_uppers_4415_);
lean_ctor_set(v_reuseFailAlloc_4439_, 34, v_diseqs_4416_);
lean_ctor_set(v_reuseFailAlloc_4439_, 35, v_assignment_4417_);
lean_ctor_set(v_reuseFailAlloc_4439_, 36, v_conflict_x3f_4419_);
lean_ctor_set(v_reuseFailAlloc_4439_, 37, v_diseqSplits_4420_);
lean_ctor_set(v_reuseFailAlloc_4439_, 38, v___x_4431_);
lean_ctor_set(v_reuseFailAlloc_4439_, 39, v___x_4432_);
lean_ctor_set(v_reuseFailAlloc_4439_, 40, v_occurs_4423_);
lean_ctor_set(v_reuseFailAlloc_4439_, 41, v_ignored_4424_);
lean_ctor_set_uint8(v_reuseFailAlloc_4439_, sizeof(void*)*42, v_caseSplits_4418_);
v___x_4434_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
lean_object* v___x_4435_; lean_object* v___x_4437_; 
v___x_4435_ = lean_array_fset(v_xs_x27_4429_, v___y_4364_, v___x_4434_);
if (v_isShared_4380_ == 0)
{
lean_ctor_set(v___x_4379_, 0, v___x_4435_);
v___x_4437_ = v___x_4379_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v___x_4435_);
lean_ctor_set(v_reuseFailAlloc_4438_, 1, v_typeIdOf_4369_);
lean_ctor_set(v_reuseFailAlloc_4438_, 2, v_exprToStructId_4370_);
lean_ctor_set(v_reuseFailAlloc_4438_, 3, v_exprToStructIdEntries_4371_);
lean_ctor_set(v_reuseFailAlloc_4438_, 4, v_forbiddenNatModules_4372_);
lean_ctor_set(v_reuseFailAlloc_4438_, 5, v_natStructs_4373_);
lean_ctor_set(v_reuseFailAlloc_4438_, 6, v_natTypeIdOf_4374_);
lean_ctor_set(v_reuseFailAlloc_4438_, 7, v_exprToNatStructId_4375_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed(lean_object* v___y_4450_, lean_object* v_snd_4451_, lean_object* v_fst_4452_, lean_object* v_s_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(v___y_4450_, v_snd_4451_, v_fst_4452_, v_s_4453_);
lean_dec(v___y_4450_);
return v_res_4454_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1(void){
_start:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4456_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0));
v___x_4457_ = l_Lean_stringToMessageData(v___x_4456_);
return v___x_4457_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4(void){
_start:
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
v___x_4463_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4465_ = l_Lean_Name_append(v___x_4464_, v___x_4463_);
return v___x_4465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object* v_c_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_){
_start:
{
lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4492_; lean_object* v___y_4493_; lean_object* v___y_4494_; lean_object* v___y_4495_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4504_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4514_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v_options_4545_; lean_object* v_inheritedTraceOptions_4546_; uint8_t v_hasTrace_4547_; lean_object* v___y_4549_; lean_object* v___y_4550_; lean_object* v___y_4551_; lean_object* v___y_4552_; lean_object* v___y_4553_; lean_object* v___y_4554_; lean_object* v___y_4555_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v_options_4564_; lean_object* v_inheritedTraceOptions_4565_; lean_object* v___y_4566_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v___y_4590_; lean_object* v___y_4591_; lean_object* v___y_4592_; lean_object* v___y_4593_; 
v_options_4545_ = lean_ctor_get(v_a_4476_, 2);
v_inheritedTraceOptions_4546_ = lean_ctor_get(v_a_4476_, 13);
v_hasTrace_4547_ = lean_ctor_get_uint8(v_options_4545_, sizeof(void*)*1);
if (v_hasTrace_4547_ == 0)
{
v___y_4583_ = v_a_4467_;
v___y_4584_ = v_a_4468_;
v___y_4585_ = v_a_4469_;
v___y_4586_ = v_a_4470_;
v___y_4587_ = v_a_4471_;
v___y_4588_ = v_a_4472_;
v___y_4589_ = v_a_4473_;
v___y_4590_ = v_a_4474_;
v___y_4591_ = v_a_4475_;
v___y_4592_ = v_a_4476_;
v___y_4593_ = v_a_4477_;
goto v___jp_4582_;
}
else
{
lean_object* v_cls_4689_; lean_object* v___x_4690_; uint8_t v___x_4691_; 
v_cls_4689_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_4690_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_4691_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4546_, v_options_4545_, v___x_4690_);
if (v___x_4691_ == 0)
{
v___y_4583_ = v_a_4467_;
v___y_4584_ = v_a_4468_;
v___y_4585_ = v_a_4469_;
v___y_4586_ = v_a_4470_;
v___y_4587_ = v_a_4471_;
v___y_4588_ = v_a_4472_;
v___y_4589_ = v_a_4473_;
v___y_4590_ = v_a_4474_;
v___y_4591_ = v_a_4475_;
v___y_4592_ = v_a_4476_;
v___y_4593_ = v_a_4477_;
goto v___jp_4582_;
}
else
{
lean_object* v___x_4692_; 
v___x_4692_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_, v_a_4473_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_);
if (lean_obj_tag(v___x_4692_) == 0)
{
lean_object* v_a_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v_a_4693_ = lean_ctor_get(v___x_4692_, 0);
lean_inc(v_a_4693_);
lean_dec_ref(v___x_4692_);
v___x_4694_ = l_Lean_MessageData_ofExpr(v_a_4693_);
v___x_4695_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4689_, v___x_4694_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_);
if (lean_obj_tag(v___x_4695_) == 0)
{
lean_dec_ref(v___x_4695_);
v___y_4583_ = v_a_4467_;
v___y_4584_ = v_a_4468_;
v___y_4585_ = v_a_4469_;
v___y_4586_ = v_a_4470_;
v___y_4587_ = v_a_4471_;
v___y_4588_ = v_a_4472_;
v___y_4589_ = v_a_4473_;
v___y_4590_ = v_a_4474_;
v___y_4591_ = v_a_4475_;
v___y_4592_ = v_a_4476_;
v___y_4593_ = v_a_4477_;
goto v___jp_4582_;
}
else
{
lean_dec_ref(v_c_4466_);
return v___x_4695_;
}
}
else
{
lean_object* v_a_4696_; lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4703_; 
lean_dec_ref(v_c_4466_);
v_a_4696_ = lean_ctor_get(v___x_4692_, 0);
v_isSharedCheck_4703_ = !lean_is_exclusive(v___x_4692_);
if (v_isSharedCheck_4703_ == 0)
{
v___x_4698_ = v___x_4692_;
v_isShared_4699_ = v_isSharedCheck_4703_;
goto v_resetjp_4697_;
}
else
{
lean_inc(v_a_4696_);
lean_dec(v___x_4692_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4703_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v___x_4701_; 
if (v_isShared_4699_ == 0)
{
v___x_4701_ = v___x_4698_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4702_; 
v_reuseFailAlloc_4702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4702_, 0, v_a_4696_);
v___x_4701_ = v_reuseFailAlloc_4702_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
return v___x_4701_;
}
}
}
}
}
v___jp_4479_:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; 
v___x_4480_ = lean_box(0);
v___x_4481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4481_, 0, v___x_4480_);
return v___x_4481_;
}
v___jp_4482_:
{
lean_object* v___f_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
lean_inc(v___y_4488_);
v___f_4499_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4499_, 0, v___y_4488_);
lean_closure_set(v___f_4499_, 1, v___y_4483_);
lean_closure_set(v___f_4499_, 2, v___y_4484_);
v___x_4500_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4501_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4500_, v___f_4499_, v___y_4489_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v___x_4502_; 
lean_dec_ref(v___x_4501_);
v___x_4502_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v___y_4487_, v___y_4486_, v___y_4485_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
return v___x_4502_;
}
else
{
lean_dec(v___y_4487_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
return v___x_4501_;
}
}
v___jp_4503_:
{
lean_object* v___x_4520_; 
v___x_4520_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
if (lean_obj_tag(v___x_4520_) == 0)
{
lean_object* v_a_4521_; uint8_t v_caseSplits_4522_; 
v_a_4521_ = lean_ctor_get(v___x_4520_, 0);
lean_inc(v_a_4521_);
lean_dec_ref(v___x_4520_);
v_caseSplits_4522_ = lean_ctor_get_uint8(v_a_4521_, sizeof(void*)*42);
lean_dec(v_a_4521_);
if (v_caseSplits_4522_ == 0)
{
lean_object* v___x_4523_; 
v___x_4523_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v___y_4506_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
if (lean_obj_tag(v___x_4523_) == 0)
{
lean_object* v_a_4524_; uint8_t v___x_4525_; 
v_a_4524_ = lean_ctor_get(v___x_4523_, 0);
lean_inc(v_a_4524_);
lean_dec_ref(v___x_4523_);
v___x_4525_ = lean_unbox(v_a_4524_);
lean_dec(v_a_4524_);
if (v___x_4525_ == 0)
{
v___y_4483_ = v___y_4504_;
v___y_4484_ = v___y_4505_;
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
goto v___jp_4482_;
}
else
{
lean_object* v___x_4526_; lean_object* v_a_4527_; lean_object* v___x_4528_; 
lean_inc_ref(v___y_4506_);
v___x_4526_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v___y_4506_);
v_a_4527_ = lean_ctor_get(v___x_4526_, 0);
lean_inc(v_a_4527_);
lean_dec_ref(v___x_4526_);
v___x_4528_ = l_Lean_Meta_Grind_Arith_Linear_propagateImpEq(v_a_4527_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
if (lean_obj_tag(v___x_4528_) == 0)
{
lean_dec_ref(v___x_4528_);
v___y_4483_ = v___y_4504_;
v___y_4484_ = v___y_4505_;
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
goto v___jp_4482_;
}
else
{
lean_dec(v___y_4508_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
return v___x_4528_;
}
}
}
else
{
lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4536_; 
lean_dec(v___y_4508_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
v_a_4529_ = lean_ctor_get(v___x_4523_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v___x_4523_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4531_ = v___x_4523_;
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_dec(v___x_4523_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4534_; 
if (v_isShared_4532_ == 0)
{
v___x_4534_ = v___x_4531_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_a_4529_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
return v___x_4534_;
}
}
}
}
else
{
v___y_4483_ = v___y_4504_;
v___y_4484_ = v___y_4505_;
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
goto v___jp_4482_;
}
}
else
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4544_; 
lean_dec(v___y_4508_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
v_a_4537_ = lean_ctor_get(v___x_4520_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4539_ = v___x_4520_;
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v___x_4520_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4542_; 
if (v_isShared_4540_ == 0)
{
v___x_4542_ = v___x_4539_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_a_4537_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
return v___x_4542_;
}
}
}
}
v___jp_4548_:
{
lean_object* v___x_4567_; lean_object* v___x_4568_; uint8_t v___x_4569_; 
v___x_4567_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_4568_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_4569_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4565_, v_options_4564_, v___x_4568_);
if (v___x_4569_ == 0)
{
v___y_4504_ = v___y_4549_;
v___y_4505_ = v___y_4550_;
v___y_4506_ = v___y_4551_;
v___y_4507_ = v___y_4552_;
v___y_4508_ = v___y_4553_;
v___y_4509_ = v___y_4554_;
v___y_4510_ = v___y_4555_;
v___y_4511_ = v___y_4556_;
v___y_4512_ = v___y_4557_;
v___y_4513_ = v___y_4558_;
v___y_4514_ = v___y_4559_;
v___y_4515_ = v___y_4560_;
v___y_4516_ = v___y_4561_;
v___y_4517_ = v___y_4562_;
v___y_4518_ = v___y_4563_;
v___y_4519_ = v___y_4566_;
goto v___jp_4503_;
}
else
{
lean_object* v___x_4570_; 
v___x_4570_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v___y_4551_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4566_);
if (lean_obj_tag(v___x_4570_) == 0)
{
lean_object* v_a_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v_a_4571_ = lean_ctor_get(v___x_4570_, 0);
lean_inc(v_a_4571_);
lean_dec_ref(v___x_4570_);
v___x_4572_ = l_Lean_MessageData_ofExpr(v_a_4571_);
v___x_4573_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4567_, v___x_4572_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4566_);
if (lean_obj_tag(v___x_4573_) == 0)
{
lean_dec_ref(v___x_4573_);
v___y_4504_ = v___y_4549_;
v___y_4505_ = v___y_4550_;
v___y_4506_ = v___y_4551_;
v___y_4507_ = v___y_4552_;
v___y_4508_ = v___y_4553_;
v___y_4509_ = v___y_4554_;
v___y_4510_ = v___y_4555_;
v___y_4511_ = v___y_4556_;
v___y_4512_ = v___y_4557_;
v___y_4513_ = v___y_4558_;
v___y_4514_ = v___y_4559_;
v___y_4515_ = v___y_4560_;
v___y_4516_ = v___y_4561_;
v___y_4517_ = v___y_4562_;
v___y_4518_ = v___y_4563_;
v___y_4519_ = v___y_4566_;
goto v___jp_4503_;
}
else
{
lean_dec(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
return v___x_4573_;
}
}
else
{
lean_object* v_a_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4581_; 
lean_dec(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
v_a_4574_ = lean_ctor_get(v___x_4570_, 0);
v_isSharedCheck_4581_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4581_ == 0)
{
v___x_4576_ = v___x_4570_;
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_a_4574_);
lean_dec(v___x_4570_);
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
}
v___jp_4582_:
{
lean_object* v___x_4594_; 
lean_inc_ref(v___y_4592_);
v___x_4594_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_4466_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
if (lean_obj_tag(v___x_4594_) == 0)
{
lean_object* v_a_4595_; lean_object* v_p_4596_; lean_object* v___x_4597_; uint8_t v___x_4598_; 
v_a_4595_ = lean_ctor_get(v___x_4594_, 0);
lean_inc(v_a_4595_);
lean_dec_ref(v___x_4594_);
v_p_4596_ = lean_ctor_get(v_a_4595_, 0);
v___x_4597_ = lean_box(0);
v___x_4598_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_4596_, v___x_4597_);
if (v___x_4598_ == 0)
{
lean_object* v___x_4599_; 
v___x_4599_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_a_4595_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
if (lean_obj_tag(v___x_4599_) == 0)
{
lean_object* v_a_4600_; lean_object* v_snd_4601_; lean_object* v_options_4602_; uint8_t v_hasTrace_4603_; 
v_a_4600_ = lean_ctor_get(v___x_4599_, 0);
lean_inc(v_a_4600_);
lean_dec_ref(v___x_4599_);
v_snd_4601_ = lean_ctor_get(v_a_4600_, 1);
lean_inc(v_snd_4601_);
v_options_4602_ = lean_ctor_get(v___y_4592_, 2);
v_hasTrace_4603_ = lean_ctor_get_uint8(v_options_4602_, sizeof(void*)*1);
if (v_hasTrace_4603_ == 0)
{
lean_object* v_fst_4604_; lean_object* v_fst_4605_; lean_object* v_snd_4606_; 
v_fst_4604_ = lean_ctor_get(v_a_4600_, 0);
lean_inc(v_fst_4604_);
lean_dec(v_a_4600_);
v_fst_4605_ = lean_ctor_get(v_snd_4601_, 0);
lean_inc_n(v_fst_4605_, 2);
v_snd_4606_ = lean_ctor_get(v_snd_4601_, 1);
lean_inc_n(v_snd_4606_, 2);
lean_dec(v_snd_4601_);
v___y_4504_ = v_snd_4606_;
v___y_4505_ = v_fst_4605_;
v___y_4506_ = v_snd_4606_;
v___y_4507_ = v_fst_4605_;
v___y_4508_ = v_fst_4604_;
v___y_4509_ = v___y_4583_;
v___y_4510_ = v___y_4584_;
v___y_4511_ = v___y_4585_;
v___y_4512_ = v___y_4586_;
v___y_4513_ = v___y_4587_;
v___y_4514_ = v___y_4588_;
v___y_4515_ = v___y_4589_;
v___y_4516_ = v___y_4590_;
v___y_4517_ = v___y_4591_;
v___y_4518_ = v___y_4592_;
v___y_4519_ = v___y_4593_;
goto v___jp_4503_;
}
else
{
lean_object* v_fst_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4653_; 
v_fst_4607_ = lean_ctor_get(v_a_4600_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v_a_4600_);
if (v_isSharedCheck_4653_ == 0)
{
lean_object* v_unused_4654_; 
v_unused_4654_ = lean_ctor_get(v_a_4600_, 1);
lean_dec(v_unused_4654_);
v___x_4609_ = v_a_4600_;
v_isShared_4610_ = v_isSharedCheck_4653_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_fst_4607_);
lean_dec(v_a_4600_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4653_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v_fst_4611_; lean_object* v_snd_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4652_; 
v_fst_4611_ = lean_ctor_get(v_snd_4601_, 0);
v_snd_4612_ = lean_ctor_get(v_snd_4601_, 1);
v_isSharedCheck_4652_ = !lean_is_exclusive(v_snd_4601_);
if (v_isSharedCheck_4652_ == 0)
{
v___x_4614_ = v_snd_4601_;
v_isShared_4615_ = v_isSharedCheck_4652_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_snd_4612_);
lean_inc(v_fst_4611_);
lean_dec(v_snd_4601_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4652_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v_inheritedTraceOptions_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; uint8_t v___x_4619_; 
v_inheritedTraceOptions_4616_ = lean_ctor_get(v___y_4592_, 13);
v___x_4617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_4618_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_4619_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4616_, v_options_4602_, v___x_4618_);
if (v___x_4619_ == 0)
{
lean_del_object(v___x_4614_);
lean_del_object(v___x_4609_);
lean_inc(v_fst_4611_);
lean_inc(v_snd_4612_);
v___y_4549_ = v_snd_4612_;
v___y_4550_ = v_fst_4611_;
v___y_4551_ = v_snd_4612_;
v___y_4552_ = v_fst_4611_;
v___y_4553_ = v_fst_4607_;
v___y_4554_ = v___y_4583_;
v___y_4555_ = v___y_4584_;
v___y_4556_ = v___y_4585_;
v___y_4557_ = v___y_4586_;
v___y_4558_ = v___y_4587_;
v___y_4559_ = v___y_4588_;
v___y_4560_ = v___y_4589_;
v___y_4561_ = v___y_4590_;
v___y_4562_ = v___y_4591_;
v___y_4563_ = v___y_4592_;
v_options_4564_ = v_options_4602_;
v_inheritedTraceOptions_4565_ = v_inheritedTraceOptions_4616_;
v___y_4566_ = v___y_4593_;
goto v___jp_4548_;
}
else
{
lean_object* v___x_4620_; 
v___x_4620_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_4611_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_object* v_a_4621_; lean_object* v___x_4622_; 
v_a_4621_ = lean_ctor_get(v___x_4620_, 0);
lean_inc(v_a_4621_);
lean_dec_ref(v___x_4620_);
v___x_4622_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_4612_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
if (lean_obj_tag(v___x_4622_) == 0)
{
lean_object* v_a_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4627_; 
v_a_4623_ = lean_ctor_get(v___x_4622_, 0);
lean_inc(v_a_4623_);
lean_dec_ref(v___x_4622_);
v___x_4624_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1);
v___x_4625_ = l_Lean_MessageData_ofExpr(v_a_4621_);
if (v_isShared_4615_ == 0)
{
lean_ctor_set_tag(v___x_4614_, 7);
lean_ctor_set(v___x_4614_, 1, v___x_4625_);
lean_ctor_set(v___x_4614_, 0, v___x_4624_);
v___x_4627_ = v___x_4614_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v___x_4624_);
lean_ctor_set(v_reuseFailAlloc_4635_, 1, v___x_4625_);
v___x_4627_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
lean_object* v___x_4628_; lean_object* v___x_4630_; 
v___x_4628_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_4610_ == 0)
{
lean_ctor_set_tag(v___x_4609_, 7);
lean_ctor_set(v___x_4609_, 1, v___x_4628_);
lean_ctor_set(v___x_4609_, 0, v___x_4627_);
v___x_4630_ = v___x_4609_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v___x_4627_);
lean_ctor_set(v_reuseFailAlloc_4634_, 1, v___x_4628_);
v___x_4630_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4631_ = l_Lean_MessageData_ofExpr(v_a_4623_);
v___x_4632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4632_, 0, v___x_4630_);
lean_ctor_set(v___x_4632_, 1, v___x_4631_);
v___x_4633_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4617_, v___x_4632_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_dec_ref(v___x_4633_);
lean_inc(v_fst_4611_);
lean_inc(v_snd_4612_);
v___y_4549_ = v_snd_4612_;
v___y_4550_ = v_fst_4611_;
v___y_4551_ = v_snd_4612_;
v___y_4552_ = v_fst_4611_;
v___y_4553_ = v_fst_4607_;
v___y_4554_ = v___y_4583_;
v___y_4555_ = v___y_4584_;
v___y_4556_ = v___y_4585_;
v___y_4557_ = v___y_4586_;
v___y_4558_ = v___y_4587_;
v___y_4559_ = v___y_4588_;
v___y_4560_ = v___y_4589_;
v___y_4561_ = v___y_4590_;
v___y_4562_ = v___y_4591_;
v___y_4563_ = v___y_4592_;
v_options_4564_ = v_options_4602_;
v_inheritedTraceOptions_4565_ = v_inheritedTraceOptions_4616_;
v___y_4566_ = v___y_4593_;
goto v___jp_4548_;
}
else
{
lean_dec(v_snd_4612_);
lean_dec(v_fst_4611_);
lean_dec(v_fst_4607_);
return v___x_4633_;
}
}
}
}
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
lean_dec(v_a_4621_);
lean_del_object(v___x_4614_);
lean_dec(v_snd_4612_);
lean_dec(v_fst_4611_);
lean_del_object(v___x_4609_);
lean_dec(v_fst_4607_);
v_a_4636_ = lean_ctor_get(v___x_4622_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4622_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4622_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4622_);
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
lean_object* v_a_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4651_; 
lean_del_object(v___x_4614_);
lean_dec(v_snd_4612_);
lean_dec(v_fst_4611_);
lean_del_object(v___x_4609_);
lean_dec(v_fst_4607_);
v_a_4644_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4646_ = v___x_4620_;
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_a_4644_);
lean_dec(v___x_4620_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4649_; 
if (v_isShared_4647_ == 0)
{
v___x_4649_ = v___x_4646_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_a_4644_);
v___x_4649_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
return v___x_4649_;
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
lean_object* v_a_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4662_; 
v_a_4655_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4662_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4657_ = v___x_4599_;
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_a_4655_);
lean_dec(v___x_4599_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v___x_4660_; 
if (v_isShared_4658_ == 0)
{
v___x_4660_ = v___x_4657_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_a_4655_);
v___x_4660_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
return v___x_4660_;
}
}
}
}
else
{
lean_object* v_options_4663_; uint8_t v_hasTrace_4664_; 
v_options_4663_ = lean_ctor_get(v___y_4592_, 2);
v_hasTrace_4664_ = lean_ctor_get_uint8(v_options_4663_, sizeof(void*)*1);
if (v_hasTrace_4664_ == 0)
{
lean_dec(v_a_4595_);
goto v___jp_4479_;
}
else
{
lean_object* v_inheritedTraceOptions_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; uint8_t v___x_4668_; 
v_inheritedTraceOptions_4665_ = lean_ctor_get(v___y_4592_, 13);
v___x_4666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4667_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4);
v___x_4668_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4665_, v_options_4663_, v___x_4667_);
if (v___x_4668_ == 0)
{
lean_dec(v_a_4595_);
goto v___jp_4479_;
}
else
{
lean_object* v___x_4669_; 
v___x_4669_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_a_4595_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
lean_dec(v_a_4595_);
if (lean_obj_tag(v___x_4669_) == 0)
{
lean_object* v_a_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
v_a_4670_ = lean_ctor_get(v___x_4669_, 0);
lean_inc(v_a_4670_);
lean_dec_ref(v___x_4669_);
v___x_4671_ = l_Lean_MessageData_ofExpr(v_a_4670_);
v___x_4672_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4666_, v___x_4671_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
if (lean_obj_tag(v___x_4672_) == 0)
{
lean_dec_ref(v___x_4672_);
goto v___jp_4479_;
}
else
{
return v___x_4672_;
}
}
else
{
lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4680_; 
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
}
}
else
{
lean_object* v_a_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4688_; 
v_a_4681_ = lean_ctor_get(v___x_4594_, 0);
v_isSharedCheck_4688_ = !lean_is_exclusive(v___x_4594_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4683_ = v___x_4594_;
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_a_4681_);
lean_dec(v___x_4594_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4686_; 
if (v_isShared_4684_ == 0)
{
v___x_4686_ = v___x_4683_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_a_4681_);
v___x_4686_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
return v___x_4686_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object* v_c_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_){
_start:
{
lean_object* v_res_4717_; 
v_res_4717_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v_c_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_);
lean_dec(v_a_4715_);
lean_dec_ref(v_a_4714_);
lean_dec(v_a_4713_);
lean_dec_ref(v_a_4712_);
lean_dec(v_a_4711_);
lean_dec_ref(v_a_4710_);
lean_dec(v_a_4709_);
lean_dec_ref(v_a_4708_);
lean_dec(v_a_4707_);
lean_dec(v_a_4706_);
lean_dec(v_a_4705_);
return v_res_4717_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2(void){
_start:
{
lean_object* v_cls_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; 
v_cls_4722_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4723_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4724_ = l_Lean_Name_append(v___x_4723_, v_cls_4722_);
return v___x_4724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object* v_a_4725_, lean_object* v_b_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_){
_start:
{
lean_object* v_options_4735_; uint8_t v_hasTrace_4736_; 
v_options_4735_ = lean_ctor_get(v_a_4729_, 2);
v_hasTrace_4736_ = lean_ctor_get_uint8(v_options_4735_, sizeof(void*)*1);
if (v_hasTrace_4736_ == 0)
{
lean_dec_ref(v_b_4726_);
lean_dec_ref(v_a_4725_);
goto v___jp_4732_;
}
else
{
lean_object* v_inheritedTraceOptions_4737_; lean_object* v_cls_4738_; lean_object* v___x_4739_; uint8_t v___x_4740_; 
v_inheritedTraceOptions_4737_ = lean_ctor_get(v_a_4729_, 13);
v_cls_4738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4739_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2);
v___x_4740_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4737_, v_options_4735_, v___x_4739_);
if (v___x_4740_ == 0)
{
lean_dec_ref(v_b_4726_);
lean_dec_ref(v_a_4725_);
goto v___jp_4732_;
}
else
{
lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; 
v___x_4741_ = l_Lean_MessageData_ofExpr(v_a_4725_);
v___x_4742_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_4743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4743_, 0, v___x_4741_);
lean_ctor_set(v___x_4743_, 1, v___x_4742_);
v___x_4744_ = l_Lean_MessageData_ofExpr(v_b_4726_);
v___x_4745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4745_, 0, v___x_4743_);
lean_ctor_set(v___x_4745_, 1, v___x_4744_);
v___x_4746_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4738_, v___x_4745_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_);
return v___x_4746_;
}
}
v___jp_4732_:
{
lean_object* v___x_4733_; lean_object* v___x_4734_; 
v___x_4733_ = lean_box(0);
v___x_4734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4734_, 0, v___x_4733_);
return v___x_4734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object* v_a_4747_, lean_object* v_b_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4747_, v_b_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
lean_dec(v_a_4752_);
lean_dec_ref(v_a_4751_);
lean_dec(v_a_4750_);
lean_dec_ref(v_a_4749_);
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object* v_a_4755_, lean_object* v_b_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_){
_start:
{
lean_object* v___x_4769_; 
v___x_4769_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4755_, v_b_4756_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_);
return v___x_4769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object* v_a_4770_, lean_object* v_b_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_){
_start:
{
lean_object* v_res_4784_; 
v_res_4784_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(v_a_4770_, v_b_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_);
lean_dec(v_a_4782_);
lean_dec_ref(v_a_4781_);
lean_dec(v_a_4780_);
lean_dec_ref(v_a_4779_);
lean_dec(v_a_4778_);
lean_dec_ref(v_a_4777_);
lean_dec(v_a_4776_);
lean_dec_ref(v_a_4775_);
lean_dec(v_a_4774_);
lean_dec(v_a_4773_);
lean_dec(v_a_4772_);
return v_res_4784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object* v_a_4785_, lean_object* v_b_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_){
_start:
{
lean_object* v___x_4799_; 
v___x_4799_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4785_, v_a_4788_);
if (lean_obj_tag(v___x_4799_) == 0)
{
lean_object* v_a_4800_; uint8_t v___x_4801_; lean_object* v___x_4802_; 
v_a_4800_ = lean_ctor_get(v___x_4799_, 0);
lean_inc(v_a_4800_);
lean_dec_ref(v___x_4799_);
v___x_4801_ = 0;
lean_inc_ref(v_a_4785_);
v___x_4802_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_4785_, v___x_4801_, v_a_4800_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_);
if (lean_obj_tag(v___x_4802_) == 0)
{
lean_object* v_a_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4852_; 
v_a_4803_ = lean_ctor_get(v___x_4802_, 0);
v_isSharedCheck_4852_ = !lean_is_exclusive(v___x_4802_);
if (v_isSharedCheck_4852_ == 0)
{
v___x_4805_ = v___x_4802_;
v_isShared_4806_ = v_isSharedCheck_4852_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_a_4803_);
lean_dec(v___x_4802_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4852_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
if (lean_obj_tag(v_a_4803_) == 1)
{
lean_object* v_val_4807_; lean_object* v___x_4808_; 
lean_del_object(v___x_4805_);
v_val_4807_ = lean_ctor_get(v_a_4803_, 0);
lean_inc(v_val_4807_);
lean_dec_ref(v_a_4803_);
v___x_4808_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4786_, v_a_4788_);
if (lean_obj_tag(v___x_4808_) == 0)
{
lean_object* v_a_4809_; lean_object* v___x_4810_; 
v_a_4809_ = lean_ctor_get(v___x_4808_, 0);
lean_inc(v_a_4809_);
lean_dec_ref(v___x_4808_);
lean_inc_ref(v_b_4786_);
v___x_4810_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_4786_, v___x_4801_, v_a_4809_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_);
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4831_; 
v_a_4811_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4831_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4831_ == 0)
{
v___x_4813_ = v___x_4810_;
v_isShared_4814_ = v_isSharedCheck_4831_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4810_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4831_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
if (lean_obj_tag(v_a_4811_) == 1)
{
lean_object* v_val_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; uint8_t v___x_4819_; 
v_val_4815_ = lean_ctor_get(v_a_4811_, 0);
lean_inc_n(v_val_4815_, 2);
lean_dec_ref(v_a_4811_);
lean_inc(v_val_4807_);
v___x_4816_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4816_, 0, v_val_4807_);
lean_ctor_set(v___x_4816_, 1, v_val_4815_);
v___x_4817_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4816_);
v___x_4818_ = lean_box(0);
v___x_4819_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4817_, v___x_4818_);
if (v___x_4819_ == 0)
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; 
lean_del_object(v___x_4813_);
v___x_4820_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4820_, 0, v_a_4785_);
lean_ctor_set(v___x_4820_, 1, v_b_4786_);
lean_ctor_set(v___x_4820_, 2, v_val_4807_);
lean_ctor_set(v___x_4820_, 3, v_val_4815_);
v___x_4821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4817_);
lean_ctor_set(v___x_4821_, 1, v___x_4820_);
v___x_4822_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_4821_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_);
return v___x_4822_;
}
else
{
lean_object* v___x_4823_; lean_object* v___x_4825_; 
lean_dec(v___x_4817_);
lean_dec(v_val_4815_);
lean_dec(v_val_4807_);
lean_dec_ref(v_b_4786_);
lean_dec_ref(v_a_4785_);
v___x_4823_ = lean_box(0);
if (v_isShared_4814_ == 0)
{
lean_ctor_set(v___x_4813_, 0, v___x_4823_);
v___x_4825_ = v___x_4813_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v___x_4823_);
v___x_4825_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
return v___x_4825_;
}
}
}
else
{
lean_object* v___x_4827_; lean_object* v___x_4829_; 
lean_dec(v_a_4811_);
lean_dec(v_val_4807_);
lean_dec_ref(v_b_4786_);
lean_dec_ref(v_a_4785_);
v___x_4827_ = lean_box(0);
if (v_isShared_4814_ == 0)
{
lean_ctor_set(v___x_4813_, 0, v___x_4827_);
v___x_4829_ = v___x_4813_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v___x_4827_);
v___x_4829_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
return v___x_4829_;
}
}
}
}
else
{
lean_object* v_a_4832_; lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4839_; 
lean_dec(v_val_4807_);
lean_dec_ref(v_b_4786_);
lean_dec_ref(v_a_4785_);
v_a_4832_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4839_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4839_ == 0)
{
v___x_4834_ = v___x_4810_;
v_isShared_4835_ = v_isSharedCheck_4839_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_a_4832_);
lean_dec(v___x_4810_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4839_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
lean_object* v___x_4837_; 
if (v_isShared_4835_ == 0)
{
v___x_4837_ = v___x_4834_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4838_; 
v_reuseFailAlloc_4838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_a_4832_);
v___x_4837_ = v_reuseFailAlloc_4838_;
goto v_reusejp_4836_;
}
v_reusejp_4836_:
{
return v___x_4837_;
}
}
}
}
else
{
lean_object* v_a_4840_; lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4847_; 
lean_dec(v_val_4807_);
lean_dec_ref(v_b_4786_);
lean_dec_ref(v_a_4785_);
v_a_4840_ = lean_ctor_get(v___x_4808_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v___x_4808_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4842_ = v___x_4808_;
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_a_4840_);
lean_dec(v___x_4808_);
v___x_4842_ = lean_box(0);
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
v_resetjp_4841_:
{
lean_object* v___x_4845_; 
if (v_isShared_4843_ == 0)
{
v___x_4845_ = v___x_4842_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v_a_4840_);
v___x_4845_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
return v___x_4845_;
}
}
}
}
else
{
lean_object* v___x_4848_; lean_object* v___x_4850_; 
lean_dec(v_a_4803_);
lean_dec_ref(v_b_4786_);
lean_dec_ref(v_a_4785_);
v___x_4848_ = lean_box(0);
if (v_isShared_4806_ == 0)
{
lean_ctor_set(v___x_4805_, 0, v___x_4848_);
v___x_4850_ = v___x_4805_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v___x_4848_);
v___x_4850_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
return v___x_4850_;
}
}
}
}
else
{
lean_object* v_a_4853_; lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_4860_; 
lean_dec_ref(v_b_4786_);
lean_dec_ref(v_a_4785_);
v_a_4853_ = lean_ctor_get(v___x_4802_, 0);
v_isSharedCheck_4860_ = !lean_is_exclusive(v___x_4802_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4855_ = v___x_4802_;
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
else
{
lean_inc(v_a_4853_);
lean_dec(v___x_4802_);
v___x_4855_ = lean_box(0);
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
v_resetjp_4854_:
{
lean_object* v___x_4858_; 
if (v_isShared_4856_ == 0)
{
v___x_4858_ = v___x_4855_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_a_4853_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
}
}
else
{
lean_object* v_a_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4868_; 
lean_dec_ref(v_b_4786_);
lean_dec_ref(v_a_4785_);
v_a_4861_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4868_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4863_ = v___x_4799_;
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_a_4861_);
lean_dec(v___x_4799_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
lean_object* v___x_4866_; 
if (v_isShared_4864_ == 0)
{
v___x_4866_ = v___x_4863_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_a_4861_);
v___x_4866_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
return v___x_4866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___boxed(lean_object* v_a_4869_, lean_object* v_b_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_){
_start:
{
lean_object* v_res_4883_; 
v_res_4883_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_4869_, v_b_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_);
lean_dec(v_a_4881_);
lean_dec_ref(v_a_4880_);
lean_dec(v_a_4879_);
lean_dec_ref(v_a_4878_);
lean_dec(v_a_4877_);
lean_dec_ref(v_a_4876_);
lean_dec(v_a_4875_);
lean_dec_ref(v_a_4874_);
lean_dec(v_a_4873_);
lean_dec(v_a_4872_);
lean_dec(v_a_4871_);
return v_res_4883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(lean_object* v_a_4884_, lean_object* v_b_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_){
_start:
{
lean_object* v___x_4898_; 
v___x_4898_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_);
if (lean_obj_tag(v___x_4898_) == 0)
{
lean_object* v_a_4899_; lean_object* v___x_4900_; 
v_a_4899_ = lean_ctor_get(v___x_4898_, 0);
lean_inc(v_a_4899_);
lean_dec_ref(v___x_4898_);
lean_inc_ref(v_a_4884_);
v___x_4900_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_4884_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_);
if (lean_obj_tag(v___x_4900_) == 0)
{
lean_object* v_a_4901_; lean_object* v_fst_4902_; lean_object* v___x_4903_; 
v_a_4901_ = lean_ctor_get(v___x_4900_, 0);
lean_inc(v_a_4901_);
lean_dec_ref(v___x_4900_);
v_fst_4902_ = lean_ctor_get(v_a_4901_, 0);
lean_inc(v_fst_4902_);
lean_dec(v_a_4901_);
lean_inc_ref(v_b_4885_);
v___x_4903_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_4885_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_);
if (lean_obj_tag(v___x_4903_) == 0)
{
lean_object* v_a_4904_; lean_object* v_fst_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4988_; 
v_a_4904_ = lean_ctor_get(v___x_4903_, 0);
lean_inc(v_a_4904_);
lean_dec_ref(v___x_4903_);
v_fst_4905_ = lean_ctor_get(v_a_4904_, 0);
v_isSharedCheck_4988_ = !lean_is_exclusive(v_a_4904_);
if (v_isSharedCheck_4988_ == 0)
{
lean_object* v_unused_4989_; 
v_unused_4989_ = lean_ctor_get(v_a_4904_, 1);
lean_dec(v_unused_4989_);
v___x_4907_ = v_a_4904_;
v_isShared_4908_ = v_isSharedCheck_4988_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_fst_4905_);
lean_dec(v_a_4904_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4988_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4909_; 
v___x_4909_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4884_, v_a_4887_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v_a_4910_; lean_object* v_id_4911_; lean_object* v_structId_4912_; uint8_t v___x_4913_; lean_object* v___x_4914_; 
v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
lean_inc(v_a_4910_);
lean_dec_ref(v___x_4909_);
v_id_4911_ = lean_ctor_get(v_a_4899_, 0);
lean_inc(v_id_4911_);
v_structId_4912_ = lean_ctor_get(v_a_4899_, 1);
lean_inc(v_structId_4912_);
lean_dec(v_a_4899_);
v___x_4913_ = 0;
v___x_4914_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4902_, v___x_4913_, v_a_4910_, v_structId_4912_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_);
if (lean_obj_tag(v___x_4914_) == 0)
{
lean_object* v_a_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4971_; 
v_a_4915_ = lean_ctor_get(v___x_4914_, 0);
v_isSharedCheck_4971_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4971_ == 0)
{
v___x_4917_ = v___x_4914_;
v_isShared_4918_ = v_isSharedCheck_4971_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_a_4915_);
lean_dec(v___x_4914_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4971_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
if (lean_obj_tag(v_a_4915_) == 1)
{
lean_object* v_val_4919_; lean_object* v___x_4920_; 
lean_del_object(v___x_4917_);
v_val_4919_ = lean_ctor_get(v_a_4915_, 0);
lean_inc(v_val_4919_);
lean_dec_ref(v_a_4915_);
v___x_4920_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4885_, v_a_4887_);
if (lean_obj_tag(v___x_4920_) == 0)
{
lean_object* v_a_4921_; lean_object* v___x_4922_; 
v_a_4921_ = lean_ctor_get(v___x_4920_, 0);
lean_inc(v_a_4921_);
lean_dec_ref(v___x_4920_);
v___x_4922_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4905_, v___x_4913_, v_a_4921_, v_structId_4912_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_);
if (lean_obj_tag(v___x_4922_) == 0)
{
lean_object* v_a_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4950_; 
v_a_4923_ = lean_ctor_get(v___x_4922_, 0);
v_isSharedCheck_4950_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_4950_ == 0)
{
v___x_4925_ = v___x_4922_;
v_isShared_4926_ = v_isSharedCheck_4950_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_a_4923_);
lean_dec(v___x_4922_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4950_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
if (lean_obj_tag(v_a_4923_) == 1)
{
lean_object* v_val_4927_; lean_object* v___x_4929_; 
v_val_4927_ = lean_ctor_get(v_a_4923_, 0);
lean_inc_n(v_val_4927_, 2);
lean_dec_ref(v_a_4923_);
lean_inc(v_val_4919_);
if (v_isShared_4908_ == 0)
{
lean_ctor_set_tag(v___x_4907_, 3);
lean_ctor_set(v___x_4907_, 1, v_val_4927_);
lean_ctor_set(v___x_4907_, 0, v_val_4919_);
v___x_4929_ = v___x_4907_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4945_; 
v_reuseFailAlloc_4945_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4945_, 0, v_val_4919_);
lean_ctor_set(v_reuseFailAlloc_4945_, 1, v_val_4927_);
v___x_4929_ = v_reuseFailAlloc_4945_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
lean_object* v___x_4930_; lean_object* v___x_4931_; uint8_t v___x_4932_; 
v___x_4930_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4929_);
v___x_4931_ = lean_box(0);
v___x_4932_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4930_, v___x_4931_);
if (v___x_4932_ == 0)
{
lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; 
lean_del_object(v___x_4925_);
lean_inc(v_val_4927_);
lean_inc(v_val_4919_);
lean_inc(v_id_4911_);
lean_inc_ref(v_b_4885_);
lean_inc_ref(v_a_4884_);
v___x_4933_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4933_, 0, v_a_4884_);
lean_ctor_set(v___x_4933_, 1, v_b_4885_);
lean_ctor_set(v___x_4933_, 2, v_id_4911_);
lean_ctor_set(v___x_4933_, 3, v_val_4919_);
lean_ctor_set(v___x_4933_, 4, v_val_4927_);
lean_inc(v___x_4930_);
v___x_4934_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4934_, 0, v___x_4930_);
lean_ctor_set(v___x_4934_, 1, v___x_4933_);
lean_ctor_set_uint8(v___x_4934_, sizeof(void*)*2, v___x_4913_);
v___x_4935_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4934_, v_structId_4912_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_);
if (lean_obj_tag(v___x_4935_) == 0)
{
lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; 
lean_dec_ref(v___x_4935_);
v___x_4936_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4937_ = l_Lean_Grind_Linarith_Poly_mul(v___x_4930_, v___x_4936_);
v___x_4938_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4938_, 0, v_b_4885_);
lean_ctor_set(v___x_4938_, 1, v_a_4884_);
lean_ctor_set(v___x_4938_, 2, v_id_4911_);
lean_ctor_set(v___x_4938_, 3, v_val_4927_);
lean_ctor_set(v___x_4938_, 4, v_val_4919_);
v___x_4939_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4939_, 0, v___x_4937_);
lean_ctor_set(v___x_4939_, 1, v___x_4938_);
lean_ctor_set_uint8(v___x_4939_, sizeof(void*)*2, v___x_4913_);
v___x_4940_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4939_, v_structId_4912_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_);
lean_dec(v_structId_4912_);
return v___x_4940_;
}
else
{
lean_dec(v___x_4930_);
lean_dec(v_val_4927_);
lean_dec(v_val_4919_);
lean_dec(v_structId_4912_);
lean_dec(v_id_4911_);
lean_dec_ref(v_b_4885_);
lean_dec_ref(v_a_4884_);
return v___x_4935_;
}
}
else
{
lean_object* v___x_4941_; lean_object* v___x_4943_; 
lean_dec(v___x_4930_);
lean_dec(v_val_4927_);
lean_dec(v_val_4919_);
lean_dec(v_structId_4912_);
lean_dec(v_id_4911_);
lean_dec_ref(v_b_4885_);
lean_dec_ref(v_a_4884_);
v___x_4941_ = lean_box(0);
if (v_isShared_4926_ == 0)
{
lean_ctor_set(v___x_4925_, 0, v___x_4941_);
v___x_4943_ = v___x_4925_;
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
lean_object* v___x_4946_; lean_object* v___x_4948_; 
lean_dec(v_a_4923_);
lean_dec(v_val_4919_);
lean_dec(v_structId_4912_);
lean_dec(v_id_4911_);
lean_del_object(v___x_4907_);
lean_dec_ref(v_b_4885_);
lean_dec_ref(v_a_4884_);
v___x_4946_ = lean_box(0);
if (v_isShared_4926_ == 0)
{
lean_ctor_set(v___x_4925_, 0, v___x_4946_);
v___x_4948_ = v___x_4925_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v___x_4946_);
v___x_4948_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
return v___x_4948_;
}
}
}
}
else
{
lean_object* v_a_4951_; lean_object* v___x_4953_; uint8_t v_isShared_4954_; uint8_t v_isSharedCheck_4958_; 
lean_dec(v_val_4919_);
lean_dec(v_structId_4912_);
lean_dec(v_id_4911_);
lean_del_object(v___x_4907_);
lean_dec_ref(v_b_4885_);
lean_dec_ref(v_a_4884_);
v_a_4951_ = lean_ctor_get(v___x_4922_, 0);
v_isSharedCheck_4958_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_4958_ == 0)
{
v___x_4953_ = v___x_4922_;
v_isShared_4954_ = v_isSharedCheck_4958_;
goto v_resetjp_4952_;
}
else
{
lean_inc(v_a_4951_);
lean_dec(v___x_4922_);
v___x_4953_ = lean_box(0);
v_isShared_4954_ = v_isSharedCheck_4958_;
goto v_resetjp_4952_;
}
v_resetjp_4952_:
{
lean_object* v___x_4956_; 
if (v_isShared_4954_ == 0)
{
v___x_4956_ = v___x_4953_;
goto v_reusejp_4955_;
}
else
{
lean_object* v_reuseFailAlloc_4957_; 
v_reuseFailAlloc_4957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4957_, 0, v_a_4951_);
v___x_4956_ = v_reuseFailAlloc_4957_;
goto v_reusejp_4955_;
}
v_reusejp_4955_:
{
return v___x_4956_;
}
}
}
}
else
{
lean_object* v_a_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_4966_; 
lean_dec(v_val_4919_);
lean_dec(v_structId_4912_);
lean_dec(v_id_4911_);
lean_del_object(v___x_4907_);
lean_dec(v_fst_4905_);
lean_dec_ref(v_b_4885_);
lean_dec_ref(v_a_4884_);
v_a_4959_ = lean_ctor_get(v___x_4920_, 0);
v_isSharedCheck_4966_ = !lean_is_exclusive(v___x_4920_);
if (v_isSharedCheck_4966_ == 0)
{
v___x_4961_ = v___x_4920_;
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_a_4959_);
lean_dec(v___x_4920_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v___x_4964_; 
if (v_isShared_4962_ == 0)
{
v___x_4964_ = v___x_4961_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4965_; 
v_reuseFailAlloc_4965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4965_, 0, v_a_4959_);
v___x_4964_ = v_reuseFailAlloc_4965_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
return v___x_4964_;
}
}
}
}
else
{
lean_object* v___x_4967_; lean_object* v___x_4969_; 
lean_dec(v_a_4915_);
lean_dec(v_structId_4912_);
lean_dec(v_id_4911_);
lean_del_object(v___x_4907_);
lean_dec(v_fst_4905_);
lean_dec_ref(v_b_4885_);
lean_dec_ref(v_a_4884_);
v___x_4967_ = lean_box(0);
if (v_isShared_4918_ == 0)
{
lean_ctor_set(v___x_4917_, 0, v___x_4967_);
v___x_4969_ = v___x_4917_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v___x_4967_);
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
lean_dec(v_structId_4912_);
lean_dec(v_id_4911_);
lean_del_object(v___x_4907_);
lean_dec(v_fst_4905_);
lean_dec_ref(v_b_4885_);
lean_dec_ref(v_a_4884_);
v_a_4972_ = lean_ctor_get(v___x_4914_, 0);
v_isSharedCheck_4979_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4979_ == 0)
{
v___x_4974_ = v___x_4914_;
v_isShared_4975_ = v_isSharedCheck_4979_;
goto v_resetjp_4973_;
}
else
{
lean_inc(v_a_4972_);
lean_dec(v___x_4914_);
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
lean_del_object(v___x_4907_);
lean_dec(v_fst_4905_);
lean_dec(v_fst_4902_);
lean_dec(v_a_4899_);
lean_dec_ref(v_b_4885_);
lean_dec_ref(v_a_4884_);
v_a_4980_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4987_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4987_ == 0)
{
v___x_4982_ = v___x_4909_;
v_isShared_4983_ = v_isSharedCheck_4987_;
goto v_resetjp_4981_;
}
else
{
lean_inc(v_a_4980_);
lean_dec(v___x_4909_);
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
else
{
lean_object* v_a_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_4997_; 
lean_dec(v_fst_4902_);
lean_dec(v_a_4899_);
lean_dec_ref(v_b_4885_);
lean_dec_ref(v_a_4884_);
v_a_4990_ = lean_ctor_get(v___x_4903_, 0);
v_isSharedCheck_4997_ = !lean_is_exclusive(v___x_4903_);
if (v_isSharedCheck_4997_ == 0)
{
v___x_4992_ = v___x_4903_;
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_a_4990_);
lean_dec(v___x_4903_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
lean_object* v___x_4995_; 
if (v_isShared_4993_ == 0)
{
v___x_4995_ = v___x_4992_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4990_);
v___x_4995_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
return v___x_4995_;
}
}
}
}
else
{
lean_object* v_a_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5005_; 
lean_dec(v_a_4899_);
lean_dec_ref(v_b_4885_);
lean_dec_ref(v_a_4884_);
v_a_4998_ = lean_ctor_get(v___x_4900_, 0);
v_isSharedCheck_5005_ = !lean_is_exclusive(v___x_4900_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_5000_ = v___x_4900_;
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_a_4998_);
lean_dec(v___x_4900_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
lean_object* v___x_5003_; 
if (v_isShared_5001_ == 0)
{
v___x_5003_ = v___x_5000_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v_a_4998_);
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
lean_dec_ref(v_b_4885_);
lean_dec_ref(v_a_4884_);
v_a_5006_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_5013_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_5013_ == 0)
{
v___x_5008_ = v___x_4898_;
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_a_5006_);
lean_dec(v___x_4898_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27___boxed(lean_object* v_a_5014_, lean_object* v_b_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_){
_start:
{
lean_object* v_res_5028_; 
v_res_5028_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5014_, v_b_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_);
lean_dec(v_a_5026_);
lean_dec_ref(v_a_5025_);
lean_dec(v_a_5024_);
lean_dec_ref(v_a_5023_);
lean_dec(v_a_5022_);
lean_dec_ref(v_a_5021_);
lean_dec(v_a_5020_);
lean_dec_ref(v_a_5019_);
lean_dec(v_a_5018_);
lean_dec(v_a_5017_);
lean_dec(v_a_5016_);
return v_res_5028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(lean_object* v_a_5029_, lean_object* v_b_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_){
_start:
{
lean_object* v___x_5043_; 
v___x_5043_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_);
if (lean_obj_tag(v___x_5043_) == 0)
{
lean_object* v_a_5044_; lean_object* v___x_5045_; 
v_a_5044_ = lean_ctor_get(v___x_5043_, 0);
lean_inc(v_a_5044_);
lean_dec_ref(v___x_5043_);
lean_inc_ref(v_a_5029_);
v___x_5045_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5029_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_);
if (lean_obj_tag(v___x_5045_) == 0)
{
lean_object* v_a_5046_; lean_object* v_fst_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5143_; 
v_a_5046_ = lean_ctor_get(v___x_5045_, 0);
lean_inc(v_a_5046_);
lean_dec_ref(v___x_5045_);
v_fst_5047_ = lean_ctor_get(v_a_5046_, 0);
v_isSharedCheck_5143_ = !lean_is_exclusive(v_a_5046_);
if (v_isSharedCheck_5143_ == 0)
{
lean_object* v_unused_5144_; 
v_unused_5144_ = lean_ctor_get(v_a_5046_, 1);
lean_dec(v_unused_5144_);
v___x_5049_ = v_a_5046_;
v_isShared_5050_ = v_isSharedCheck_5143_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_fst_5047_);
lean_dec(v_a_5046_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5143_;
goto v_resetjp_5048_;
}
v_resetjp_5048_:
{
lean_object* v___x_5051_; 
lean_inc_ref(v_b_5030_);
v___x_5051_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5030_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_);
if (lean_obj_tag(v___x_5051_) == 0)
{
lean_object* v_a_5052_; lean_object* v_fst_5053_; lean_object* v___x_5055_; uint8_t v_isShared_5056_; uint8_t v_isSharedCheck_5133_; 
v_a_5052_ = lean_ctor_get(v___x_5051_, 0);
lean_inc(v_a_5052_);
lean_dec_ref(v___x_5051_);
v_fst_5053_ = lean_ctor_get(v_a_5052_, 0);
v_isSharedCheck_5133_ = !lean_is_exclusive(v_a_5052_);
if (v_isSharedCheck_5133_ == 0)
{
lean_object* v_unused_5134_; 
v_unused_5134_ = lean_ctor_get(v_a_5052_, 1);
lean_dec(v_unused_5134_);
v___x_5055_ = v_a_5052_;
v_isShared_5056_ = v_isSharedCheck_5133_;
goto v_resetjp_5054_;
}
else
{
lean_inc(v_fst_5053_);
lean_dec(v_a_5052_);
v___x_5055_ = lean_box(0);
v_isShared_5056_ = v_isSharedCheck_5133_;
goto v_resetjp_5054_;
}
v_resetjp_5054_:
{
lean_object* v___x_5057_; 
v___x_5057_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5029_, v_a_5032_);
if (lean_obj_tag(v___x_5057_) == 0)
{
lean_object* v_a_5058_; lean_object* v_id_5059_; lean_object* v_structId_5060_; uint8_t v___x_5061_; lean_object* v___x_5062_; 
v_a_5058_ = lean_ctor_get(v___x_5057_, 0);
lean_inc(v_a_5058_);
lean_dec_ref(v___x_5057_);
v_id_5059_ = lean_ctor_get(v_a_5044_, 0);
lean_inc(v_id_5059_);
v_structId_5060_ = lean_ctor_get(v_a_5044_, 1);
lean_inc(v_structId_5060_);
lean_dec(v_a_5044_);
v___x_5061_ = 0;
v___x_5062_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5047_, v___x_5061_, v_a_5058_, v_structId_5060_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v_a_5063_; lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5116_; 
v_a_5063_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5065_ = v___x_5062_;
v_isShared_5066_ = v_isSharedCheck_5116_;
goto v_resetjp_5064_;
}
else
{
lean_inc(v_a_5063_);
lean_dec(v___x_5062_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5116_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
if (lean_obj_tag(v_a_5063_) == 1)
{
lean_object* v_val_5067_; lean_object* v___x_5068_; 
lean_del_object(v___x_5065_);
v_val_5067_ = lean_ctor_get(v_a_5063_, 0);
lean_inc(v_val_5067_);
lean_dec_ref(v_a_5063_);
v___x_5068_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5030_, v_a_5032_);
if (lean_obj_tag(v___x_5068_) == 0)
{
lean_object* v_a_5069_; lean_object* v___x_5070_; 
v_a_5069_ = lean_ctor_get(v___x_5068_, 0);
lean_inc(v_a_5069_);
lean_dec_ref(v___x_5068_);
v___x_5070_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5053_, v___x_5061_, v_a_5069_, v_structId_5060_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_);
if (lean_obj_tag(v___x_5070_) == 0)
{
lean_object* v_a_5071_; lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5095_; 
v_a_5071_ = lean_ctor_get(v___x_5070_, 0);
v_isSharedCheck_5095_ = !lean_is_exclusive(v___x_5070_);
if (v_isSharedCheck_5095_ == 0)
{
v___x_5073_ = v___x_5070_;
v_isShared_5074_ = v_isSharedCheck_5095_;
goto v_resetjp_5072_;
}
else
{
lean_inc(v_a_5071_);
lean_dec(v___x_5070_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5095_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
if (lean_obj_tag(v_a_5071_) == 1)
{
lean_object* v_val_5075_; lean_object* v___x_5077_; 
v_val_5075_ = lean_ctor_get(v_a_5071_, 0);
lean_inc_n(v_val_5075_, 2);
lean_dec_ref(v_a_5071_);
lean_inc(v_val_5067_);
if (v_isShared_5056_ == 0)
{
lean_ctor_set_tag(v___x_5055_, 3);
lean_ctor_set(v___x_5055_, 1, v_val_5075_);
lean_ctor_set(v___x_5055_, 0, v_val_5067_);
v___x_5077_ = v___x_5055_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5090_; 
v_reuseFailAlloc_5090_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5090_, 0, v_val_5067_);
lean_ctor_set(v_reuseFailAlloc_5090_, 1, v_val_5075_);
v___x_5077_ = v_reuseFailAlloc_5090_;
goto v_reusejp_5076_;
}
v_reusejp_5076_:
{
lean_object* v___x_5078_; lean_object* v___x_5079_; uint8_t v___x_5080_; 
v___x_5078_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5077_);
v___x_5079_ = lean_box(0);
v___x_5080_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_5078_, v___x_5079_);
if (v___x_5080_ == 0)
{
lean_object* v___x_5081_; lean_object* v___x_5083_; 
lean_del_object(v___x_5073_);
v___x_5081_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5081_, 0, v_a_5029_);
lean_ctor_set(v___x_5081_, 1, v_b_5030_);
lean_ctor_set(v___x_5081_, 2, v_id_5059_);
lean_ctor_set(v___x_5081_, 3, v_val_5067_);
lean_ctor_set(v___x_5081_, 4, v_val_5075_);
if (v_isShared_5050_ == 0)
{
lean_ctor_set(v___x_5049_, 1, v___x_5081_);
lean_ctor_set(v___x_5049_, 0, v___x_5078_);
v___x_5083_ = v___x_5049_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v___x_5078_);
lean_ctor_set(v_reuseFailAlloc_5085_, 1, v___x_5081_);
v___x_5083_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
lean_object* v___x_5084_; 
v___x_5084_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_5083_, v_structId_5060_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_);
lean_dec(v_structId_5060_);
return v___x_5084_;
}
}
else
{
lean_object* v___x_5086_; lean_object* v___x_5088_; 
lean_dec(v___x_5078_);
lean_dec(v_val_5075_);
lean_dec(v_val_5067_);
lean_dec(v_structId_5060_);
lean_dec(v_id_5059_);
lean_del_object(v___x_5049_);
lean_dec_ref(v_b_5030_);
lean_dec_ref(v_a_5029_);
v___x_5086_ = lean_box(0);
if (v_isShared_5074_ == 0)
{
lean_ctor_set(v___x_5073_, 0, v___x_5086_);
v___x_5088_ = v___x_5073_;
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
lean_object* v___x_5091_; lean_object* v___x_5093_; 
lean_dec(v_a_5071_);
lean_dec(v_val_5067_);
lean_dec(v_structId_5060_);
lean_dec(v_id_5059_);
lean_del_object(v___x_5055_);
lean_del_object(v___x_5049_);
lean_dec_ref(v_b_5030_);
lean_dec_ref(v_a_5029_);
v___x_5091_ = lean_box(0);
if (v_isShared_5074_ == 0)
{
lean_ctor_set(v___x_5073_, 0, v___x_5091_);
v___x_5093_ = v___x_5073_;
goto v_reusejp_5092_;
}
else
{
lean_object* v_reuseFailAlloc_5094_; 
v_reuseFailAlloc_5094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5094_, 0, v___x_5091_);
v___x_5093_ = v_reuseFailAlloc_5094_;
goto v_reusejp_5092_;
}
v_reusejp_5092_:
{
return v___x_5093_;
}
}
}
}
else
{
lean_object* v_a_5096_; lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5103_; 
lean_dec(v_val_5067_);
lean_dec(v_structId_5060_);
lean_dec(v_id_5059_);
lean_del_object(v___x_5055_);
lean_del_object(v___x_5049_);
lean_dec_ref(v_b_5030_);
lean_dec_ref(v_a_5029_);
v_a_5096_ = lean_ctor_get(v___x_5070_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_5070_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5098_ = v___x_5070_;
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_a_5096_);
lean_dec(v___x_5070_);
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
lean_dec(v_val_5067_);
lean_dec(v_structId_5060_);
lean_dec(v_id_5059_);
lean_del_object(v___x_5055_);
lean_dec(v_fst_5053_);
lean_del_object(v___x_5049_);
lean_dec_ref(v_b_5030_);
lean_dec_ref(v_a_5029_);
v_a_5104_ = lean_ctor_get(v___x_5068_, 0);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_5068_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5106_ = v___x_5068_;
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
else
{
lean_inc(v_a_5104_);
lean_dec(v___x_5068_);
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
else
{
lean_object* v___x_5112_; lean_object* v___x_5114_; 
lean_dec(v_a_5063_);
lean_dec(v_structId_5060_);
lean_dec(v_id_5059_);
lean_del_object(v___x_5055_);
lean_dec(v_fst_5053_);
lean_del_object(v___x_5049_);
lean_dec_ref(v_b_5030_);
lean_dec_ref(v_a_5029_);
v___x_5112_ = lean_box(0);
if (v_isShared_5066_ == 0)
{
lean_ctor_set(v___x_5065_, 0, v___x_5112_);
v___x_5114_ = v___x_5065_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v___x_5112_);
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
else
{
lean_object* v_a_5117_; lean_object* v___x_5119_; uint8_t v_isShared_5120_; uint8_t v_isSharedCheck_5124_; 
lean_dec(v_structId_5060_);
lean_dec(v_id_5059_);
lean_del_object(v___x_5055_);
lean_dec(v_fst_5053_);
lean_del_object(v___x_5049_);
lean_dec_ref(v_b_5030_);
lean_dec_ref(v_a_5029_);
v_a_5117_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5124_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5124_ == 0)
{
v___x_5119_ = v___x_5062_;
v_isShared_5120_ = v_isSharedCheck_5124_;
goto v_resetjp_5118_;
}
else
{
lean_inc(v_a_5117_);
lean_dec(v___x_5062_);
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
lean_object* v_a_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5132_; 
lean_del_object(v___x_5055_);
lean_dec(v_fst_5053_);
lean_del_object(v___x_5049_);
lean_dec(v_fst_5047_);
lean_dec(v_a_5044_);
lean_dec_ref(v_b_5030_);
lean_dec_ref(v_a_5029_);
v_a_5125_ = lean_ctor_get(v___x_5057_, 0);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5132_ == 0)
{
v___x_5127_ = v___x_5057_;
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_a_5125_);
lean_dec(v___x_5057_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
lean_object* v___x_5130_; 
if (v_isShared_5128_ == 0)
{
v___x_5130_ = v___x_5127_;
goto v_reusejp_5129_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_a_5125_);
v___x_5130_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5129_;
}
v_reusejp_5129_:
{
return v___x_5130_;
}
}
}
}
}
else
{
lean_object* v_a_5135_; lean_object* v___x_5137_; uint8_t v_isShared_5138_; uint8_t v_isSharedCheck_5142_; 
lean_del_object(v___x_5049_);
lean_dec(v_fst_5047_);
lean_dec(v_a_5044_);
lean_dec_ref(v_b_5030_);
lean_dec_ref(v_a_5029_);
v_a_5135_ = lean_ctor_get(v___x_5051_, 0);
v_isSharedCheck_5142_ = !lean_is_exclusive(v___x_5051_);
if (v_isSharedCheck_5142_ == 0)
{
v___x_5137_ = v___x_5051_;
v_isShared_5138_ = v_isSharedCheck_5142_;
goto v_resetjp_5136_;
}
else
{
lean_inc(v_a_5135_);
lean_dec(v___x_5051_);
v___x_5137_ = lean_box(0);
v_isShared_5138_ = v_isSharedCheck_5142_;
goto v_resetjp_5136_;
}
v_resetjp_5136_:
{
lean_object* v___x_5140_; 
if (v_isShared_5138_ == 0)
{
v___x_5140_ = v___x_5137_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5141_; 
v_reuseFailAlloc_5141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5141_, 0, v_a_5135_);
v___x_5140_ = v_reuseFailAlloc_5141_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
return v___x_5140_;
}
}
}
}
}
else
{
lean_object* v_a_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5152_; 
lean_dec(v_a_5044_);
lean_dec_ref(v_b_5030_);
lean_dec_ref(v_a_5029_);
v_a_5145_ = lean_ctor_get(v___x_5045_, 0);
v_isSharedCheck_5152_ = !lean_is_exclusive(v___x_5045_);
if (v_isSharedCheck_5152_ == 0)
{
v___x_5147_ = v___x_5045_;
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
else
{
lean_inc(v_a_5145_);
lean_dec(v___x_5045_);
v___x_5147_ = lean_box(0);
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
v_resetjp_5146_:
{
lean_object* v___x_5150_; 
if (v_isShared_5148_ == 0)
{
v___x_5150_ = v___x_5147_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_a_5145_);
v___x_5150_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
return v___x_5150_;
}
}
}
}
else
{
lean_object* v_a_5153_; lean_object* v___x_5155_; uint8_t v_isShared_5156_; uint8_t v_isSharedCheck_5160_; 
lean_dec_ref(v_b_5030_);
lean_dec_ref(v_a_5029_);
v_a_5153_ = lean_ctor_get(v___x_5043_, 0);
v_isSharedCheck_5160_ = !lean_is_exclusive(v___x_5043_);
if (v_isSharedCheck_5160_ == 0)
{
v___x_5155_ = v___x_5043_;
v_isShared_5156_ = v_isSharedCheck_5160_;
goto v_resetjp_5154_;
}
else
{
lean_inc(v_a_5153_);
lean_dec(v___x_5043_);
v___x_5155_ = lean_box(0);
v_isShared_5156_ = v_isSharedCheck_5160_;
goto v_resetjp_5154_;
}
v_resetjp_5154_:
{
lean_object* v___x_5158_; 
if (v_isShared_5156_ == 0)
{
v___x_5158_ = v___x_5155_;
goto v_reusejp_5157_;
}
else
{
lean_object* v_reuseFailAlloc_5159_; 
v_reuseFailAlloc_5159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5159_, 0, v_a_5153_);
v___x_5158_ = v_reuseFailAlloc_5159_;
goto v_reusejp_5157_;
}
v_reusejp_5157_:
{
return v___x_5158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq___boxed(lean_object* v_a_5161_, lean_object* v_b_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_){
_start:
{
lean_object* v_res_5175_; 
v_res_5175_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5161_, v_b_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_);
lean_dec(v_a_5173_);
lean_dec_ref(v_a_5172_);
lean_dec(v_a_5171_);
lean_dec_ref(v_a_5170_);
lean_dec(v_a_5169_);
lean_dec_ref(v_a_5168_);
lean_dec(v_a_5167_);
lean_dec_ref(v_a_5166_);
lean_dec(v_a_5165_);
lean_dec(v_a_5164_);
lean_dec(v_a_5163_);
return v_res_5175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq(lean_object* v_a_5176_, lean_object* v_b_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_, lean_object* v_a_5181_, lean_object* v_a_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_){
_start:
{
uint8_t v___x_5189_; 
v___x_5189_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_5176_, v_b_5177_);
if (v___x_5189_ == 0)
{
lean_object* v___x_5190_; 
v___x_5190_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5176_, v_b_5177_, v_a_5178_, v_a_5186_);
if (lean_obj_tag(v___x_5190_) == 0)
{
lean_object* v_a_5191_; 
v_a_5191_ = lean_ctor_get(v___x_5190_, 0);
lean_inc(v_a_5191_);
lean_dec_ref(v___x_5190_);
if (lean_obj_tag(v_a_5191_) == 1)
{
lean_object* v_val_5192_; lean_object* v___x_5193_; 
v_val_5192_ = lean_ctor_get(v_a_5191_, 0);
lean_inc(v_val_5192_);
lean_dec_ref(v_a_5191_);
v___x_5193_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_val_5192_, v_a_5178_, v_a_5179_, v_a_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_);
if (lean_obj_tag(v___x_5193_) == 0)
{
lean_object* v_a_5194_; uint8_t v___x_5195_; 
v_a_5194_ = lean_ctor_get(v___x_5193_, 0);
lean_inc(v_a_5194_);
lean_dec_ref(v___x_5193_);
v___x_5195_ = lean_unbox(v_a_5194_);
lean_dec(v_a_5194_);
if (v___x_5195_ == 0)
{
lean_object* v___x_5196_; 
v___x_5196_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5192_, v_a_5178_, v_a_5179_, v_a_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_);
if (lean_obj_tag(v___x_5196_) == 0)
{
lean_object* v_a_5197_; uint8_t v___x_5198_; 
v_a_5197_ = lean_ctor_get(v___x_5196_, 0);
lean_inc(v_a_5197_);
lean_dec_ref(v___x_5196_);
v___x_5198_ = lean_unbox(v_a_5197_);
lean_dec(v_a_5197_);
if (v___x_5198_ == 0)
{
lean_object* v___x_5199_; 
v___x_5199_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_5176_, v_b_5177_, v_val_5192_, v_a_5178_, v_a_5179_, v_a_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_);
lean_dec(v_val_5192_);
return v___x_5199_;
}
else
{
lean_object* v___x_5200_; 
lean_dec(v_val_5192_);
v___x_5200_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_5176_, v_b_5177_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_);
return v___x_5200_;
}
}
else
{
lean_object* v_a_5201_; lean_object* v___x_5203_; uint8_t v_isShared_5204_; uint8_t v_isSharedCheck_5208_; 
lean_dec(v_val_5192_);
lean_dec_ref(v_b_5177_);
lean_dec_ref(v_a_5176_);
v_a_5201_ = lean_ctor_get(v___x_5196_, 0);
v_isSharedCheck_5208_ = !lean_is_exclusive(v___x_5196_);
if (v_isSharedCheck_5208_ == 0)
{
v___x_5203_ = v___x_5196_;
v_isShared_5204_ = v_isSharedCheck_5208_;
goto v_resetjp_5202_;
}
else
{
lean_inc(v_a_5201_);
lean_dec(v___x_5196_);
v___x_5203_ = lean_box(0);
v_isShared_5204_ = v_isSharedCheck_5208_;
goto v_resetjp_5202_;
}
v_resetjp_5202_:
{
lean_object* v___x_5206_; 
if (v_isShared_5204_ == 0)
{
v___x_5206_ = v___x_5203_;
goto v_reusejp_5205_;
}
else
{
lean_object* v_reuseFailAlloc_5207_; 
v_reuseFailAlloc_5207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5207_, 0, v_a_5201_);
v___x_5206_ = v_reuseFailAlloc_5207_;
goto v_reusejp_5205_;
}
v_reusejp_5205_:
{
return v___x_5206_;
}
}
}
}
else
{
lean_object* v___x_5209_; 
v___x_5209_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5192_, v_a_5178_, v_a_5179_, v_a_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_);
if (lean_obj_tag(v___x_5209_) == 0)
{
lean_object* v_a_5210_; uint8_t v___x_5211_; 
v_a_5210_ = lean_ctor_get(v___x_5209_, 0);
lean_inc(v_a_5210_);
lean_dec_ref(v___x_5209_);
v___x_5211_ = lean_unbox(v_a_5210_);
lean_dec(v_a_5210_);
if (v___x_5211_ == 0)
{
lean_object* v___x_5212_; 
v___x_5212_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_5176_, v_b_5177_, v_val_5192_, v_a_5178_, v_a_5179_, v_a_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_);
lean_dec(v_val_5192_);
return v___x_5212_;
}
else
{
lean_object* v___x_5213_; 
v___x_5213_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_5176_, v_b_5177_, v_val_5192_, v_a_5178_, v_a_5179_, v_a_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_);
lean_dec(v_val_5192_);
return v___x_5213_;
}
}
else
{
lean_object* v_a_5214_; lean_object* v___x_5216_; uint8_t v_isShared_5217_; uint8_t v_isSharedCheck_5221_; 
lean_dec(v_val_5192_);
lean_dec_ref(v_b_5177_);
lean_dec_ref(v_a_5176_);
v_a_5214_ = lean_ctor_get(v___x_5209_, 0);
v_isSharedCheck_5221_ = !lean_is_exclusive(v___x_5209_);
if (v_isSharedCheck_5221_ == 0)
{
v___x_5216_ = v___x_5209_;
v_isShared_5217_ = v_isSharedCheck_5221_;
goto v_resetjp_5215_;
}
else
{
lean_inc(v_a_5214_);
lean_dec(v___x_5209_);
v___x_5216_ = lean_box(0);
v_isShared_5217_ = v_isSharedCheck_5221_;
goto v_resetjp_5215_;
}
v_resetjp_5215_:
{
lean_object* v___x_5219_; 
if (v_isShared_5217_ == 0)
{
v___x_5219_ = v___x_5216_;
goto v_reusejp_5218_;
}
else
{
lean_object* v_reuseFailAlloc_5220_; 
v_reuseFailAlloc_5220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5220_, 0, v_a_5214_);
v___x_5219_ = v_reuseFailAlloc_5220_;
goto v_reusejp_5218_;
}
v_reusejp_5218_:
{
return v___x_5219_;
}
}
}
}
}
else
{
lean_object* v_a_5222_; lean_object* v___x_5224_; uint8_t v_isShared_5225_; uint8_t v_isSharedCheck_5229_; 
lean_dec(v_val_5192_);
lean_dec_ref(v_b_5177_);
lean_dec_ref(v_a_5176_);
v_a_5222_ = lean_ctor_get(v___x_5193_, 0);
v_isSharedCheck_5229_ = !lean_is_exclusive(v___x_5193_);
if (v_isSharedCheck_5229_ == 0)
{
v___x_5224_ = v___x_5193_;
v_isShared_5225_ = v_isSharedCheck_5229_;
goto v_resetjp_5223_;
}
else
{
lean_inc(v_a_5222_);
lean_dec(v___x_5193_);
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
lean_object* v___x_5230_; 
lean_dec(v_a_5191_);
v___x_5230_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5176_, v_b_5177_, v_a_5178_, v_a_5186_);
if (lean_obj_tag(v___x_5230_) == 0)
{
lean_object* v_a_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5253_; 
v_a_5231_ = lean_ctor_get(v___x_5230_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v___x_5230_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_5233_ = v___x_5230_;
v_isShared_5234_ = v_isSharedCheck_5253_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_a_5231_);
lean_dec(v___x_5230_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5253_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
if (lean_obj_tag(v_a_5231_) == 1)
{
lean_object* v_val_5235_; lean_object* v___x_5236_; 
lean_del_object(v___x_5233_);
v_val_5235_ = lean_ctor_get(v_a_5231_, 0);
lean_inc(v_val_5235_);
lean_dec_ref(v_a_5231_);
v___x_5236_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_5235_, v_a_5178_, v_a_5179_, v_a_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_);
if (lean_obj_tag(v___x_5236_) == 0)
{
lean_object* v_a_5237_; lean_object* v_orderedAddInst_x3f_5238_; 
v_a_5237_ = lean_ctor_get(v___x_5236_, 0);
lean_inc(v_a_5237_);
lean_dec_ref(v___x_5236_);
v_orderedAddInst_x3f_5238_ = lean_ctor_get(v_a_5237_, 9);
lean_inc(v_orderedAddInst_x3f_5238_);
lean_dec(v_a_5237_);
if (lean_obj_tag(v_orderedAddInst_x3f_5238_) == 0)
{
lean_object* v___x_5239_; 
v___x_5239_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5176_, v_b_5177_, v_val_5235_, v_a_5178_, v_a_5179_, v_a_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_);
lean_dec(v_val_5235_);
return v___x_5239_;
}
else
{
lean_object* v___x_5240_; 
lean_dec_ref(v_orderedAddInst_x3f_5238_);
v___x_5240_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5176_, v_b_5177_, v_val_5235_, v_a_5178_, v_a_5179_, v_a_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_);
lean_dec(v_val_5235_);
return v___x_5240_;
}
}
else
{
lean_object* v_a_5241_; lean_object* v___x_5243_; uint8_t v_isShared_5244_; uint8_t v_isSharedCheck_5248_; 
lean_dec(v_val_5235_);
lean_dec_ref(v_b_5177_);
lean_dec_ref(v_a_5176_);
v_a_5241_ = lean_ctor_get(v___x_5236_, 0);
v_isSharedCheck_5248_ = !lean_is_exclusive(v___x_5236_);
if (v_isSharedCheck_5248_ == 0)
{
v___x_5243_ = v___x_5236_;
v_isShared_5244_ = v_isSharedCheck_5248_;
goto v_resetjp_5242_;
}
else
{
lean_inc(v_a_5241_);
lean_dec(v___x_5236_);
v___x_5243_ = lean_box(0);
v_isShared_5244_ = v_isSharedCheck_5248_;
goto v_resetjp_5242_;
}
v_resetjp_5242_:
{
lean_object* v___x_5246_; 
if (v_isShared_5244_ == 0)
{
v___x_5246_ = v___x_5243_;
goto v_reusejp_5245_;
}
else
{
lean_object* v_reuseFailAlloc_5247_; 
v_reuseFailAlloc_5247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5247_, 0, v_a_5241_);
v___x_5246_ = v_reuseFailAlloc_5247_;
goto v_reusejp_5245_;
}
v_reusejp_5245_:
{
return v___x_5246_;
}
}
}
}
else
{
lean_object* v___x_5249_; lean_object* v___x_5251_; 
lean_dec(v_a_5231_);
lean_dec_ref(v_b_5177_);
lean_dec_ref(v_a_5176_);
v___x_5249_ = lean_box(0);
if (v_isShared_5234_ == 0)
{
lean_ctor_set(v___x_5233_, 0, v___x_5249_);
v___x_5251_ = v___x_5233_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v___x_5249_);
v___x_5251_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
return v___x_5251_;
}
}
}
}
else
{
lean_object* v_a_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5261_; 
lean_dec_ref(v_b_5177_);
lean_dec_ref(v_a_5176_);
v_a_5254_ = lean_ctor_get(v___x_5230_, 0);
v_isSharedCheck_5261_ = !lean_is_exclusive(v___x_5230_);
if (v_isSharedCheck_5261_ == 0)
{
v___x_5256_ = v___x_5230_;
v_isShared_5257_ = v_isSharedCheck_5261_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_a_5254_);
lean_dec(v___x_5230_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5261_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v___x_5259_; 
if (v_isShared_5257_ == 0)
{
v___x_5259_ = v___x_5256_;
goto v_reusejp_5258_;
}
else
{
lean_object* v_reuseFailAlloc_5260_; 
v_reuseFailAlloc_5260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5260_, 0, v_a_5254_);
v___x_5259_ = v_reuseFailAlloc_5260_;
goto v_reusejp_5258_;
}
v_reusejp_5258_:
{
return v___x_5259_;
}
}
}
}
}
else
{
lean_object* v_a_5262_; lean_object* v___x_5264_; uint8_t v_isShared_5265_; uint8_t v_isSharedCheck_5269_; 
lean_dec_ref(v_b_5177_);
lean_dec_ref(v_a_5176_);
v_a_5262_ = lean_ctor_get(v___x_5190_, 0);
v_isSharedCheck_5269_ = !lean_is_exclusive(v___x_5190_);
if (v_isSharedCheck_5269_ == 0)
{
v___x_5264_ = v___x_5190_;
v_isShared_5265_ = v_isSharedCheck_5269_;
goto v_resetjp_5263_;
}
else
{
lean_inc(v_a_5262_);
lean_dec(v___x_5190_);
v___x_5264_ = lean_box(0);
v_isShared_5265_ = v_isSharedCheck_5269_;
goto v_resetjp_5263_;
}
v_resetjp_5263_:
{
lean_object* v___x_5267_; 
if (v_isShared_5265_ == 0)
{
v___x_5267_ = v___x_5264_;
goto v_reusejp_5266_;
}
else
{
lean_object* v_reuseFailAlloc_5268_; 
v_reuseFailAlloc_5268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5268_, 0, v_a_5262_);
v___x_5267_ = v_reuseFailAlloc_5268_;
goto v_reusejp_5266_;
}
v_reusejp_5266_:
{
return v___x_5267_;
}
}
}
}
else
{
lean_object* v___x_5270_; lean_object* v___x_5271_; 
lean_dec_ref(v_b_5177_);
lean_dec_ref(v_a_5176_);
v___x_5270_ = lean_box(0);
v___x_5271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5271_, 0, v___x_5270_);
return v___x_5271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed(lean_object* v_a_5272_, lean_object* v_b_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_, lean_object* v_a_5276_, lean_object* v_a_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_, lean_object* v_a_5281_, lean_object* v_a_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_){
_start:
{
lean_object* v_res_5285_; 
v_res_5285_ = l_Lean_Meta_Grind_Arith_Linear_processNewEq(v_a_5272_, v_b_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_, v_a_5282_, v_a_5283_);
lean_dec(v_a_5283_);
lean_dec_ref(v_a_5282_);
lean_dec(v_a_5281_);
lean_dec_ref(v_a_5280_);
lean_dec(v_a_5279_);
lean_dec_ref(v_a_5278_);
lean_dec(v_a_5277_);
lean_dec_ref(v_a_5276_);
lean_dec(v_a_5275_);
lean_dec(v_a_5274_);
return v_res_5285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object* v_a_5286_, lean_object* v_b_5287_, lean_object* v_a_5288_, lean_object* v_a_5289_, lean_object* v_a_5290_, lean_object* v_a_5291_, lean_object* v_a_5292_, lean_object* v_a_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_, lean_object* v_a_5298_){
_start:
{
uint8_t v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; 
v___x_5300_ = 0;
v___x_5301_ = lean_unsigned_to_nat(0u);
v___x_5302_ = lean_box(v___x_5300_);
lean_inc_ref(v_a_5286_);
v___x_5303_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5303_, 0, v_a_5286_);
lean_closure_set(v___x_5303_, 1, v___x_5302_);
lean_closure_set(v___x_5303_, 2, v___x_5301_);
v___x_5304_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5303_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_);
if (lean_obj_tag(v___x_5304_) == 0)
{
lean_object* v_a_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5406_; 
v_a_5305_ = lean_ctor_get(v___x_5304_, 0);
v_isSharedCheck_5406_ = !lean_is_exclusive(v___x_5304_);
if (v_isSharedCheck_5406_ == 0)
{
v___x_5307_ = v___x_5304_;
v_isShared_5308_ = v_isSharedCheck_5406_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_a_5305_);
lean_dec(v___x_5304_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5406_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
if (lean_obj_tag(v_a_5305_) == 1)
{
lean_object* v_val_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; 
lean_del_object(v___x_5307_);
v_val_5309_ = lean_ctor_get(v_a_5305_, 0);
lean_inc(v_val_5309_);
lean_dec_ref(v_a_5305_);
v___x_5310_ = lean_box(v___x_5300_);
lean_inc_ref(v_b_5287_);
v___x_5311_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5311_, 0, v_b_5287_);
lean_closure_set(v___x_5311_, 1, v___x_5310_);
lean_closure_set(v___x_5311_, 2, v___x_5301_);
v___x_5312_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5311_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_);
if (lean_obj_tag(v___x_5312_) == 0)
{
lean_object* v_a_5313_; lean_object* v___x_5315_; uint8_t v_isShared_5316_; uint8_t v_isSharedCheck_5393_; 
v_a_5313_ = lean_ctor_get(v___x_5312_, 0);
v_isSharedCheck_5393_ = !lean_is_exclusive(v___x_5312_);
if (v_isSharedCheck_5393_ == 0)
{
v___x_5315_ = v___x_5312_;
v_isShared_5316_ = v_isSharedCheck_5393_;
goto v_resetjp_5314_;
}
else
{
lean_inc(v_a_5313_);
lean_dec(v___x_5312_);
v___x_5315_ = lean_box(0);
v_isShared_5316_ = v_isSharedCheck_5393_;
goto v_resetjp_5314_;
}
v_resetjp_5314_:
{
if (lean_obj_tag(v_a_5313_) == 1)
{
lean_object* v_val_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; 
lean_del_object(v___x_5315_);
v_val_5317_ = lean_ctor_get(v_a_5313_, 0);
lean_inc_n(v_val_5317_, 2);
lean_dec_ref(v_a_5313_);
lean_inc(v_val_5309_);
v___x_5318_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_5318_, 0, v_val_5309_);
lean_ctor_set(v___x_5318_, 1, v_val_5317_);
v___x_5319_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_5318_);
lean_inc_ref(v_b_5287_);
lean_inc_ref(v_a_5286_);
v___x_5320_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5320_, 0, v_a_5286_);
lean_ctor_set(v___x_5320_, 1, v_b_5287_);
lean_ctor_set(v___x_5320_, 2, v_val_5309_);
lean_ctor_set(v___x_5320_, 3, v_val_5317_);
v___x_5321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5321_, 0, v___x_5319_);
lean_ctor_set(v___x_5321_, 1, v___x_5320_);
v___x_5322_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(v___x_5321_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_);
if (lean_obj_tag(v___x_5322_) == 0)
{
lean_object* v_a_5323_; lean_object* v___x_5324_; 
v_a_5323_ = lean_ctor_get(v___x_5322_, 0);
lean_inc(v_a_5323_);
lean_dec_ref(v___x_5322_);
v___x_5324_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5286_, v_a_5289_);
lean_dec_ref(v_a_5286_);
if (lean_obj_tag(v___x_5324_) == 0)
{
lean_object* v_a_5325_; lean_object* v___x_5326_; 
v_a_5325_ = lean_ctor_get(v___x_5324_, 0);
lean_inc(v_a_5325_);
lean_dec_ref(v___x_5324_);
v___x_5326_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5287_, v_a_5289_);
lean_dec_ref(v_b_5287_);
if (lean_obj_tag(v___x_5326_) == 0)
{
lean_object* v_a_5327_; lean_object* v_p_5328_; lean_object* v___y_5330_; uint8_t v___x_5364_; 
v_a_5327_ = lean_ctor_get(v___x_5326_, 0);
lean_inc(v_a_5327_);
lean_dec_ref(v___x_5326_);
v_p_5328_ = lean_ctor_get(v_a_5323_, 0);
v___x_5364_ = lean_nat_dec_le(v_a_5325_, v_a_5327_);
if (v___x_5364_ == 0)
{
lean_dec(v_a_5327_);
v___y_5330_ = v_a_5325_;
goto v___jp_5329_;
}
else
{
lean_dec(v_a_5325_);
v___y_5330_ = v_a_5327_;
goto v___jp_5329_;
}
v___jp_5329_:
{
lean_object* v___x_5331_; 
lean_inc(v___y_5330_);
lean_inc_ref(v_p_5328_);
v___x_5331_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_5328_, v___y_5330_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_);
if (lean_obj_tag(v___x_5331_) == 0)
{
lean_object* v_a_5332_; lean_object* v___x_5333_; 
v_a_5332_ = lean_ctor_get(v___x_5331_, 0);
lean_inc(v_a_5332_);
lean_dec_ref(v___x_5331_);
v___x_5333_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5332_, v___x_5300_, v___y_5330_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_);
if (lean_obj_tag(v___x_5333_) == 0)
{
lean_object* v_a_5334_; lean_object* v___x_5336_; uint8_t v_isShared_5337_; uint8_t v_isSharedCheck_5347_; 
v_a_5334_ = lean_ctor_get(v___x_5333_, 0);
v_isSharedCheck_5347_ = !lean_is_exclusive(v___x_5333_);
if (v_isSharedCheck_5347_ == 0)
{
v___x_5336_ = v___x_5333_;
v_isShared_5337_ = v_isSharedCheck_5347_;
goto v_resetjp_5335_;
}
else
{
lean_inc(v_a_5334_);
lean_dec(v___x_5333_);
v___x_5336_ = lean_box(0);
v_isShared_5337_ = v_isSharedCheck_5347_;
goto v_resetjp_5335_;
}
v_resetjp_5335_:
{
if (lean_obj_tag(v_a_5334_) == 1)
{
lean_object* v_val_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; 
lean_del_object(v___x_5336_);
v_val_5338_ = lean_ctor_get(v_a_5334_, 0);
lean_inc_n(v_val_5338_, 2);
lean_dec_ref(v_a_5334_);
v___x_5339_ = l_Lean_Grind_Linarith_Expr_norm(v_val_5338_);
v___x_5340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5340_, 0, v_a_5323_);
lean_ctor_set(v___x_5340_, 1, v_val_5338_);
v___x_5341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5341_, 0, v___x_5339_);
lean_ctor_set(v___x_5341_, 1, v___x_5340_);
v___x_5342_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5341_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_);
return v___x_5342_;
}
else
{
lean_object* v___x_5343_; lean_object* v___x_5345_; 
lean_dec(v_a_5334_);
lean_dec(v_a_5323_);
v___x_5343_ = lean_box(0);
if (v_isShared_5337_ == 0)
{
lean_ctor_set(v___x_5336_, 0, v___x_5343_);
v___x_5345_ = v___x_5336_;
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
lean_dec(v_a_5323_);
v_a_5348_ = lean_ctor_get(v___x_5333_, 0);
v_isSharedCheck_5355_ = !lean_is_exclusive(v___x_5333_);
if (v_isSharedCheck_5355_ == 0)
{
v___x_5350_ = v___x_5333_;
v_isShared_5351_ = v_isSharedCheck_5355_;
goto v_resetjp_5349_;
}
else
{
lean_inc(v_a_5348_);
lean_dec(v___x_5333_);
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
lean_object* v_a_5356_; lean_object* v___x_5358_; uint8_t v_isShared_5359_; uint8_t v_isSharedCheck_5363_; 
lean_dec(v___y_5330_);
lean_dec(v_a_5323_);
v_a_5356_ = lean_ctor_get(v___x_5331_, 0);
v_isSharedCheck_5363_ = !lean_is_exclusive(v___x_5331_);
if (v_isSharedCheck_5363_ == 0)
{
v___x_5358_ = v___x_5331_;
v_isShared_5359_ = v_isSharedCheck_5363_;
goto v_resetjp_5357_;
}
else
{
lean_inc(v_a_5356_);
lean_dec(v___x_5331_);
v___x_5358_ = lean_box(0);
v_isShared_5359_ = v_isSharedCheck_5363_;
goto v_resetjp_5357_;
}
v_resetjp_5357_:
{
lean_object* v___x_5361_; 
if (v_isShared_5359_ == 0)
{
v___x_5361_ = v___x_5358_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5362_; 
v_reuseFailAlloc_5362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5362_, 0, v_a_5356_);
v___x_5361_ = v_reuseFailAlloc_5362_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
return v___x_5361_;
}
}
}
}
}
else
{
lean_object* v_a_5365_; lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5372_; 
lean_dec(v_a_5325_);
lean_dec(v_a_5323_);
v_a_5365_ = lean_ctor_get(v___x_5326_, 0);
v_isSharedCheck_5372_ = !lean_is_exclusive(v___x_5326_);
if (v_isSharedCheck_5372_ == 0)
{
v___x_5367_ = v___x_5326_;
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
else
{
lean_inc(v_a_5365_);
lean_dec(v___x_5326_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
lean_object* v___x_5370_; 
if (v_isShared_5368_ == 0)
{
v___x_5370_ = v___x_5367_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v_a_5365_);
v___x_5370_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
return v___x_5370_;
}
}
}
}
else
{
lean_object* v_a_5373_; lean_object* v___x_5375_; uint8_t v_isShared_5376_; uint8_t v_isSharedCheck_5380_; 
lean_dec(v_a_5323_);
lean_dec_ref(v_b_5287_);
v_a_5373_ = lean_ctor_get(v___x_5324_, 0);
v_isSharedCheck_5380_ = !lean_is_exclusive(v___x_5324_);
if (v_isSharedCheck_5380_ == 0)
{
v___x_5375_ = v___x_5324_;
v_isShared_5376_ = v_isSharedCheck_5380_;
goto v_resetjp_5374_;
}
else
{
lean_inc(v_a_5373_);
lean_dec(v___x_5324_);
v___x_5375_ = lean_box(0);
v_isShared_5376_ = v_isSharedCheck_5380_;
goto v_resetjp_5374_;
}
v_resetjp_5374_:
{
lean_object* v___x_5378_; 
if (v_isShared_5376_ == 0)
{
v___x_5378_ = v___x_5375_;
goto v_reusejp_5377_;
}
else
{
lean_object* v_reuseFailAlloc_5379_; 
v_reuseFailAlloc_5379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5379_, 0, v_a_5373_);
v___x_5378_ = v_reuseFailAlloc_5379_;
goto v_reusejp_5377_;
}
v_reusejp_5377_:
{
return v___x_5378_;
}
}
}
}
else
{
lean_object* v_a_5381_; lean_object* v___x_5383_; uint8_t v_isShared_5384_; uint8_t v_isSharedCheck_5388_; 
lean_dec_ref(v_b_5287_);
lean_dec_ref(v_a_5286_);
v_a_5381_ = lean_ctor_get(v___x_5322_, 0);
v_isSharedCheck_5388_ = !lean_is_exclusive(v___x_5322_);
if (v_isSharedCheck_5388_ == 0)
{
v___x_5383_ = v___x_5322_;
v_isShared_5384_ = v_isSharedCheck_5388_;
goto v_resetjp_5382_;
}
else
{
lean_inc(v_a_5381_);
lean_dec(v___x_5322_);
v___x_5383_ = lean_box(0);
v_isShared_5384_ = v_isSharedCheck_5388_;
goto v_resetjp_5382_;
}
v_resetjp_5382_:
{
lean_object* v___x_5386_; 
if (v_isShared_5384_ == 0)
{
v___x_5386_ = v___x_5383_;
goto v_reusejp_5385_;
}
else
{
lean_object* v_reuseFailAlloc_5387_; 
v_reuseFailAlloc_5387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5387_, 0, v_a_5381_);
v___x_5386_ = v_reuseFailAlloc_5387_;
goto v_reusejp_5385_;
}
v_reusejp_5385_:
{
return v___x_5386_;
}
}
}
}
else
{
lean_object* v___x_5389_; lean_object* v___x_5391_; 
lean_dec(v_a_5313_);
lean_dec(v_val_5309_);
lean_dec_ref(v_b_5287_);
lean_dec_ref(v_a_5286_);
v___x_5389_ = lean_box(0);
if (v_isShared_5316_ == 0)
{
lean_ctor_set(v___x_5315_, 0, v___x_5389_);
v___x_5391_ = v___x_5315_;
goto v_reusejp_5390_;
}
else
{
lean_object* v_reuseFailAlloc_5392_; 
v_reuseFailAlloc_5392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5392_, 0, v___x_5389_);
v___x_5391_ = v_reuseFailAlloc_5392_;
goto v_reusejp_5390_;
}
v_reusejp_5390_:
{
return v___x_5391_;
}
}
}
}
else
{
lean_object* v_a_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5401_; 
lean_dec(v_val_5309_);
lean_dec_ref(v_b_5287_);
lean_dec_ref(v_a_5286_);
v_a_5394_ = lean_ctor_get(v___x_5312_, 0);
v_isSharedCheck_5401_ = !lean_is_exclusive(v___x_5312_);
if (v_isSharedCheck_5401_ == 0)
{
v___x_5396_ = v___x_5312_;
v_isShared_5397_ = v_isSharedCheck_5401_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_a_5394_);
lean_dec(v___x_5312_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5401_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
lean_object* v___x_5399_; 
if (v_isShared_5397_ == 0)
{
v___x_5399_ = v___x_5396_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5400_; 
v_reuseFailAlloc_5400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5400_, 0, v_a_5394_);
v___x_5399_ = v_reuseFailAlloc_5400_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
return v___x_5399_;
}
}
}
}
else
{
lean_object* v___x_5402_; lean_object* v___x_5404_; 
lean_dec(v_a_5305_);
lean_dec_ref(v_b_5287_);
lean_dec_ref(v_a_5286_);
v___x_5402_ = lean_box(0);
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 0, v___x_5402_);
v___x_5404_ = v___x_5307_;
goto v_reusejp_5403_;
}
else
{
lean_object* v_reuseFailAlloc_5405_; 
v_reuseFailAlloc_5405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5405_, 0, v___x_5402_);
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
lean_dec_ref(v_b_5287_);
lean_dec_ref(v_a_5286_);
v_a_5407_ = lean_ctor_get(v___x_5304_, 0);
v_isSharedCheck_5414_ = !lean_is_exclusive(v___x_5304_);
if (v_isSharedCheck_5414_ == 0)
{
v___x_5409_ = v___x_5304_;
v_isShared_5410_ = v_isSharedCheck_5414_;
goto v_resetjp_5408_;
}
else
{
lean_inc(v_a_5407_);
lean_dec(v___x_5304_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq___boxed(lean_object* v_a_5415_, lean_object* v_b_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_, lean_object* v_a_5424_, lean_object* v_a_5425_, lean_object* v_a_5426_, lean_object* v_a_5427_, lean_object* v_a_5428_){
_start:
{
lean_object* v_res_5429_; 
v_res_5429_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5415_, v_b_5416_, v_a_5417_, v_a_5418_, v_a_5419_, v_a_5420_, v_a_5421_, v_a_5422_, v_a_5423_, v_a_5424_, v_a_5425_, v_a_5426_, v_a_5427_);
lean_dec(v_a_5427_);
lean_dec_ref(v_a_5426_);
lean_dec(v_a_5425_);
lean_dec_ref(v_a_5424_);
lean_dec(v_a_5423_);
lean_dec_ref(v_a_5422_);
lean_dec(v_a_5421_);
lean_dec_ref(v_a_5420_);
lean_dec(v_a_5419_);
lean_dec(v_a_5418_);
lean_dec(v_a_5417_);
return v_res_5429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(lean_object* v_a_5430_, lean_object* v_b_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_){
_start:
{
lean_object* v___x_5444_; 
v___x_5444_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5430_, v_a_5433_);
if (lean_obj_tag(v___x_5444_) == 0)
{
lean_object* v_a_5445_; uint8_t v___x_5446_; lean_object* v___x_5447_; 
v_a_5445_ = lean_ctor_get(v___x_5444_, 0);
lean_inc(v_a_5445_);
lean_dec_ref(v___x_5444_);
v___x_5446_ = 0;
lean_inc_ref(v_a_5430_);
v___x_5447_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5430_, v___x_5446_, v_a_5445_, v_a_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_, v_a_5440_, v_a_5441_, v_a_5442_);
if (lean_obj_tag(v___x_5447_) == 0)
{
lean_object* v_a_5448_; lean_object* v___x_5450_; uint8_t v_isShared_5451_; uint8_t v_isSharedCheck_5491_; 
v_a_5448_ = lean_ctor_get(v___x_5447_, 0);
v_isSharedCheck_5491_ = !lean_is_exclusive(v___x_5447_);
if (v_isSharedCheck_5491_ == 0)
{
v___x_5450_ = v___x_5447_;
v_isShared_5451_ = v_isSharedCheck_5491_;
goto v_resetjp_5449_;
}
else
{
lean_inc(v_a_5448_);
lean_dec(v___x_5447_);
v___x_5450_ = lean_box(0);
v_isShared_5451_ = v_isSharedCheck_5491_;
goto v_resetjp_5449_;
}
v_resetjp_5449_:
{
if (lean_obj_tag(v_a_5448_) == 1)
{
lean_object* v_val_5452_; lean_object* v___x_5453_; 
lean_del_object(v___x_5450_);
v_val_5452_ = lean_ctor_get(v_a_5448_, 0);
lean_inc(v_val_5452_);
lean_dec_ref(v_a_5448_);
v___x_5453_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5431_, v_a_5433_);
if (lean_obj_tag(v___x_5453_) == 0)
{
lean_object* v_a_5454_; lean_object* v___x_5455_; 
v_a_5454_ = lean_ctor_get(v___x_5453_, 0);
lean_inc(v_a_5454_);
lean_dec_ref(v___x_5453_);
lean_inc_ref(v_b_5431_);
v___x_5455_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_5431_, v___x_5446_, v_a_5454_, v_a_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_, v_a_5440_, v_a_5441_, v_a_5442_);
if (lean_obj_tag(v___x_5455_) == 0)
{
lean_object* v_a_5456_; lean_object* v___x_5458_; uint8_t v_isShared_5459_; uint8_t v_isSharedCheck_5470_; 
v_a_5456_ = lean_ctor_get(v___x_5455_, 0);
v_isSharedCheck_5470_ = !lean_is_exclusive(v___x_5455_);
if (v_isSharedCheck_5470_ == 0)
{
v___x_5458_ = v___x_5455_;
v_isShared_5459_ = v_isSharedCheck_5470_;
goto v_resetjp_5457_;
}
else
{
lean_inc(v_a_5456_);
lean_dec(v___x_5455_);
v___x_5458_ = lean_box(0);
v_isShared_5459_ = v_isSharedCheck_5470_;
goto v_resetjp_5457_;
}
v_resetjp_5457_:
{
if (lean_obj_tag(v_a_5456_) == 1)
{
lean_object* v_val_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; 
lean_del_object(v___x_5458_);
v_val_5460_ = lean_ctor_get(v_a_5456_, 0);
lean_inc_n(v_val_5460_, 2);
lean_dec_ref(v_a_5456_);
lean_inc(v_val_5452_);
v___x_5461_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5461_, 0, v_val_5452_);
lean_ctor_set(v___x_5461_, 1, v_val_5460_);
v___x_5462_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5461_);
v___x_5463_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5463_, 0, v_a_5430_);
lean_ctor_set(v___x_5463_, 1, v_b_5431_);
lean_ctor_set(v___x_5463_, 2, v_val_5452_);
lean_ctor_set(v___x_5463_, 3, v_val_5460_);
v___x_5464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5464_, 0, v___x_5462_);
lean_ctor_set(v___x_5464_, 1, v___x_5463_);
v___x_5465_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5464_, v_a_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_, v_a_5440_, v_a_5441_, v_a_5442_);
return v___x_5465_;
}
else
{
lean_object* v___x_5466_; lean_object* v___x_5468_; 
lean_dec(v_a_5456_);
lean_dec(v_val_5452_);
lean_dec_ref(v_b_5431_);
lean_dec_ref(v_a_5430_);
v___x_5466_ = lean_box(0);
if (v_isShared_5459_ == 0)
{
lean_ctor_set(v___x_5458_, 0, v___x_5466_);
v___x_5468_ = v___x_5458_;
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
lean_dec(v_val_5452_);
lean_dec_ref(v_b_5431_);
lean_dec_ref(v_a_5430_);
v_a_5471_ = lean_ctor_get(v___x_5455_, 0);
v_isSharedCheck_5478_ = !lean_is_exclusive(v___x_5455_);
if (v_isSharedCheck_5478_ == 0)
{
v___x_5473_ = v___x_5455_;
v_isShared_5474_ = v_isSharedCheck_5478_;
goto v_resetjp_5472_;
}
else
{
lean_inc(v_a_5471_);
lean_dec(v___x_5455_);
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
else
{
lean_object* v_a_5479_; lean_object* v___x_5481_; uint8_t v_isShared_5482_; uint8_t v_isSharedCheck_5486_; 
lean_dec(v_val_5452_);
lean_dec_ref(v_b_5431_);
lean_dec_ref(v_a_5430_);
v_a_5479_ = lean_ctor_get(v___x_5453_, 0);
v_isSharedCheck_5486_ = !lean_is_exclusive(v___x_5453_);
if (v_isSharedCheck_5486_ == 0)
{
v___x_5481_ = v___x_5453_;
v_isShared_5482_ = v_isSharedCheck_5486_;
goto v_resetjp_5480_;
}
else
{
lean_inc(v_a_5479_);
lean_dec(v___x_5453_);
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
else
{
lean_object* v___x_5487_; lean_object* v___x_5489_; 
lean_dec(v_a_5448_);
lean_dec_ref(v_b_5431_);
lean_dec_ref(v_a_5430_);
v___x_5487_ = lean_box(0);
if (v_isShared_5451_ == 0)
{
lean_ctor_set(v___x_5450_, 0, v___x_5487_);
v___x_5489_ = v___x_5450_;
goto v_reusejp_5488_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v___x_5487_);
v___x_5489_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5488_;
}
v_reusejp_5488_:
{
return v___x_5489_;
}
}
}
}
else
{
lean_object* v_a_5492_; lean_object* v___x_5494_; uint8_t v_isShared_5495_; uint8_t v_isSharedCheck_5499_; 
lean_dec_ref(v_b_5431_);
lean_dec_ref(v_a_5430_);
v_a_5492_ = lean_ctor_get(v___x_5447_, 0);
v_isSharedCheck_5499_ = !lean_is_exclusive(v___x_5447_);
if (v_isSharedCheck_5499_ == 0)
{
v___x_5494_ = v___x_5447_;
v_isShared_5495_ = v_isSharedCheck_5499_;
goto v_resetjp_5493_;
}
else
{
lean_inc(v_a_5492_);
lean_dec(v___x_5447_);
v___x_5494_ = lean_box(0);
v_isShared_5495_ = v_isSharedCheck_5499_;
goto v_resetjp_5493_;
}
v_resetjp_5493_:
{
lean_object* v___x_5497_; 
if (v_isShared_5495_ == 0)
{
v___x_5497_ = v___x_5494_;
goto v_reusejp_5496_;
}
else
{
lean_object* v_reuseFailAlloc_5498_; 
v_reuseFailAlloc_5498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5498_, 0, v_a_5492_);
v___x_5497_ = v_reuseFailAlloc_5498_;
goto v_reusejp_5496_;
}
v_reusejp_5496_:
{
return v___x_5497_;
}
}
}
}
else
{
lean_object* v_a_5500_; lean_object* v___x_5502_; uint8_t v_isShared_5503_; uint8_t v_isSharedCheck_5507_; 
lean_dec_ref(v_b_5431_);
lean_dec_ref(v_a_5430_);
v_a_5500_ = lean_ctor_get(v___x_5444_, 0);
v_isSharedCheck_5507_ = !lean_is_exclusive(v___x_5444_);
if (v_isSharedCheck_5507_ == 0)
{
v___x_5502_ = v___x_5444_;
v_isShared_5503_ = v_isSharedCheck_5507_;
goto v_resetjp_5501_;
}
else
{
lean_inc(v_a_5500_);
lean_dec(v___x_5444_);
v___x_5502_ = lean_box(0);
v_isShared_5503_ = v_isSharedCheck_5507_;
goto v_resetjp_5501_;
}
v_resetjp_5501_:
{
lean_object* v___x_5505_; 
if (v_isShared_5503_ == 0)
{
v___x_5505_ = v___x_5502_;
goto v_reusejp_5504_;
}
else
{
lean_object* v_reuseFailAlloc_5506_; 
v_reuseFailAlloc_5506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5506_, 0, v_a_5500_);
v___x_5505_ = v_reuseFailAlloc_5506_;
goto v_reusejp_5504_;
}
v_reusejp_5504_:
{
return v___x_5505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq___boxed(lean_object* v_a_5508_, lean_object* v_b_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_, lean_object* v_a_5516_, lean_object* v_a_5517_, lean_object* v_a_5518_, lean_object* v_a_5519_, lean_object* v_a_5520_, lean_object* v_a_5521_){
_start:
{
lean_object* v_res_5522_; 
v_res_5522_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5508_, v_b_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_, v_a_5518_, v_a_5519_, v_a_5520_);
lean_dec(v_a_5520_);
lean_dec_ref(v_a_5519_);
lean_dec(v_a_5518_);
lean_dec_ref(v_a_5517_);
lean_dec(v_a_5516_);
lean_dec_ref(v_a_5515_);
lean_dec(v_a_5514_);
lean_dec_ref(v_a_5513_);
lean_dec(v_a_5512_);
lean_dec(v_a_5511_);
lean_dec(v_a_5510_);
return v_res_5522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(lean_object* v_a_5523_, lean_object* v_b_5524_, lean_object* v_a_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_, lean_object* v_a_5530_, lean_object* v_a_5531_, lean_object* v_a_5532_, lean_object* v_a_5533_, lean_object* v_a_5534_, lean_object* v_a_5535_){
_start:
{
lean_object* v___x_5537_; 
v___x_5537_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
if (lean_obj_tag(v___x_5537_) == 0)
{
lean_object* v_a_5538_; lean_object* v_addRightCancelInst_x3f_5539_; 
v_a_5538_ = lean_ctor_get(v___x_5537_, 0);
lean_inc(v_a_5538_);
lean_dec_ref(v___x_5537_);
v_addRightCancelInst_x3f_5539_ = lean_ctor_get(v_a_5538_, 11);
if (lean_obj_tag(v_addRightCancelInst_x3f_5539_) == 0)
{
lean_object* v___x_5540_; 
lean_dec(v_a_5538_);
v___x_5540_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(v_a_5523_, v_b_5524_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
return v___x_5540_;
}
else
{
lean_object* v_id_5541_; lean_object* v_structId_5542_; lean_object* v___x_5543_; 
v_id_5541_ = lean_ctor_get(v_a_5538_, 0);
lean_inc(v_id_5541_);
v_structId_5542_ = lean_ctor_get(v_a_5538_, 1);
lean_inc(v_structId_5542_);
lean_dec(v_a_5538_);
lean_inc_ref(v_a_5523_);
v___x_5543_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5523_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
if (lean_obj_tag(v___x_5543_) == 0)
{
lean_object* v_a_5544_; lean_object* v_fst_5545_; lean_object* v___x_5547_; uint8_t v_isShared_5548_; uint8_t v_isSharedCheck_5633_; 
v_a_5544_ = lean_ctor_get(v___x_5543_, 0);
lean_inc(v_a_5544_);
lean_dec_ref(v___x_5543_);
v_fst_5545_ = lean_ctor_get(v_a_5544_, 0);
v_isSharedCheck_5633_ = !lean_is_exclusive(v_a_5544_);
if (v_isSharedCheck_5633_ == 0)
{
lean_object* v_unused_5634_; 
v_unused_5634_ = lean_ctor_get(v_a_5544_, 1);
lean_dec(v_unused_5634_);
v___x_5547_ = v_a_5544_;
v_isShared_5548_ = v_isSharedCheck_5633_;
goto v_resetjp_5546_;
}
else
{
lean_inc(v_fst_5545_);
lean_dec(v_a_5544_);
v___x_5547_ = lean_box(0);
v_isShared_5548_ = v_isSharedCheck_5633_;
goto v_resetjp_5546_;
}
v_resetjp_5546_:
{
lean_object* v___x_5549_; 
lean_inc_ref(v_b_5524_);
v___x_5549_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5524_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
if (lean_obj_tag(v___x_5549_) == 0)
{
lean_object* v_a_5550_; lean_object* v_fst_5551_; lean_object* v___x_5553_; uint8_t v_isShared_5554_; uint8_t v_isSharedCheck_5623_; 
v_a_5550_ = lean_ctor_get(v___x_5549_, 0);
lean_inc(v_a_5550_);
lean_dec_ref(v___x_5549_);
v_fst_5551_ = lean_ctor_get(v_a_5550_, 0);
v_isSharedCheck_5623_ = !lean_is_exclusive(v_a_5550_);
if (v_isSharedCheck_5623_ == 0)
{
lean_object* v_unused_5624_; 
v_unused_5624_ = lean_ctor_get(v_a_5550_, 1);
lean_dec(v_unused_5624_);
v___x_5553_ = v_a_5550_;
v_isShared_5554_ = v_isSharedCheck_5623_;
goto v_resetjp_5552_;
}
else
{
lean_inc(v_fst_5551_);
lean_dec(v_a_5550_);
v___x_5553_ = lean_box(0);
v_isShared_5554_ = v_isSharedCheck_5623_;
goto v_resetjp_5552_;
}
v_resetjp_5552_:
{
lean_object* v___x_5555_; 
v___x_5555_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5523_, v_a_5526_);
if (lean_obj_tag(v___x_5555_) == 0)
{
lean_object* v_a_5556_; uint8_t v___x_5557_; lean_object* v___x_5558_; 
v_a_5556_ = lean_ctor_get(v___x_5555_, 0);
lean_inc(v_a_5556_);
lean_dec_ref(v___x_5555_);
v___x_5557_ = 0;
v___x_5558_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5545_, v___x_5557_, v_a_5556_, v_structId_5542_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
if (lean_obj_tag(v___x_5558_) == 0)
{
lean_object* v_a_5559_; lean_object* v___x_5561_; uint8_t v_isShared_5562_; uint8_t v_isSharedCheck_5606_; 
v_a_5559_ = lean_ctor_get(v___x_5558_, 0);
v_isSharedCheck_5606_ = !lean_is_exclusive(v___x_5558_);
if (v_isSharedCheck_5606_ == 0)
{
v___x_5561_ = v___x_5558_;
v_isShared_5562_ = v_isSharedCheck_5606_;
goto v_resetjp_5560_;
}
else
{
lean_inc(v_a_5559_);
lean_dec(v___x_5558_);
v___x_5561_ = lean_box(0);
v_isShared_5562_ = v_isSharedCheck_5606_;
goto v_resetjp_5560_;
}
v_resetjp_5560_:
{
if (lean_obj_tag(v_a_5559_) == 1)
{
lean_object* v_val_5563_; lean_object* v___x_5564_; 
lean_del_object(v___x_5561_);
v_val_5563_ = lean_ctor_get(v_a_5559_, 0);
lean_inc(v_val_5563_);
lean_dec_ref(v_a_5559_);
v___x_5564_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5524_, v_a_5526_);
if (lean_obj_tag(v___x_5564_) == 0)
{
lean_object* v_a_5565_; lean_object* v___x_5566_; 
v_a_5565_ = lean_ctor_get(v___x_5564_, 0);
lean_inc(v_a_5565_);
lean_dec_ref(v___x_5564_);
v___x_5566_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5551_, v___x_5557_, v_a_5565_, v_structId_5542_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
if (lean_obj_tag(v___x_5566_) == 0)
{
lean_object* v_a_5567_; lean_object* v___x_5569_; uint8_t v_isShared_5570_; uint8_t v_isSharedCheck_5585_; 
v_a_5567_ = lean_ctor_get(v___x_5566_, 0);
v_isSharedCheck_5585_ = !lean_is_exclusive(v___x_5566_);
if (v_isSharedCheck_5585_ == 0)
{
v___x_5569_ = v___x_5566_;
v_isShared_5570_ = v_isSharedCheck_5585_;
goto v_resetjp_5568_;
}
else
{
lean_inc(v_a_5567_);
lean_dec(v___x_5566_);
v___x_5569_ = lean_box(0);
v_isShared_5570_ = v_isSharedCheck_5585_;
goto v_resetjp_5568_;
}
v_resetjp_5568_:
{
if (lean_obj_tag(v_a_5567_) == 1)
{
lean_object* v_val_5571_; lean_object* v___x_5573_; 
lean_del_object(v___x_5569_);
v_val_5571_ = lean_ctor_get(v_a_5567_, 0);
lean_inc_n(v_val_5571_, 2);
lean_dec_ref(v_a_5567_);
lean_inc(v_val_5563_);
if (v_isShared_5554_ == 0)
{
lean_ctor_set_tag(v___x_5553_, 3);
lean_ctor_set(v___x_5553_, 1, v_val_5571_);
lean_ctor_set(v___x_5553_, 0, v_val_5563_);
v___x_5573_ = v___x_5553_;
goto v_reusejp_5572_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v_val_5563_);
lean_ctor_set(v_reuseFailAlloc_5580_, 1, v_val_5571_);
v___x_5573_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5572_;
}
v_reusejp_5572_:
{
lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5577_; 
v___x_5574_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5573_);
v___x_5575_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5575_, 0, v_a_5523_);
lean_ctor_set(v___x_5575_, 1, v_b_5524_);
lean_ctor_set(v___x_5575_, 2, v_id_5541_);
lean_ctor_set(v___x_5575_, 3, v_val_5563_);
lean_ctor_set(v___x_5575_, 4, v_val_5571_);
if (v_isShared_5548_ == 0)
{
lean_ctor_set(v___x_5547_, 1, v___x_5575_);
lean_ctor_set(v___x_5547_, 0, v___x_5574_);
v___x_5577_ = v___x_5547_;
goto v_reusejp_5576_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v___x_5574_);
lean_ctor_set(v_reuseFailAlloc_5579_, 1, v___x_5575_);
v___x_5577_ = v_reuseFailAlloc_5579_;
goto v_reusejp_5576_;
}
v_reusejp_5576_:
{
lean_object* v___x_5578_; 
v___x_5578_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5577_, v_structId_5542_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
lean_dec(v_structId_5542_);
return v___x_5578_;
}
}
}
else
{
lean_object* v___x_5581_; lean_object* v___x_5583_; 
lean_dec(v_a_5567_);
lean_dec(v_val_5563_);
lean_del_object(v___x_5553_);
lean_del_object(v___x_5547_);
lean_dec(v_structId_5542_);
lean_dec(v_id_5541_);
lean_dec_ref(v_b_5524_);
lean_dec_ref(v_a_5523_);
v___x_5581_ = lean_box(0);
if (v_isShared_5570_ == 0)
{
lean_ctor_set(v___x_5569_, 0, v___x_5581_);
v___x_5583_ = v___x_5569_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5584_; 
v_reuseFailAlloc_5584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5584_, 0, v___x_5581_);
v___x_5583_ = v_reuseFailAlloc_5584_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
return v___x_5583_;
}
}
}
}
else
{
lean_object* v_a_5586_; lean_object* v___x_5588_; uint8_t v_isShared_5589_; uint8_t v_isSharedCheck_5593_; 
lean_dec(v_val_5563_);
lean_del_object(v___x_5553_);
lean_del_object(v___x_5547_);
lean_dec(v_structId_5542_);
lean_dec(v_id_5541_);
lean_dec_ref(v_b_5524_);
lean_dec_ref(v_a_5523_);
v_a_5586_ = lean_ctor_get(v___x_5566_, 0);
v_isSharedCheck_5593_ = !lean_is_exclusive(v___x_5566_);
if (v_isSharedCheck_5593_ == 0)
{
v___x_5588_ = v___x_5566_;
v_isShared_5589_ = v_isSharedCheck_5593_;
goto v_resetjp_5587_;
}
else
{
lean_inc(v_a_5586_);
lean_dec(v___x_5566_);
v___x_5588_ = lean_box(0);
v_isShared_5589_ = v_isSharedCheck_5593_;
goto v_resetjp_5587_;
}
v_resetjp_5587_:
{
lean_object* v___x_5591_; 
if (v_isShared_5589_ == 0)
{
v___x_5591_ = v___x_5588_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v_a_5586_);
v___x_5591_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
return v___x_5591_;
}
}
}
}
else
{
lean_object* v_a_5594_; lean_object* v___x_5596_; uint8_t v_isShared_5597_; uint8_t v_isSharedCheck_5601_; 
lean_dec(v_val_5563_);
lean_del_object(v___x_5553_);
lean_dec(v_fst_5551_);
lean_del_object(v___x_5547_);
lean_dec(v_structId_5542_);
lean_dec(v_id_5541_);
lean_dec_ref(v_b_5524_);
lean_dec_ref(v_a_5523_);
v_a_5594_ = lean_ctor_get(v___x_5564_, 0);
v_isSharedCheck_5601_ = !lean_is_exclusive(v___x_5564_);
if (v_isSharedCheck_5601_ == 0)
{
v___x_5596_ = v___x_5564_;
v_isShared_5597_ = v_isSharedCheck_5601_;
goto v_resetjp_5595_;
}
else
{
lean_inc(v_a_5594_);
lean_dec(v___x_5564_);
v___x_5596_ = lean_box(0);
v_isShared_5597_ = v_isSharedCheck_5601_;
goto v_resetjp_5595_;
}
v_resetjp_5595_:
{
lean_object* v___x_5599_; 
if (v_isShared_5597_ == 0)
{
v___x_5599_ = v___x_5596_;
goto v_reusejp_5598_;
}
else
{
lean_object* v_reuseFailAlloc_5600_; 
v_reuseFailAlloc_5600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5600_, 0, v_a_5594_);
v___x_5599_ = v_reuseFailAlloc_5600_;
goto v_reusejp_5598_;
}
v_reusejp_5598_:
{
return v___x_5599_;
}
}
}
}
else
{
lean_object* v___x_5602_; lean_object* v___x_5604_; 
lean_dec(v_a_5559_);
lean_del_object(v___x_5553_);
lean_dec(v_fst_5551_);
lean_del_object(v___x_5547_);
lean_dec(v_structId_5542_);
lean_dec(v_id_5541_);
lean_dec_ref(v_b_5524_);
lean_dec_ref(v_a_5523_);
v___x_5602_ = lean_box(0);
if (v_isShared_5562_ == 0)
{
lean_ctor_set(v___x_5561_, 0, v___x_5602_);
v___x_5604_ = v___x_5561_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v___x_5602_);
v___x_5604_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5603_;
}
v_reusejp_5603_:
{
return v___x_5604_;
}
}
}
}
else
{
lean_object* v_a_5607_; lean_object* v___x_5609_; uint8_t v_isShared_5610_; uint8_t v_isSharedCheck_5614_; 
lean_del_object(v___x_5553_);
lean_dec(v_fst_5551_);
lean_del_object(v___x_5547_);
lean_dec(v_structId_5542_);
lean_dec(v_id_5541_);
lean_dec_ref(v_b_5524_);
lean_dec_ref(v_a_5523_);
v_a_5607_ = lean_ctor_get(v___x_5558_, 0);
v_isSharedCheck_5614_ = !lean_is_exclusive(v___x_5558_);
if (v_isSharedCheck_5614_ == 0)
{
v___x_5609_ = v___x_5558_;
v_isShared_5610_ = v_isSharedCheck_5614_;
goto v_resetjp_5608_;
}
else
{
lean_inc(v_a_5607_);
lean_dec(v___x_5558_);
v___x_5609_ = lean_box(0);
v_isShared_5610_ = v_isSharedCheck_5614_;
goto v_resetjp_5608_;
}
v_resetjp_5608_:
{
lean_object* v___x_5612_; 
if (v_isShared_5610_ == 0)
{
v___x_5612_ = v___x_5609_;
goto v_reusejp_5611_;
}
else
{
lean_object* v_reuseFailAlloc_5613_; 
v_reuseFailAlloc_5613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5613_, 0, v_a_5607_);
v___x_5612_ = v_reuseFailAlloc_5613_;
goto v_reusejp_5611_;
}
v_reusejp_5611_:
{
return v___x_5612_;
}
}
}
}
else
{
lean_object* v_a_5615_; lean_object* v___x_5617_; uint8_t v_isShared_5618_; uint8_t v_isSharedCheck_5622_; 
lean_del_object(v___x_5553_);
lean_dec(v_fst_5551_);
lean_del_object(v___x_5547_);
lean_dec(v_fst_5545_);
lean_dec(v_structId_5542_);
lean_dec(v_id_5541_);
lean_dec_ref(v_b_5524_);
lean_dec_ref(v_a_5523_);
v_a_5615_ = lean_ctor_get(v___x_5555_, 0);
v_isSharedCheck_5622_ = !lean_is_exclusive(v___x_5555_);
if (v_isSharedCheck_5622_ == 0)
{
v___x_5617_ = v___x_5555_;
v_isShared_5618_ = v_isSharedCheck_5622_;
goto v_resetjp_5616_;
}
else
{
lean_inc(v_a_5615_);
lean_dec(v___x_5555_);
v___x_5617_ = lean_box(0);
v_isShared_5618_ = v_isSharedCheck_5622_;
goto v_resetjp_5616_;
}
v_resetjp_5616_:
{
lean_object* v___x_5620_; 
if (v_isShared_5618_ == 0)
{
v___x_5620_ = v___x_5617_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5621_; 
v_reuseFailAlloc_5621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5621_, 0, v_a_5615_);
v___x_5620_ = v_reuseFailAlloc_5621_;
goto v_reusejp_5619_;
}
v_reusejp_5619_:
{
return v___x_5620_;
}
}
}
}
}
else
{
lean_object* v_a_5625_; lean_object* v___x_5627_; uint8_t v_isShared_5628_; uint8_t v_isSharedCheck_5632_; 
lean_del_object(v___x_5547_);
lean_dec(v_fst_5545_);
lean_dec(v_structId_5542_);
lean_dec(v_id_5541_);
lean_dec_ref(v_b_5524_);
lean_dec_ref(v_a_5523_);
v_a_5625_ = lean_ctor_get(v___x_5549_, 0);
v_isSharedCheck_5632_ = !lean_is_exclusive(v___x_5549_);
if (v_isSharedCheck_5632_ == 0)
{
v___x_5627_ = v___x_5549_;
v_isShared_5628_ = v_isSharedCheck_5632_;
goto v_resetjp_5626_;
}
else
{
lean_inc(v_a_5625_);
lean_dec(v___x_5549_);
v___x_5627_ = lean_box(0);
v_isShared_5628_ = v_isSharedCheck_5632_;
goto v_resetjp_5626_;
}
v_resetjp_5626_:
{
lean_object* v___x_5630_; 
if (v_isShared_5628_ == 0)
{
v___x_5630_ = v___x_5627_;
goto v_reusejp_5629_;
}
else
{
lean_object* v_reuseFailAlloc_5631_; 
v_reuseFailAlloc_5631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5631_, 0, v_a_5625_);
v___x_5630_ = v_reuseFailAlloc_5631_;
goto v_reusejp_5629_;
}
v_reusejp_5629_:
{
return v___x_5630_;
}
}
}
}
}
else
{
lean_object* v_a_5635_; lean_object* v___x_5637_; uint8_t v_isShared_5638_; uint8_t v_isSharedCheck_5642_; 
lean_dec(v_structId_5542_);
lean_dec(v_id_5541_);
lean_dec_ref(v_b_5524_);
lean_dec_ref(v_a_5523_);
v_a_5635_ = lean_ctor_get(v___x_5543_, 0);
v_isSharedCheck_5642_ = !lean_is_exclusive(v___x_5543_);
if (v_isSharedCheck_5642_ == 0)
{
v___x_5637_ = v___x_5543_;
v_isShared_5638_ = v_isSharedCheck_5642_;
goto v_resetjp_5636_;
}
else
{
lean_inc(v_a_5635_);
lean_dec(v___x_5543_);
v___x_5637_ = lean_box(0);
v_isShared_5638_ = v_isSharedCheck_5642_;
goto v_resetjp_5636_;
}
v_resetjp_5636_:
{
lean_object* v___x_5640_; 
if (v_isShared_5638_ == 0)
{
v___x_5640_ = v___x_5637_;
goto v_reusejp_5639_;
}
else
{
lean_object* v_reuseFailAlloc_5641_; 
v_reuseFailAlloc_5641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5641_, 0, v_a_5635_);
v___x_5640_ = v_reuseFailAlloc_5641_;
goto v_reusejp_5639_;
}
v_reusejp_5639_:
{
return v___x_5640_;
}
}
}
}
}
else
{
lean_object* v_a_5643_; lean_object* v___x_5645_; uint8_t v_isShared_5646_; uint8_t v_isSharedCheck_5650_; 
lean_dec_ref(v_b_5524_);
lean_dec_ref(v_a_5523_);
v_a_5643_ = lean_ctor_get(v___x_5537_, 0);
v_isSharedCheck_5650_ = !lean_is_exclusive(v___x_5537_);
if (v_isSharedCheck_5650_ == 0)
{
v___x_5645_ = v___x_5537_;
v_isShared_5646_ = v_isSharedCheck_5650_;
goto v_resetjp_5644_;
}
else
{
lean_inc(v_a_5643_);
lean_dec(v___x_5537_);
v___x_5645_ = lean_box(0);
v_isShared_5646_ = v_isSharedCheck_5650_;
goto v_resetjp_5644_;
}
v_resetjp_5644_:
{
lean_object* v___x_5648_; 
if (v_isShared_5646_ == 0)
{
v___x_5648_ = v___x_5645_;
goto v_reusejp_5647_;
}
else
{
lean_object* v_reuseFailAlloc_5649_; 
v_reuseFailAlloc_5649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5649_, 0, v_a_5643_);
v___x_5648_ = v_reuseFailAlloc_5649_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
return v___x_5648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq___boxed(lean_object* v_a_5651_, lean_object* v_b_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_, lean_object* v_a_5659_, lean_object* v_a_5660_, lean_object* v_a_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_){
_start:
{
lean_object* v_res_5665_; 
v_res_5665_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5651_, v_b_5652_, v_a_5653_, v_a_5654_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_, v_a_5659_, v_a_5660_, v_a_5661_, v_a_5662_, v_a_5663_);
lean_dec(v_a_5663_);
lean_dec_ref(v_a_5662_);
lean_dec(v_a_5661_);
lean_dec_ref(v_a_5660_);
lean_dec(v_a_5659_);
lean_dec_ref(v_a_5658_);
lean_dec(v_a_5657_);
lean_dec_ref(v_a_5656_);
lean_dec(v_a_5655_);
lean_dec(v_a_5654_);
lean_dec(v_a_5653_);
return v_res_5665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(lean_object* v_a_5666_, lean_object* v_b_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_, lean_object* v_a_5671_, lean_object* v_a_5672_, lean_object* v_a_5673_, lean_object* v_a_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_){
_start:
{
lean_object* v___x_5679_; 
v___x_5679_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5666_, v_b_5667_, v_a_5668_, v_a_5676_);
if (lean_obj_tag(v___x_5679_) == 0)
{
lean_object* v_a_5680_; 
v_a_5680_ = lean_ctor_get(v___x_5679_, 0);
lean_inc(v_a_5680_);
lean_dec_ref(v___x_5679_);
if (lean_obj_tag(v_a_5680_) == 1)
{
lean_object* v_val_5681_; lean_object* v___x_5682_; 
v_val_5681_ = lean_ctor_get(v_a_5680_, 0);
lean_inc(v_val_5681_);
lean_dec_ref(v_a_5680_);
v___x_5682_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5681_, v_a_5668_, v_a_5669_, v_a_5670_, v_a_5671_, v_a_5672_, v_a_5673_, v_a_5674_, v_a_5675_, v_a_5676_, v_a_5677_);
if (lean_obj_tag(v___x_5682_) == 0)
{
lean_object* v_a_5683_; uint8_t v___x_5684_; 
v_a_5683_ = lean_ctor_get(v___x_5682_, 0);
lean_inc(v_a_5683_);
lean_dec_ref(v___x_5682_);
v___x_5684_ = lean_unbox(v_a_5683_);
lean_dec(v_a_5683_);
if (v___x_5684_ == 0)
{
lean_object* v___x_5685_; 
v___x_5685_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5666_, v_b_5667_, v_val_5681_, v_a_5668_, v_a_5669_, v_a_5670_, v_a_5671_, v_a_5672_, v_a_5673_, v_a_5674_, v_a_5675_, v_a_5676_, v_a_5677_);
lean_dec(v_val_5681_);
return v___x_5685_;
}
else
{
lean_object* v___x_5686_; 
v___x_5686_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5666_, v_b_5667_, v_val_5681_, v_a_5668_, v_a_5669_, v_a_5670_, v_a_5671_, v_a_5672_, v_a_5673_, v_a_5674_, v_a_5675_, v_a_5676_, v_a_5677_);
lean_dec(v_val_5681_);
return v___x_5686_;
}
}
else
{
lean_object* v_a_5687_; lean_object* v___x_5689_; uint8_t v_isShared_5690_; uint8_t v_isSharedCheck_5694_; 
lean_dec(v_val_5681_);
lean_dec_ref(v_b_5667_);
lean_dec_ref(v_a_5666_);
v_a_5687_ = lean_ctor_get(v___x_5682_, 0);
v_isSharedCheck_5694_ = !lean_is_exclusive(v___x_5682_);
if (v_isSharedCheck_5694_ == 0)
{
v___x_5689_ = v___x_5682_;
v_isShared_5690_ = v_isSharedCheck_5694_;
goto v_resetjp_5688_;
}
else
{
lean_inc(v_a_5687_);
lean_dec(v___x_5682_);
v___x_5689_ = lean_box(0);
v_isShared_5690_ = v_isSharedCheck_5694_;
goto v_resetjp_5688_;
}
v_resetjp_5688_:
{
lean_object* v___x_5692_; 
if (v_isShared_5690_ == 0)
{
v___x_5692_ = v___x_5689_;
goto v_reusejp_5691_;
}
else
{
lean_object* v_reuseFailAlloc_5693_; 
v_reuseFailAlloc_5693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5693_, 0, v_a_5687_);
v___x_5692_ = v_reuseFailAlloc_5693_;
goto v_reusejp_5691_;
}
v_reusejp_5691_:
{
return v___x_5692_;
}
}
}
}
else
{
lean_object* v___x_5695_; 
lean_dec(v_a_5680_);
v___x_5695_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5666_, v_b_5667_, v_a_5668_, v_a_5676_);
if (lean_obj_tag(v___x_5695_) == 0)
{
lean_object* v_a_5696_; lean_object* v___x_5698_; uint8_t v_isShared_5699_; uint8_t v_isSharedCheck_5706_; 
v_a_5696_ = lean_ctor_get(v___x_5695_, 0);
v_isSharedCheck_5706_ = !lean_is_exclusive(v___x_5695_);
if (v_isSharedCheck_5706_ == 0)
{
v___x_5698_ = v___x_5695_;
v_isShared_5699_ = v_isSharedCheck_5706_;
goto v_resetjp_5697_;
}
else
{
lean_inc(v_a_5696_);
lean_dec(v___x_5695_);
v___x_5698_ = lean_box(0);
v_isShared_5699_ = v_isSharedCheck_5706_;
goto v_resetjp_5697_;
}
v_resetjp_5697_:
{
if (lean_obj_tag(v_a_5696_) == 1)
{
lean_object* v_val_5700_; lean_object* v___x_5701_; 
lean_del_object(v___x_5698_);
v_val_5700_ = lean_ctor_get(v_a_5696_, 0);
lean_inc(v_val_5700_);
lean_dec_ref(v_a_5696_);
v___x_5701_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5666_, v_b_5667_, v_val_5700_, v_a_5668_, v_a_5669_, v_a_5670_, v_a_5671_, v_a_5672_, v_a_5673_, v_a_5674_, v_a_5675_, v_a_5676_, v_a_5677_);
lean_dec(v_val_5700_);
return v___x_5701_;
}
else
{
lean_object* v___x_5702_; lean_object* v___x_5704_; 
lean_dec(v_a_5696_);
lean_dec_ref(v_b_5667_);
lean_dec_ref(v_a_5666_);
v___x_5702_ = lean_box(0);
if (v_isShared_5699_ == 0)
{
lean_ctor_set(v___x_5698_, 0, v___x_5702_);
v___x_5704_ = v___x_5698_;
goto v_reusejp_5703_;
}
else
{
lean_object* v_reuseFailAlloc_5705_; 
v_reuseFailAlloc_5705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5705_, 0, v___x_5702_);
v___x_5704_ = v_reuseFailAlloc_5705_;
goto v_reusejp_5703_;
}
v_reusejp_5703_:
{
return v___x_5704_;
}
}
}
}
else
{
lean_object* v_a_5707_; lean_object* v___x_5709_; uint8_t v_isShared_5710_; uint8_t v_isSharedCheck_5714_; 
lean_dec_ref(v_b_5667_);
lean_dec_ref(v_a_5666_);
v_a_5707_ = lean_ctor_get(v___x_5695_, 0);
v_isSharedCheck_5714_ = !lean_is_exclusive(v___x_5695_);
if (v_isSharedCheck_5714_ == 0)
{
v___x_5709_ = v___x_5695_;
v_isShared_5710_ = v_isSharedCheck_5714_;
goto v_resetjp_5708_;
}
else
{
lean_inc(v_a_5707_);
lean_dec(v___x_5695_);
v___x_5709_ = lean_box(0);
v_isShared_5710_ = v_isSharedCheck_5714_;
goto v_resetjp_5708_;
}
v_resetjp_5708_:
{
lean_object* v___x_5712_; 
if (v_isShared_5710_ == 0)
{
v___x_5712_ = v___x_5709_;
goto v_reusejp_5711_;
}
else
{
lean_object* v_reuseFailAlloc_5713_; 
v_reuseFailAlloc_5713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5713_, 0, v_a_5707_);
v___x_5712_ = v_reuseFailAlloc_5713_;
goto v_reusejp_5711_;
}
v_reusejp_5711_:
{
return v___x_5712_;
}
}
}
}
}
else
{
lean_object* v_a_5715_; lean_object* v___x_5717_; uint8_t v_isShared_5718_; uint8_t v_isSharedCheck_5722_; 
lean_dec_ref(v_b_5667_);
lean_dec_ref(v_a_5666_);
v_a_5715_ = lean_ctor_get(v___x_5679_, 0);
v_isSharedCheck_5722_ = !lean_is_exclusive(v___x_5679_);
if (v_isSharedCheck_5722_ == 0)
{
v___x_5717_ = v___x_5679_;
v_isShared_5718_ = v_isSharedCheck_5722_;
goto v_resetjp_5716_;
}
else
{
lean_inc(v_a_5715_);
lean_dec(v___x_5679_);
v___x_5717_ = lean_box(0);
v_isShared_5718_ = v_isSharedCheck_5722_;
goto v_resetjp_5716_;
}
v_resetjp_5716_:
{
lean_object* v___x_5720_; 
if (v_isShared_5718_ == 0)
{
v___x_5720_ = v___x_5717_;
goto v_reusejp_5719_;
}
else
{
lean_object* v_reuseFailAlloc_5721_; 
v_reuseFailAlloc_5721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5721_, 0, v_a_5715_);
v___x_5720_ = v_reuseFailAlloc_5721_;
goto v_reusejp_5719_;
}
v_reusejp_5719_:
{
return v___x_5720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed(lean_object* v_a_5723_, lean_object* v_b_5724_, lean_object* v_a_5725_, lean_object* v_a_5726_, lean_object* v_a_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_, lean_object* v_a_5733_, lean_object* v_a_5734_, lean_object* v_a_5735_){
_start:
{
lean_object* v_res_5736_; 
v_res_5736_ = l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(v_a_5723_, v_b_5724_, v_a_5725_, v_a_5726_, v_a_5727_, v_a_5728_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_, v_a_5734_);
lean_dec(v_a_5734_);
lean_dec_ref(v_a_5733_);
lean_dec(v_a_5732_);
lean_dec_ref(v_a_5731_);
lean_dec(v_a_5730_);
lean_dec_ref(v_a_5729_);
lean_dec(v_a_5728_);
lean_dec_ref(v_a_5727_);
lean_dec(v_a_5726_);
lean_dec(v_a_5725_);
return v_res_5736_;
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
