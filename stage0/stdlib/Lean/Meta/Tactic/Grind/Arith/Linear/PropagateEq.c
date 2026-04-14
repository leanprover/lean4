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
lean_object* v_cs_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; size_t v_sz_2224_; size_t v___x_2225_; lean_object* v___x_2226_; lean_object* v_fst_2227_; 
v_cs_2221_ = lean_ctor_get(v_n_2219_, 0);
v___x_2222_ = lean_box(0);
v___x_2223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set(v___x_2223_, 1, v_b_2220_);
v_sz_2224_ = lean_array_size(v_cs_2221_);
v___x_2225_ = ((size_t)0ULL);
v___x_2226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2217_, v_x_2218_, v_cs_2221_, v_sz_2224_, v___x_2225_, v___x_2223_);
v_fst_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_fst_2227_);
if (lean_obj_tag(v_fst_2227_) == 0)
{
lean_object* v_snd_2228_; lean_object* v___x_2229_; 
v_snd_2228_ = lean_ctor_get(v___x_2226_, 1);
lean_inc(v_snd_2228_);
lean_dec_ref(v___x_2226_);
v___x_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2229_, 0, v_snd_2228_);
return v___x_2229_;
}
else
{
lean_object* v_val_2230_; 
lean_dec_ref(v___x_2226_);
v_val_2230_ = lean_ctor_get(v_fst_2227_, 0);
lean_inc(v_val_2230_);
lean_dec_ref(v_fst_2227_);
return v_val_2230_;
}
}
else
{
lean_object* v_vs_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; size_t v_sz_2234_; size_t v___x_2235_; lean_object* v___x_2236_; lean_object* v_fst_2237_; 
v_vs_2231_ = lean_ctor_get(v_n_2219_, 0);
v___x_2232_ = lean_box(0);
v___x_2233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
lean_ctor_set(v___x_2233_, 1, v_b_2220_);
v_sz_2234_ = lean_array_size(v_vs_2231_);
v___x_2235_ = ((size_t)0ULL);
v___x_2236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2218_, v_vs_2231_, v_sz_2234_, v___x_2235_, v___x_2233_);
v_fst_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_fst_2237_);
if (lean_obj_tag(v_fst_2237_) == 0)
{
lean_object* v_snd_2238_; lean_object* v___x_2239_; 
v_snd_2238_ = lean_ctor_get(v___x_2236_, 1);
lean_inc(v_snd_2238_);
lean_dec_ref(v___x_2236_);
v___x_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2239_, 0, v_snd_2238_);
return v___x_2239_;
}
else
{
lean_object* v_val_2240_; 
lean_dec_ref(v___x_2236_);
v_val_2240_ = lean_ctor_get(v_fst_2237_, 0);
lean_inc(v_val_2240_);
lean_dec_ref(v_fst_2237_);
return v_val_2240_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_2241_, lean_object* v_x_2242_, lean_object* v_as_2243_, size_t v_sz_2244_, size_t v_i_2245_, lean_object* v_b_2246_){
_start:
{
uint8_t v___x_2247_; 
v___x_2247_ = lean_usize_dec_lt(v_i_2245_, v_sz_2244_);
if (v___x_2247_ == 0)
{
return v_b_2246_;
}
else
{
lean_object* v_snd_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2266_; 
v_snd_2248_ = lean_ctor_get(v_b_2246_, 1);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_b_2246_);
if (v_isSharedCheck_2266_ == 0)
{
lean_object* v_unused_2267_; 
v_unused_2267_ = lean_ctor_get(v_b_2246_, 0);
lean_dec(v_unused_2267_);
v___x_2250_ = v_b_2246_;
v_isShared_2251_ = v_isSharedCheck_2266_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_snd_2248_);
lean_dec(v_b_2246_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2266_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v_a_2252_; lean_object* v___x_2253_; 
v_a_2252_ = lean_array_uget_borrowed(v_as_2243_, v_i_2245_);
lean_inc(v_snd_2248_);
v___x_2253_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2241_, v_x_2242_, v_a_2252_, v_snd_2248_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 0, v___x_2254_);
v___x_2256_ = v___x_2250_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_snd_2248_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
lean_dec(v_snd_2248_);
v_a_2258_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2258_);
lean_dec_ref(v___x_2253_);
v___x_2259_ = lean_box(0);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 1, v_a_2258_);
lean_ctor_set(v___x_2250_, 0, v___x_2259_);
v___x_2261_ = v___x_2250_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_a_2258_);
v___x_2261_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
size_t v___x_2262_; size_t v___x_2263_; 
v___x_2262_ = ((size_t)1ULL);
v___x_2263_ = lean_usize_add(v_i_2245_, v___x_2262_);
v_i_2245_ = v___x_2263_;
v_b_2246_ = v___x_2261_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_2268_, lean_object* v_x_2269_, lean_object* v_as_2270_, lean_object* v_sz_2271_, lean_object* v_i_2272_, lean_object* v_b_2273_){
_start:
{
size_t v_sz_boxed_2274_; size_t v_i_boxed_2275_; lean_object* v_res_2276_; 
v_sz_boxed_2274_ = lean_unbox_usize(v_sz_2271_);
lean_dec(v_sz_2271_);
v_i_boxed_2275_ = lean_unbox_usize(v_i_2272_);
lean_dec(v_i_2272_);
v_res_2276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2268_, v_x_2269_, v_as_2270_, v_sz_boxed_2274_, v_i_boxed_2275_, v_b_2273_);
lean_dec_ref(v_as_2270_);
lean_dec(v_x_2269_);
lean_dec_ref(v_init_2268_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_2277_, lean_object* v_x_2278_, lean_object* v_n_2279_, lean_object* v_b_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2277_, v_x_2278_, v_n_2279_, v_b_2280_);
lean_dec_ref(v_n_2279_);
lean_dec(v_x_2278_);
lean_dec_ref(v_init_2277_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(lean_object* v_x_2282_, lean_object* v_t_2283_, lean_object* v_init_2284_){
_start:
{
lean_object* v_root_2285_; lean_object* v_tail_2286_; lean_object* v___x_2287_; 
v_root_2285_ = lean_ctor_get(v_t_2283_, 0);
v_tail_2286_ = lean_ctor_get(v_t_2283_, 1);
lean_inc_ref(v_init_2284_);
v___x_2287_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2284_, v_x_2282_, v_root_2285_, v_init_2284_);
lean_dec_ref(v_init_2284_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref(v___x_2287_);
return v_a_2288_;
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; size_t v_sz_2292_; size_t v___x_2293_; lean_object* v___x_2294_; lean_object* v_fst_2295_; 
v_a_2289_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2289_);
lean_dec_ref(v___x_2287_);
v___x_2290_ = lean_box(0);
v___x_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
lean_ctor_set(v___x_2291_, 1, v_a_2289_);
v_sz_2292_ = lean_array_size(v_tail_2286_);
v___x_2293_ = ((size_t)0ULL);
v___x_2294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2282_, v_tail_2286_, v_sz_2292_, v___x_2293_, v___x_2291_);
v_fst_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_fst_2295_);
if (lean_obj_tag(v_fst_2295_) == 0)
{
lean_object* v_snd_2296_; 
v_snd_2296_ = lean_ctor_get(v___x_2294_, 1);
lean_inc(v_snd_2296_);
lean_dec_ref(v___x_2294_);
return v_snd_2296_;
}
else
{
lean_object* v_val_2297_; 
lean_dec_ref(v___x_2294_);
v_val_2297_ = lean_ctor_get(v_fst_2295_, 0);
lean_inc(v_val_2297_);
lean_dec_ref(v_fst_2295_);
return v_val_2297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0___boxed(lean_object* v_x_2298_, lean_object* v_t_2299_, lean_object* v_init_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2298_, v_t_2299_, v_init_2300_);
lean_dec_ref(v_t_2299_);
lean_dec(v_x_2298_);
return v_res_2301_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2302_ = lean_unsigned_to_nat(32u);
v___x_2303_ = lean_mk_empty_array_with_capacity(v___x_2302_);
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
return v___x_2304_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1(void){
_start:
{
size_t v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v_cs_x27_2310_; 
v___x_2305_ = ((size_t)5ULL);
v___x_2306_ = lean_unsigned_to_nat(0u);
v___x_2307_ = lean_unsigned_to_nat(32u);
v___x_2308_ = lean_mk_empty_array_with_capacity(v___x_2307_);
v___x_2309_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0);
v_cs_x27_2310_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_2310_, 0, v___x_2309_);
lean_ctor_set(v_cs_x27_2310_, 1, v___x_2308_);
lean_ctor_set(v_cs_x27_2310_, 2, v___x_2306_);
lean_ctor_set(v_cs_x27_2310_, 3, v___x_2306_);
lean_ctor_set_usize(v_cs_x27_2310_, 4, v___x_2305_);
return v_cs_x27_2310_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_2313_; lean_object* v_cs_x27_2314_; lean_object* v___x_2315_; 
v_todo_2313_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2));
v_cs_x27_2314_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1);
v___x_2315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2315_, 0, v_cs_x27_2314_);
lean_ctor_set(v___x_2315_, 1, v_todo_2313_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(lean_object* v_x_2316_, lean_object* v_cs_2317_){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v_fst_2320_; lean_object* v_snd_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
v___x_2318_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3);
v___x_2319_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2316_, v_cs_2317_, v___x_2318_);
v_fst_2320_ = lean_ctor_get(v___x_2319_, 0);
v_snd_2321_ = lean_ctor_get(v___x_2319_, 1);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2319_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_snd_2321_);
lean_inc(v_fst_2320_);
lean_dec(v___x_2319_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_fst_2320_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_snd_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___boxed(lean_object* v_x_2329_, lean_object* v_cs_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2329_, v_cs_2330_);
lean_dec_ref(v_cs_2330_);
lean_dec(v_x_2329_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object* v_x_2332_, lean_object* v_cs_2333_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2332_, v_cs_2333_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___boxed(lean_object* v_x_2335_, lean_object* v_cs_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(v_x_2335_, v_cs_2336_);
lean_dec_ref(v_cs_2336_);
lean_dec(v_x_2335_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(lean_object* v_a_2338_, lean_object* v_y_2339_, lean_object* v_fst_2340_, lean_object* v_s_2341_){
_start:
{
lean_object* v_structs_2342_; lean_object* v_typeIdOf_2343_; lean_object* v_exprToStructId_2344_; lean_object* v_exprToStructIdEntries_2345_; lean_object* v_forbiddenNatModules_2346_; lean_object* v_natStructs_2347_; lean_object* v_natTypeIdOf_2348_; lean_object* v_exprToNatStructId_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
v_structs_2342_ = lean_ctor_get(v_s_2341_, 0);
v_typeIdOf_2343_ = lean_ctor_get(v_s_2341_, 1);
v_exprToStructId_2344_ = lean_ctor_get(v_s_2341_, 2);
v_exprToStructIdEntries_2345_ = lean_ctor_get(v_s_2341_, 3);
v_forbiddenNatModules_2346_ = lean_ctor_get(v_s_2341_, 4);
v_natStructs_2347_ = lean_ctor_get(v_s_2341_, 5);
v_natTypeIdOf_2348_ = lean_ctor_get(v_s_2341_, 6);
v_exprToNatStructId_2349_ = lean_ctor_get(v_s_2341_, 7);
v___x_2350_ = lean_array_get_size(v_structs_2342_);
v___x_2351_ = lean_nat_dec_lt(v_a_2338_, v___x_2350_);
if (v___x_2351_ == 0)
{
lean_dec_ref(v_fst_2340_);
return v_s_2341_;
}
else
{
lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2413_; 
lean_inc_ref(v_exprToNatStructId_2349_);
lean_inc_ref(v_natTypeIdOf_2348_);
lean_inc_ref(v_natStructs_2347_);
lean_inc_ref(v_forbiddenNatModules_2346_);
lean_inc_ref(v_exprToStructIdEntries_2345_);
lean_inc_ref(v_exprToStructId_2344_);
lean_inc_ref(v_typeIdOf_2343_);
lean_inc_ref(v_structs_2342_);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_s_2341_);
if (v_isSharedCheck_2413_ == 0)
{
lean_object* v_unused_2414_; lean_object* v_unused_2415_; lean_object* v_unused_2416_; lean_object* v_unused_2417_; lean_object* v_unused_2418_; lean_object* v_unused_2419_; lean_object* v_unused_2420_; lean_object* v_unused_2421_; 
v_unused_2414_ = lean_ctor_get(v_s_2341_, 7);
lean_dec(v_unused_2414_);
v_unused_2415_ = lean_ctor_get(v_s_2341_, 6);
lean_dec(v_unused_2415_);
v_unused_2416_ = lean_ctor_get(v_s_2341_, 5);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v_s_2341_, 4);
lean_dec(v_unused_2417_);
v_unused_2418_ = lean_ctor_get(v_s_2341_, 3);
lean_dec(v_unused_2418_);
v_unused_2419_ = lean_ctor_get(v_s_2341_, 2);
lean_dec(v_unused_2419_);
v_unused_2420_ = lean_ctor_get(v_s_2341_, 1);
lean_dec(v_unused_2420_);
v_unused_2421_ = lean_ctor_get(v_s_2341_, 0);
lean_dec(v_unused_2421_);
v___x_2353_ = v_s_2341_;
v_isShared_2354_ = v_isSharedCheck_2413_;
goto v_resetjp_2352_;
}
else
{
lean_dec(v_s_2341_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2413_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v_v_2355_; lean_object* v_id_2356_; lean_object* v_ringId_x3f_2357_; lean_object* v_type_2358_; lean_object* v_u_2359_; lean_object* v_intModuleInst_2360_; lean_object* v_leInst_x3f_2361_; lean_object* v_ltInst_x3f_2362_; lean_object* v_lawfulOrderLTInst_x3f_2363_; lean_object* v_isPreorderInst_x3f_2364_; lean_object* v_orderedAddInst_x3f_2365_; lean_object* v_isLinearInst_x3f_2366_; lean_object* v_noNatDivInst_x3f_2367_; lean_object* v_ringInst_x3f_2368_; lean_object* v_commRingInst_x3f_2369_; lean_object* v_orderedRingInst_x3f_2370_; lean_object* v_fieldInst_x3f_2371_; lean_object* v_charInst_x3f_2372_; lean_object* v_zero_2373_; lean_object* v_ofNatZero_2374_; lean_object* v_one_x3f_2375_; lean_object* v_leFn_x3f_2376_; lean_object* v_ltFn_x3f_2377_; lean_object* v_addFn_2378_; lean_object* v_zsmulFn_2379_; lean_object* v_nsmulFn_2380_; lean_object* v_zsmulFn_x3f_2381_; lean_object* v_nsmulFn_x3f_2382_; lean_object* v_homomulFn_x3f_2383_; lean_object* v_subFn_2384_; lean_object* v_negFn_2385_; lean_object* v_vars_2386_; lean_object* v_varMap_2387_; lean_object* v_lowers_2388_; lean_object* v_uppers_2389_; lean_object* v_diseqs_2390_; lean_object* v_assignment_2391_; uint8_t v_caseSplits_2392_; lean_object* v_conflict_x3f_2393_; lean_object* v_diseqSplits_2394_; lean_object* v_elimEqs_2395_; lean_object* v_elimStack_2396_; lean_object* v_occurs_2397_; lean_object* v_ignored_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2412_; 
v_v_2355_ = lean_array_fget(v_structs_2342_, v_a_2338_);
v_id_2356_ = lean_ctor_get(v_v_2355_, 0);
v_ringId_x3f_2357_ = lean_ctor_get(v_v_2355_, 1);
v_type_2358_ = lean_ctor_get(v_v_2355_, 2);
v_u_2359_ = lean_ctor_get(v_v_2355_, 3);
v_intModuleInst_2360_ = lean_ctor_get(v_v_2355_, 4);
v_leInst_x3f_2361_ = lean_ctor_get(v_v_2355_, 5);
v_ltInst_x3f_2362_ = lean_ctor_get(v_v_2355_, 6);
v_lawfulOrderLTInst_x3f_2363_ = lean_ctor_get(v_v_2355_, 7);
v_isPreorderInst_x3f_2364_ = lean_ctor_get(v_v_2355_, 8);
v_orderedAddInst_x3f_2365_ = lean_ctor_get(v_v_2355_, 9);
v_isLinearInst_x3f_2366_ = lean_ctor_get(v_v_2355_, 10);
v_noNatDivInst_x3f_2367_ = lean_ctor_get(v_v_2355_, 11);
v_ringInst_x3f_2368_ = lean_ctor_get(v_v_2355_, 12);
v_commRingInst_x3f_2369_ = lean_ctor_get(v_v_2355_, 13);
v_orderedRingInst_x3f_2370_ = lean_ctor_get(v_v_2355_, 14);
v_fieldInst_x3f_2371_ = lean_ctor_get(v_v_2355_, 15);
v_charInst_x3f_2372_ = lean_ctor_get(v_v_2355_, 16);
v_zero_2373_ = lean_ctor_get(v_v_2355_, 17);
v_ofNatZero_2374_ = lean_ctor_get(v_v_2355_, 18);
v_one_x3f_2375_ = lean_ctor_get(v_v_2355_, 19);
v_leFn_x3f_2376_ = lean_ctor_get(v_v_2355_, 20);
v_ltFn_x3f_2377_ = lean_ctor_get(v_v_2355_, 21);
v_addFn_2378_ = lean_ctor_get(v_v_2355_, 22);
v_zsmulFn_2379_ = lean_ctor_get(v_v_2355_, 23);
v_nsmulFn_2380_ = lean_ctor_get(v_v_2355_, 24);
v_zsmulFn_x3f_2381_ = lean_ctor_get(v_v_2355_, 25);
v_nsmulFn_x3f_2382_ = lean_ctor_get(v_v_2355_, 26);
v_homomulFn_x3f_2383_ = lean_ctor_get(v_v_2355_, 27);
v_subFn_2384_ = lean_ctor_get(v_v_2355_, 28);
v_negFn_2385_ = lean_ctor_get(v_v_2355_, 29);
v_vars_2386_ = lean_ctor_get(v_v_2355_, 30);
v_varMap_2387_ = lean_ctor_get(v_v_2355_, 31);
v_lowers_2388_ = lean_ctor_get(v_v_2355_, 32);
v_uppers_2389_ = lean_ctor_get(v_v_2355_, 33);
v_diseqs_2390_ = lean_ctor_get(v_v_2355_, 34);
v_assignment_2391_ = lean_ctor_get(v_v_2355_, 35);
v_caseSplits_2392_ = lean_ctor_get_uint8(v_v_2355_, sizeof(void*)*42);
v_conflict_x3f_2393_ = lean_ctor_get(v_v_2355_, 36);
v_diseqSplits_2394_ = lean_ctor_get(v_v_2355_, 37);
v_elimEqs_2395_ = lean_ctor_get(v_v_2355_, 38);
v_elimStack_2396_ = lean_ctor_get(v_v_2355_, 39);
v_occurs_2397_ = lean_ctor_get(v_v_2355_, 40);
v_ignored_2398_ = lean_ctor_get(v_v_2355_, 41);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_v_2355_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2400_ = v_v_2355_;
v_isShared_2401_ = v_isSharedCheck_2412_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_ignored_2398_);
lean_inc(v_occurs_2397_);
lean_inc(v_elimStack_2396_);
lean_inc(v_elimEqs_2395_);
lean_inc(v_diseqSplits_2394_);
lean_inc(v_conflict_x3f_2393_);
lean_inc(v_assignment_2391_);
lean_inc(v_diseqs_2390_);
lean_inc(v_uppers_2389_);
lean_inc(v_lowers_2388_);
lean_inc(v_varMap_2387_);
lean_inc(v_vars_2386_);
lean_inc(v_negFn_2385_);
lean_inc(v_subFn_2384_);
lean_inc(v_homomulFn_x3f_2383_);
lean_inc(v_nsmulFn_x3f_2382_);
lean_inc(v_zsmulFn_x3f_2381_);
lean_inc(v_nsmulFn_2380_);
lean_inc(v_zsmulFn_2379_);
lean_inc(v_addFn_2378_);
lean_inc(v_ltFn_x3f_2377_);
lean_inc(v_leFn_x3f_2376_);
lean_inc(v_one_x3f_2375_);
lean_inc(v_ofNatZero_2374_);
lean_inc(v_zero_2373_);
lean_inc(v_charInst_x3f_2372_);
lean_inc(v_fieldInst_x3f_2371_);
lean_inc(v_orderedRingInst_x3f_2370_);
lean_inc(v_commRingInst_x3f_2369_);
lean_inc(v_ringInst_x3f_2368_);
lean_inc(v_noNatDivInst_x3f_2367_);
lean_inc(v_isLinearInst_x3f_2366_);
lean_inc(v_orderedAddInst_x3f_2365_);
lean_inc(v_isPreorderInst_x3f_2364_);
lean_inc(v_lawfulOrderLTInst_x3f_2363_);
lean_inc(v_ltInst_x3f_2362_);
lean_inc(v_leInst_x3f_2361_);
lean_inc(v_intModuleInst_2360_);
lean_inc(v_u_2359_);
lean_inc(v_type_2358_);
lean_inc(v_ringId_x3f_2357_);
lean_inc(v_id_2356_);
lean_dec(v_v_2355_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2412_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v_xs_x27_2403_; lean_object* v___x_2404_; lean_object* v___x_2406_; 
v___x_2402_ = lean_box(0);
v_xs_x27_2403_ = lean_array_fset(v_structs_2342_, v_a_2338_, v___x_2402_);
v___x_2404_ = l_Lean_PersistentArray_set___redArg(v_lowers_2388_, v_y_2339_, v_fst_2340_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 32, v___x_2404_);
v___x_2406_ = v___x_2400_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_id_2356_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v_ringId_x3f_2357_);
lean_ctor_set(v_reuseFailAlloc_2411_, 2, v_type_2358_);
lean_ctor_set(v_reuseFailAlloc_2411_, 3, v_u_2359_);
lean_ctor_set(v_reuseFailAlloc_2411_, 4, v_intModuleInst_2360_);
lean_ctor_set(v_reuseFailAlloc_2411_, 5, v_leInst_x3f_2361_);
lean_ctor_set(v_reuseFailAlloc_2411_, 6, v_ltInst_x3f_2362_);
lean_ctor_set(v_reuseFailAlloc_2411_, 7, v_lawfulOrderLTInst_x3f_2363_);
lean_ctor_set(v_reuseFailAlloc_2411_, 8, v_isPreorderInst_x3f_2364_);
lean_ctor_set(v_reuseFailAlloc_2411_, 9, v_orderedAddInst_x3f_2365_);
lean_ctor_set(v_reuseFailAlloc_2411_, 10, v_isLinearInst_x3f_2366_);
lean_ctor_set(v_reuseFailAlloc_2411_, 11, v_noNatDivInst_x3f_2367_);
lean_ctor_set(v_reuseFailAlloc_2411_, 12, v_ringInst_x3f_2368_);
lean_ctor_set(v_reuseFailAlloc_2411_, 13, v_commRingInst_x3f_2369_);
lean_ctor_set(v_reuseFailAlloc_2411_, 14, v_orderedRingInst_x3f_2370_);
lean_ctor_set(v_reuseFailAlloc_2411_, 15, v_fieldInst_x3f_2371_);
lean_ctor_set(v_reuseFailAlloc_2411_, 16, v_charInst_x3f_2372_);
lean_ctor_set(v_reuseFailAlloc_2411_, 17, v_zero_2373_);
lean_ctor_set(v_reuseFailAlloc_2411_, 18, v_ofNatZero_2374_);
lean_ctor_set(v_reuseFailAlloc_2411_, 19, v_one_x3f_2375_);
lean_ctor_set(v_reuseFailAlloc_2411_, 20, v_leFn_x3f_2376_);
lean_ctor_set(v_reuseFailAlloc_2411_, 21, v_ltFn_x3f_2377_);
lean_ctor_set(v_reuseFailAlloc_2411_, 22, v_addFn_2378_);
lean_ctor_set(v_reuseFailAlloc_2411_, 23, v_zsmulFn_2379_);
lean_ctor_set(v_reuseFailAlloc_2411_, 24, v_nsmulFn_2380_);
lean_ctor_set(v_reuseFailAlloc_2411_, 25, v_zsmulFn_x3f_2381_);
lean_ctor_set(v_reuseFailAlloc_2411_, 26, v_nsmulFn_x3f_2382_);
lean_ctor_set(v_reuseFailAlloc_2411_, 27, v_homomulFn_x3f_2383_);
lean_ctor_set(v_reuseFailAlloc_2411_, 28, v_subFn_2384_);
lean_ctor_set(v_reuseFailAlloc_2411_, 29, v_negFn_2385_);
lean_ctor_set(v_reuseFailAlloc_2411_, 30, v_vars_2386_);
lean_ctor_set(v_reuseFailAlloc_2411_, 31, v_varMap_2387_);
lean_ctor_set(v_reuseFailAlloc_2411_, 32, v___x_2404_);
lean_ctor_set(v_reuseFailAlloc_2411_, 33, v_uppers_2389_);
lean_ctor_set(v_reuseFailAlloc_2411_, 34, v_diseqs_2390_);
lean_ctor_set(v_reuseFailAlloc_2411_, 35, v_assignment_2391_);
lean_ctor_set(v_reuseFailAlloc_2411_, 36, v_conflict_x3f_2393_);
lean_ctor_set(v_reuseFailAlloc_2411_, 37, v_diseqSplits_2394_);
lean_ctor_set(v_reuseFailAlloc_2411_, 38, v_elimEqs_2395_);
lean_ctor_set(v_reuseFailAlloc_2411_, 39, v_elimStack_2396_);
lean_ctor_set(v_reuseFailAlloc_2411_, 40, v_occurs_2397_);
lean_ctor_set(v_reuseFailAlloc_2411_, 41, v_ignored_2398_);
lean_ctor_set_uint8(v_reuseFailAlloc_2411_, sizeof(void*)*42, v_caseSplits_2392_);
v___x_2406_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2407_ = lean_array_fset(v_xs_x27_2403_, v_a_2338_, v___x_2406_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2407_);
v___x_2409_ = v___x_2353_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2410_, 1, v_typeIdOf_2343_);
lean_ctor_set(v_reuseFailAlloc_2410_, 2, v_exprToStructId_2344_);
lean_ctor_set(v_reuseFailAlloc_2410_, 3, v_exprToStructIdEntries_2345_);
lean_ctor_set(v_reuseFailAlloc_2410_, 4, v_forbiddenNatModules_2346_);
lean_ctor_set(v_reuseFailAlloc_2410_, 5, v_natStructs_2347_);
lean_ctor_set(v_reuseFailAlloc_2410_, 6, v_natTypeIdOf_2348_);
lean_ctor_set(v_reuseFailAlloc_2410_, 7, v_exprToNatStructId_2349_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed(lean_object* v_a_2422_, lean_object* v_y_2423_, lean_object* v_fst_2424_, lean_object* v_s_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(v_a_2422_, v_y_2423_, v_fst_2424_, v_s_2425_);
lean_dec(v_y_2423_);
lean_dec(v_a_2422_);
return v_res_2426_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0(void){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object* v_a_2428_, lean_object* v_x_2429_, lean_object* v_c_2430_, lean_object* v_y_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2479_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2447_ = v___x_2444_;
v_isShared_2448_ = v_isSharedCheck_2479_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2479_;
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
v___x_2450_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___y_2453_; lean_object* v_lowers_2461_; lean_object* v_size_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2451_);
lean_dec_ref(v___x_2450_);
v_lowers_2461_ = lean_ctor_get(v_a_2451_, 32);
lean_inc_ref(v_lowers_2461_);
lean_dec(v_a_2451_);
v_size_2462_ = lean_ctor_get(v_lowers_2461_, 2);
v___x_2463_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2464_ = lean_nat_dec_lt(v_y_2431_, v_size_2462_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; 
lean_dec_ref(v_lowers_2461_);
v___x_2465_ = l_outOfBounds___redArg(v___x_2463_);
v___y_2453_ = v___x_2465_;
goto v___jp_2452_;
}
else
{
lean_object* v___x_2466_; 
v___x_2466_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2463_, v_lowers_2461_, v_y_2431_);
lean_dec_ref(v_lowers_2461_);
v___y_2453_ = v___x_2466_;
goto v___jp_2452_;
}
v___jp_2452_:
{
lean_object* v___x_2454_; lean_object* v_fst_2455_; lean_object* v_snd_2456_; lean_object* v___f_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2454_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2429_, v___y_2453_);
lean_dec_ref(v___y_2453_);
v_fst_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_fst_2455_);
v_snd_2456_ = lean_ctor_get(v___x_2454_, 1);
lean_inc(v_snd_2456_);
lean_dec_ref(v___x_2454_);
lean_inc(v_a_2432_);
v___f_2457_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2457_, 0, v_a_2432_);
lean_closure_set(v___f_2457_, 1, v_y_2431_);
lean_closure_set(v___f_2457_, 2, v_fst_2455_);
v___x_2458_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2459_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2458_, v___f_2457_, v_a_2433_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v___x_2460_; 
lean_dec_ref(v___x_2459_);
v___x_2460_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2428_, v_x_2429_, v_c_2430_, v_snd_2456_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
lean_dec(v_snd_2456_);
return v___x_2460_;
}
else
{
lean_dec(v_snd_2456_);
lean_dec_ref(v_c_2430_);
lean_dec(v_x_2429_);
lean_dec(v_a_2428_);
return v___x_2459_;
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec(v_y_2431_);
lean_dec_ref(v_c_2430_);
lean_dec(v_x_2429_);
lean_dec(v_a_2428_);
v_a_2467_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2450_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2450_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
else
{
lean_object* v___x_2475_; lean_object* v___x_2477_; 
lean_dec(v_y_2431_);
lean_dec_ref(v_c_2430_);
lean_dec(v_x_2429_);
lean_dec(v_a_2428_);
v___x_2475_ = lean_box(0);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v___x_2475_);
v___x_2477_ = v___x_2447_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2475_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
lean_dec(v_y_2431_);
lean_dec_ref(v_c_2430_);
lean_dec(v_x_2429_);
lean_dec(v_a_2428_);
v_a_2480_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2444_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2444_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object* v_a_2488_, lean_object* v_x_2489_, lean_object* v_c_2490_, lean_object* v_y_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_2488_, v_x_2489_, v_c_2490_, v_y_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
lean_dec(v_a_2500_);
lean_dec_ref(v_a_2499_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
lean_dec(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec(v_a_2492_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(lean_object* v_a_2505_, lean_object* v_y_2506_, lean_object* v_fst_2507_, lean_object* v_s_2508_){
_start:
{
lean_object* v_structs_2509_; lean_object* v_typeIdOf_2510_; lean_object* v_exprToStructId_2511_; lean_object* v_exprToStructIdEntries_2512_; lean_object* v_forbiddenNatModules_2513_; lean_object* v_natStructs_2514_; lean_object* v_natTypeIdOf_2515_; lean_object* v_exprToNatStructId_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
v_structs_2509_ = lean_ctor_get(v_s_2508_, 0);
v_typeIdOf_2510_ = lean_ctor_get(v_s_2508_, 1);
v_exprToStructId_2511_ = lean_ctor_get(v_s_2508_, 2);
v_exprToStructIdEntries_2512_ = lean_ctor_get(v_s_2508_, 3);
v_forbiddenNatModules_2513_ = lean_ctor_get(v_s_2508_, 4);
v_natStructs_2514_ = lean_ctor_get(v_s_2508_, 5);
v_natTypeIdOf_2515_ = lean_ctor_get(v_s_2508_, 6);
v_exprToNatStructId_2516_ = lean_ctor_get(v_s_2508_, 7);
v___x_2517_ = lean_array_get_size(v_structs_2509_);
v___x_2518_ = lean_nat_dec_lt(v_a_2505_, v___x_2517_);
if (v___x_2518_ == 0)
{
lean_dec_ref(v_fst_2507_);
return v_s_2508_;
}
else
{
lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2580_; 
lean_inc_ref(v_exprToNatStructId_2516_);
lean_inc_ref(v_natTypeIdOf_2515_);
lean_inc_ref(v_natStructs_2514_);
lean_inc_ref(v_forbiddenNatModules_2513_);
lean_inc_ref(v_exprToStructIdEntries_2512_);
lean_inc_ref(v_exprToStructId_2511_);
lean_inc_ref(v_typeIdOf_2510_);
lean_inc_ref(v_structs_2509_);
v_isSharedCheck_2580_ = !lean_is_exclusive(v_s_2508_);
if (v_isSharedCheck_2580_ == 0)
{
lean_object* v_unused_2581_; lean_object* v_unused_2582_; lean_object* v_unused_2583_; lean_object* v_unused_2584_; lean_object* v_unused_2585_; lean_object* v_unused_2586_; lean_object* v_unused_2587_; lean_object* v_unused_2588_; 
v_unused_2581_ = lean_ctor_get(v_s_2508_, 7);
lean_dec(v_unused_2581_);
v_unused_2582_ = lean_ctor_get(v_s_2508_, 6);
lean_dec(v_unused_2582_);
v_unused_2583_ = lean_ctor_get(v_s_2508_, 5);
lean_dec(v_unused_2583_);
v_unused_2584_ = lean_ctor_get(v_s_2508_, 4);
lean_dec(v_unused_2584_);
v_unused_2585_ = lean_ctor_get(v_s_2508_, 3);
lean_dec(v_unused_2585_);
v_unused_2586_ = lean_ctor_get(v_s_2508_, 2);
lean_dec(v_unused_2586_);
v_unused_2587_ = lean_ctor_get(v_s_2508_, 1);
lean_dec(v_unused_2587_);
v_unused_2588_ = lean_ctor_get(v_s_2508_, 0);
lean_dec(v_unused_2588_);
v___x_2520_ = v_s_2508_;
v_isShared_2521_ = v_isSharedCheck_2580_;
goto v_resetjp_2519_;
}
else
{
lean_dec(v_s_2508_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2580_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v_v_2522_; lean_object* v_id_2523_; lean_object* v_ringId_x3f_2524_; lean_object* v_type_2525_; lean_object* v_u_2526_; lean_object* v_intModuleInst_2527_; lean_object* v_leInst_x3f_2528_; lean_object* v_ltInst_x3f_2529_; lean_object* v_lawfulOrderLTInst_x3f_2530_; lean_object* v_isPreorderInst_x3f_2531_; lean_object* v_orderedAddInst_x3f_2532_; lean_object* v_isLinearInst_x3f_2533_; lean_object* v_noNatDivInst_x3f_2534_; lean_object* v_ringInst_x3f_2535_; lean_object* v_commRingInst_x3f_2536_; lean_object* v_orderedRingInst_x3f_2537_; lean_object* v_fieldInst_x3f_2538_; lean_object* v_charInst_x3f_2539_; lean_object* v_zero_2540_; lean_object* v_ofNatZero_2541_; lean_object* v_one_x3f_2542_; lean_object* v_leFn_x3f_2543_; lean_object* v_ltFn_x3f_2544_; lean_object* v_addFn_2545_; lean_object* v_zsmulFn_2546_; lean_object* v_nsmulFn_2547_; lean_object* v_zsmulFn_x3f_2548_; lean_object* v_nsmulFn_x3f_2549_; lean_object* v_homomulFn_x3f_2550_; lean_object* v_subFn_2551_; lean_object* v_negFn_2552_; lean_object* v_vars_2553_; lean_object* v_varMap_2554_; lean_object* v_lowers_2555_; lean_object* v_uppers_2556_; lean_object* v_diseqs_2557_; lean_object* v_assignment_2558_; uint8_t v_caseSplits_2559_; lean_object* v_conflict_x3f_2560_; lean_object* v_diseqSplits_2561_; lean_object* v_elimEqs_2562_; lean_object* v_elimStack_2563_; lean_object* v_occurs_2564_; lean_object* v_ignored_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2579_; 
v_v_2522_ = lean_array_fget(v_structs_2509_, v_a_2505_);
v_id_2523_ = lean_ctor_get(v_v_2522_, 0);
v_ringId_x3f_2524_ = lean_ctor_get(v_v_2522_, 1);
v_type_2525_ = lean_ctor_get(v_v_2522_, 2);
v_u_2526_ = lean_ctor_get(v_v_2522_, 3);
v_intModuleInst_2527_ = lean_ctor_get(v_v_2522_, 4);
v_leInst_x3f_2528_ = lean_ctor_get(v_v_2522_, 5);
v_ltInst_x3f_2529_ = lean_ctor_get(v_v_2522_, 6);
v_lawfulOrderLTInst_x3f_2530_ = lean_ctor_get(v_v_2522_, 7);
v_isPreorderInst_x3f_2531_ = lean_ctor_get(v_v_2522_, 8);
v_orderedAddInst_x3f_2532_ = lean_ctor_get(v_v_2522_, 9);
v_isLinearInst_x3f_2533_ = lean_ctor_get(v_v_2522_, 10);
v_noNatDivInst_x3f_2534_ = lean_ctor_get(v_v_2522_, 11);
v_ringInst_x3f_2535_ = lean_ctor_get(v_v_2522_, 12);
v_commRingInst_x3f_2536_ = lean_ctor_get(v_v_2522_, 13);
v_orderedRingInst_x3f_2537_ = lean_ctor_get(v_v_2522_, 14);
v_fieldInst_x3f_2538_ = lean_ctor_get(v_v_2522_, 15);
v_charInst_x3f_2539_ = lean_ctor_get(v_v_2522_, 16);
v_zero_2540_ = lean_ctor_get(v_v_2522_, 17);
v_ofNatZero_2541_ = lean_ctor_get(v_v_2522_, 18);
v_one_x3f_2542_ = lean_ctor_get(v_v_2522_, 19);
v_leFn_x3f_2543_ = lean_ctor_get(v_v_2522_, 20);
v_ltFn_x3f_2544_ = lean_ctor_get(v_v_2522_, 21);
v_addFn_2545_ = lean_ctor_get(v_v_2522_, 22);
v_zsmulFn_2546_ = lean_ctor_get(v_v_2522_, 23);
v_nsmulFn_2547_ = lean_ctor_get(v_v_2522_, 24);
v_zsmulFn_x3f_2548_ = lean_ctor_get(v_v_2522_, 25);
v_nsmulFn_x3f_2549_ = lean_ctor_get(v_v_2522_, 26);
v_homomulFn_x3f_2550_ = lean_ctor_get(v_v_2522_, 27);
v_subFn_2551_ = lean_ctor_get(v_v_2522_, 28);
v_negFn_2552_ = lean_ctor_get(v_v_2522_, 29);
v_vars_2553_ = lean_ctor_get(v_v_2522_, 30);
v_varMap_2554_ = lean_ctor_get(v_v_2522_, 31);
v_lowers_2555_ = lean_ctor_get(v_v_2522_, 32);
v_uppers_2556_ = lean_ctor_get(v_v_2522_, 33);
v_diseqs_2557_ = lean_ctor_get(v_v_2522_, 34);
v_assignment_2558_ = lean_ctor_get(v_v_2522_, 35);
v_caseSplits_2559_ = lean_ctor_get_uint8(v_v_2522_, sizeof(void*)*42);
v_conflict_x3f_2560_ = lean_ctor_get(v_v_2522_, 36);
v_diseqSplits_2561_ = lean_ctor_get(v_v_2522_, 37);
v_elimEqs_2562_ = lean_ctor_get(v_v_2522_, 38);
v_elimStack_2563_ = lean_ctor_get(v_v_2522_, 39);
v_occurs_2564_ = lean_ctor_get(v_v_2522_, 40);
v_ignored_2565_ = lean_ctor_get(v_v_2522_, 41);
v_isSharedCheck_2579_ = !lean_is_exclusive(v_v_2522_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2567_ = v_v_2522_;
v_isShared_2568_ = v_isSharedCheck_2579_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_ignored_2565_);
lean_inc(v_occurs_2564_);
lean_inc(v_elimStack_2563_);
lean_inc(v_elimEqs_2562_);
lean_inc(v_diseqSplits_2561_);
lean_inc(v_conflict_x3f_2560_);
lean_inc(v_assignment_2558_);
lean_inc(v_diseqs_2557_);
lean_inc(v_uppers_2556_);
lean_inc(v_lowers_2555_);
lean_inc(v_varMap_2554_);
lean_inc(v_vars_2553_);
lean_inc(v_negFn_2552_);
lean_inc(v_subFn_2551_);
lean_inc(v_homomulFn_x3f_2550_);
lean_inc(v_nsmulFn_x3f_2549_);
lean_inc(v_zsmulFn_x3f_2548_);
lean_inc(v_nsmulFn_2547_);
lean_inc(v_zsmulFn_2546_);
lean_inc(v_addFn_2545_);
lean_inc(v_ltFn_x3f_2544_);
lean_inc(v_leFn_x3f_2543_);
lean_inc(v_one_x3f_2542_);
lean_inc(v_ofNatZero_2541_);
lean_inc(v_zero_2540_);
lean_inc(v_charInst_x3f_2539_);
lean_inc(v_fieldInst_x3f_2538_);
lean_inc(v_orderedRingInst_x3f_2537_);
lean_inc(v_commRingInst_x3f_2536_);
lean_inc(v_ringInst_x3f_2535_);
lean_inc(v_noNatDivInst_x3f_2534_);
lean_inc(v_isLinearInst_x3f_2533_);
lean_inc(v_orderedAddInst_x3f_2532_);
lean_inc(v_isPreorderInst_x3f_2531_);
lean_inc(v_lawfulOrderLTInst_x3f_2530_);
lean_inc(v_ltInst_x3f_2529_);
lean_inc(v_leInst_x3f_2528_);
lean_inc(v_intModuleInst_2527_);
lean_inc(v_u_2526_);
lean_inc(v_type_2525_);
lean_inc(v_ringId_x3f_2524_);
lean_inc(v_id_2523_);
lean_dec(v_v_2522_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2579_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v_xs_x27_2570_; lean_object* v___x_2571_; lean_object* v___x_2573_; 
v___x_2569_ = lean_box(0);
v_xs_x27_2570_ = lean_array_fset(v_structs_2509_, v_a_2505_, v___x_2569_);
v___x_2571_ = l_Lean_PersistentArray_set___redArg(v_uppers_2556_, v_y_2506_, v_fst_2507_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 33, v___x_2571_);
v___x_2573_ = v___x_2567_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_id_2523_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_ringId_x3f_2524_);
lean_ctor_set(v_reuseFailAlloc_2578_, 2, v_type_2525_);
lean_ctor_set(v_reuseFailAlloc_2578_, 3, v_u_2526_);
lean_ctor_set(v_reuseFailAlloc_2578_, 4, v_intModuleInst_2527_);
lean_ctor_set(v_reuseFailAlloc_2578_, 5, v_leInst_x3f_2528_);
lean_ctor_set(v_reuseFailAlloc_2578_, 6, v_ltInst_x3f_2529_);
lean_ctor_set(v_reuseFailAlloc_2578_, 7, v_lawfulOrderLTInst_x3f_2530_);
lean_ctor_set(v_reuseFailAlloc_2578_, 8, v_isPreorderInst_x3f_2531_);
lean_ctor_set(v_reuseFailAlloc_2578_, 9, v_orderedAddInst_x3f_2532_);
lean_ctor_set(v_reuseFailAlloc_2578_, 10, v_isLinearInst_x3f_2533_);
lean_ctor_set(v_reuseFailAlloc_2578_, 11, v_noNatDivInst_x3f_2534_);
lean_ctor_set(v_reuseFailAlloc_2578_, 12, v_ringInst_x3f_2535_);
lean_ctor_set(v_reuseFailAlloc_2578_, 13, v_commRingInst_x3f_2536_);
lean_ctor_set(v_reuseFailAlloc_2578_, 14, v_orderedRingInst_x3f_2537_);
lean_ctor_set(v_reuseFailAlloc_2578_, 15, v_fieldInst_x3f_2538_);
lean_ctor_set(v_reuseFailAlloc_2578_, 16, v_charInst_x3f_2539_);
lean_ctor_set(v_reuseFailAlloc_2578_, 17, v_zero_2540_);
lean_ctor_set(v_reuseFailAlloc_2578_, 18, v_ofNatZero_2541_);
lean_ctor_set(v_reuseFailAlloc_2578_, 19, v_one_x3f_2542_);
lean_ctor_set(v_reuseFailAlloc_2578_, 20, v_leFn_x3f_2543_);
lean_ctor_set(v_reuseFailAlloc_2578_, 21, v_ltFn_x3f_2544_);
lean_ctor_set(v_reuseFailAlloc_2578_, 22, v_addFn_2545_);
lean_ctor_set(v_reuseFailAlloc_2578_, 23, v_zsmulFn_2546_);
lean_ctor_set(v_reuseFailAlloc_2578_, 24, v_nsmulFn_2547_);
lean_ctor_set(v_reuseFailAlloc_2578_, 25, v_zsmulFn_x3f_2548_);
lean_ctor_set(v_reuseFailAlloc_2578_, 26, v_nsmulFn_x3f_2549_);
lean_ctor_set(v_reuseFailAlloc_2578_, 27, v_homomulFn_x3f_2550_);
lean_ctor_set(v_reuseFailAlloc_2578_, 28, v_subFn_2551_);
lean_ctor_set(v_reuseFailAlloc_2578_, 29, v_negFn_2552_);
lean_ctor_set(v_reuseFailAlloc_2578_, 30, v_vars_2553_);
lean_ctor_set(v_reuseFailAlloc_2578_, 31, v_varMap_2554_);
lean_ctor_set(v_reuseFailAlloc_2578_, 32, v_lowers_2555_);
lean_ctor_set(v_reuseFailAlloc_2578_, 33, v___x_2571_);
lean_ctor_set(v_reuseFailAlloc_2578_, 34, v_diseqs_2557_);
lean_ctor_set(v_reuseFailAlloc_2578_, 35, v_assignment_2558_);
lean_ctor_set(v_reuseFailAlloc_2578_, 36, v_conflict_x3f_2560_);
lean_ctor_set(v_reuseFailAlloc_2578_, 37, v_diseqSplits_2561_);
lean_ctor_set(v_reuseFailAlloc_2578_, 38, v_elimEqs_2562_);
lean_ctor_set(v_reuseFailAlloc_2578_, 39, v_elimStack_2563_);
lean_ctor_set(v_reuseFailAlloc_2578_, 40, v_occurs_2564_);
lean_ctor_set(v_reuseFailAlloc_2578_, 41, v_ignored_2565_);
lean_ctor_set_uint8(v_reuseFailAlloc_2578_, sizeof(void*)*42, v_caseSplits_2559_);
v___x_2573_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
lean_object* v___x_2574_; lean_object* v___x_2576_; 
v___x_2574_ = lean_array_fset(v_xs_x27_2570_, v_a_2505_, v___x_2573_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2574_);
v___x_2576_ = v___x_2520_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2574_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_typeIdOf_2510_);
lean_ctor_set(v_reuseFailAlloc_2577_, 2, v_exprToStructId_2511_);
lean_ctor_set(v_reuseFailAlloc_2577_, 3, v_exprToStructIdEntries_2512_);
lean_ctor_set(v_reuseFailAlloc_2577_, 4, v_forbiddenNatModules_2513_);
lean_ctor_set(v_reuseFailAlloc_2577_, 5, v_natStructs_2514_);
lean_ctor_set(v_reuseFailAlloc_2577_, 6, v_natTypeIdOf_2515_);
lean_ctor_set(v_reuseFailAlloc_2577_, 7, v_exprToNatStructId_2516_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed(lean_object* v_a_2589_, lean_object* v_y_2590_, lean_object* v_fst_2591_, lean_object* v_s_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(v_a_2589_, v_y_2590_, v_fst_2591_, v_s_2592_);
lean_dec(v_y_2590_);
lean_dec(v_a_2589_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object* v_a_2594_, lean_object* v_x_2595_, lean_object* v_c_2596_, lean_object* v_y_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2645_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2613_ = v___x_2610_;
v_isShared_2614_ = v_isSharedCheck_2645_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2645_;
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
v___x_2616_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___y_2619_; lean_object* v_uppers_2627_; lean_object* v_size_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref(v___x_2616_);
v_uppers_2627_ = lean_ctor_get(v_a_2617_, 33);
lean_inc_ref(v_uppers_2627_);
lean_dec(v_a_2617_);
v_size_2628_ = lean_ctor_get(v_uppers_2627_, 2);
v___x_2629_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2630_ = lean_nat_dec_lt(v_y_2597_, v_size_2628_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; 
lean_dec_ref(v_uppers_2627_);
v___x_2631_ = l_outOfBounds___redArg(v___x_2629_);
v___y_2619_ = v___x_2631_;
goto v___jp_2618_;
}
else
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2629_, v_uppers_2627_, v_y_2597_);
lean_dec_ref(v_uppers_2627_);
v___y_2619_ = v___x_2632_;
goto v___jp_2618_;
}
v___jp_2618_:
{
lean_object* v___x_2620_; lean_object* v_fst_2621_; lean_object* v_snd_2622_; lean_object* v___f_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2620_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2595_, v___y_2619_);
lean_dec_ref(v___y_2619_);
v_fst_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_fst_2621_);
v_snd_2622_ = lean_ctor_get(v___x_2620_, 1);
lean_inc(v_snd_2622_);
lean_dec_ref(v___x_2620_);
lean_inc(v_a_2598_);
v___f_2623_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2623_, 0, v_a_2598_);
lean_closure_set(v___f_2623_, 1, v_y_2597_);
lean_closure_set(v___f_2623_, 2, v_fst_2621_);
v___x_2624_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2625_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2624_, v___f_2623_, v_a_2599_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v___x_2626_; 
lean_dec_ref(v___x_2625_);
v___x_2626_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2594_, v_x_2595_, v_c_2596_, v_snd_2622_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
lean_dec(v_snd_2622_);
return v___x_2626_;
}
else
{
lean_dec(v_snd_2622_);
lean_dec_ref(v_c_2596_);
lean_dec(v_x_2595_);
lean_dec(v_a_2594_);
return v___x_2625_;
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec(v_y_2597_);
lean_dec_ref(v_c_2596_);
lean_dec(v_x_2595_);
lean_dec(v_a_2594_);
v_a_2633_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2616_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2616_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
else
{
lean_object* v___x_2641_; lean_object* v___x_2643_; 
lean_dec(v_y_2597_);
lean_dec_ref(v_c_2596_);
lean_dec(v_x_2595_);
lean_dec(v_a_2594_);
v___x_2641_ = lean_box(0);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v___x_2641_);
v___x_2643_ = v___x_2613_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2641_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec(v_y_2597_);
lean_dec_ref(v_c_2596_);
lean_dec(v_x_2595_);
lean_dec(v_a_2594_);
v_a_2646_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2610_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2610_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object* v_a_2654_, lean_object* v_x_2655_, lean_object* v_c_2656_, lean_object* v_y_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_2654_, v_x_2655_, v_c_2656_, v_y_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec(v_a_2658_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(lean_object* v___y_2671_, lean_object* v_a_2672_, lean_object* v_s_2673_){
_start:
{
lean_object* v_structs_2674_; lean_object* v_typeIdOf_2675_; lean_object* v_exprToStructId_2676_; lean_object* v_exprToStructIdEntries_2677_; lean_object* v_forbiddenNatModules_2678_; lean_object* v_natStructs_2679_; lean_object* v_natTypeIdOf_2680_; lean_object* v_exprToNatStructId_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; 
v_structs_2674_ = lean_ctor_get(v_s_2673_, 0);
v_typeIdOf_2675_ = lean_ctor_get(v_s_2673_, 1);
v_exprToStructId_2676_ = lean_ctor_get(v_s_2673_, 2);
v_exprToStructIdEntries_2677_ = lean_ctor_get(v_s_2673_, 3);
v_forbiddenNatModules_2678_ = lean_ctor_get(v_s_2673_, 4);
v_natStructs_2679_ = lean_ctor_get(v_s_2673_, 5);
v_natTypeIdOf_2680_ = lean_ctor_get(v_s_2673_, 6);
v_exprToNatStructId_2681_ = lean_ctor_get(v_s_2673_, 7);
v___x_2682_ = lean_array_get_size(v_structs_2674_);
v___x_2683_ = lean_nat_dec_lt(v___y_2671_, v___x_2682_);
if (v___x_2683_ == 0)
{
lean_dec_ref(v_a_2672_);
return v_s_2673_;
}
else
{
lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2745_; 
lean_inc_ref(v_exprToNatStructId_2681_);
lean_inc_ref(v_natTypeIdOf_2680_);
lean_inc_ref(v_natStructs_2679_);
lean_inc_ref(v_forbiddenNatModules_2678_);
lean_inc_ref(v_exprToStructIdEntries_2677_);
lean_inc_ref(v_exprToStructId_2676_);
lean_inc_ref(v_typeIdOf_2675_);
lean_inc_ref(v_structs_2674_);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_s_2673_);
if (v_isSharedCheck_2745_ == 0)
{
lean_object* v_unused_2746_; lean_object* v_unused_2747_; lean_object* v_unused_2748_; lean_object* v_unused_2749_; lean_object* v_unused_2750_; lean_object* v_unused_2751_; lean_object* v_unused_2752_; lean_object* v_unused_2753_; 
v_unused_2746_ = lean_ctor_get(v_s_2673_, 7);
lean_dec(v_unused_2746_);
v_unused_2747_ = lean_ctor_get(v_s_2673_, 6);
lean_dec(v_unused_2747_);
v_unused_2748_ = lean_ctor_get(v_s_2673_, 5);
lean_dec(v_unused_2748_);
v_unused_2749_ = lean_ctor_get(v_s_2673_, 4);
lean_dec(v_unused_2749_);
v_unused_2750_ = lean_ctor_get(v_s_2673_, 3);
lean_dec(v_unused_2750_);
v_unused_2751_ = lean_ctor_get(v_s_2673_, 2);
lean_dec(v_unused_2751_);
v_unused_2752_ = lean_ctor_get(v_s_2673_, 1);
lean_dec(v_unused_2752_);
v_unused_2753_ = lean_ctor_get(v_s_2673_, 0);
lean_dec(v_unused_2753_);
v___x_2685_ = v_s_2673_;
v_isShared_2686_ = v_isSharedCheck_2745_;
goto v_resetjp_2684_;
}
else
{
lean_dec(v_s_2673_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2745_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v_v_2687_; lean_object* v_id_2688_; lean_object* v_ringId_x3f_2689_; lean_object* v_type_2690_; lean_object* v_u_2691_; lean_object* v_intModuleInst_2692_; lean_object* v_leInst_x3f_2693_; lean_object* v_ltInst_x3f_2694_; lean_object* v_lawfulOrderLTInst_x3f_2695_; lean_object* v_isPreorderInst_x3f_2696_; lean_object* v_orderedAddInst_x3f_2697_; lean_object* v_isLinearInst_x3f_2698_; lean_object* v_noNatDivInst_x3f_2699_; lean_object* v_ringInst_x3f_2700_; lean_object* v_commRingInst_x3f_2701_; lean_object* v_orderedRingInst_x3f_2702_; lean_object* v_fieldInst_x3f_2703_; lean_object* v_charInst_x3f_2704_; lean_object* v_zero_2705_; lean_object* v_ofNatZero_2706_; lean_object* v_one_x3f_2707_; lean_object* v_leFn_x3f_2708_; lean_object* v_ltFn_x3f_2709_; lean_object* v_addFn_2710_; lean_object* v_zsmulFn_2711_; lean_object* v_nsmulFn_2712_; lean_object* v_zsmulFn_x3f_2713_; lean_object* v_nsmulFn_x3f_2714_; lean_object* v_homomulFn_x3f_2715_; lean_object* v_subFn_2716_; lean_object* v_negFn_2717_; lean_object* v_vars_2718_; lean_object* v_varMap_2719_; lean_object* v_lowers_2720_; lean_object* v_uppers_2721_; lean_object* v_diseqs_2722_; lean_object* v_assignment_2723_; uint8_t v_caseSplits_2724_; lean_object* v_conflict_x3f_2725_; lean_object* v_diseqSplits_2726_; lean_object* v_elimEqs_2727_; lean_object* v_elimStack_2728_; lean_object* v_occurs_2729_; lean_object* v_ignored_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2744_; 
v_v_2687_ = lean_array_fget(v_structs_2674_, v___y_2671_);
v_id_2688_ = lean_ctor_get(v_v_2687_, 0);
v_ringId_x3f_2689_ = lean_ctor_get(v_v_2687_, 1);
v_type_2690_ = lean_ctor_get(v_v_2687_, 2);
v_u_2691_ = lean_ctor_get(v_v_2687_, 3);
v_intModuleInst_2692_ = lean_ctor_get(v_v_2687_, 4);
v_leInst_x3f_2693_ = lean_ctor_get(v_v_2687_, 5);
v_ltInst_x3f_2694_ = lean_ctor_get(v_v_2687_, 6);
v_lawfulOrderLTInst_x3f_2695_ = lean_ctor_get(v_v_2687_, 7);
v_isPreorderInst_x3f_2696_ = lean_ctor_get(v_v_2687_, 8);
v_orderedAddInst_x3f_2697_ = lean_ctor_get(v_v_2687_, 9);
v_isLinearInst_x3f_2698_ = lean_ctor_get(v_v_2687_, 10);
v_noNatDivInst_x3f_2699_ = lean_ctor_get(v_v_2687_, 11);
v_ringInst_x3f_2700_ = lean_ctor_get(v_v_2687_, 12);
v_commRingInst_x3f_2701_ = lean_ctor_get(v_v_2687_, 13);
v_orderedRingInst_x3f_2702_ = lean_ctor_get(v_v_2687_, 14);
v_fieldInst_x3f_2703_ = lean_ctor_get(v_v_2687_, 15);
v_charInst_x3f_2704_ = lean_ctor_get(v_v_2687_, 16);
v_zero_2705_ = lean_ctor_get(v_v_2687_, 17);
v_ofNatZero_2706_ = lean_ctor_get(v_v_2687_, 18);
v_one_x3f_2707_ = lean_ctor_get(v_v_2687_, 19);
v_leFn_x3f_2708_ = lean_ctor_get(v_v_2687_, 20);
v_ltFn_x3f_2709_ = lean_ctor_get(v_v_2687_, 21);
v_addFn_2710_ = lean_ctor_get(v_v_2687_, 22);
v_zsmulFn_2711_ = lean_ctor_get(v_v_2687_, 23);
v_nsmulFn_2712_ = lean_ctor_get(v_v_2687_, 24);
v_zsmulFn_x3f_2713_ = lean_ctor_get(v_v_2687_, 25);
v_nsmulFn_x3f_2714_ = lean_ctor_get(v_v_2687_, 26);
v_homomulFn_x3f_2715_ = lean_ctor_get(v_v_2687_, 27);
v_subFn_2716_ = lean_ctor_get(v_v_2687_, 28);
v_negFn_2717_ = lean_ctor_get(v_v_2687_, 29);
v_vars_2718_ = lean_ctor_get(v_v_2687_, 30);
v_varMap_2719_ = lean_ctor_get(v_v_2687_, 31);
v_lowers_2720_ = lean_ctor_get(v_v_2687_, 32);
v_uppers_2721_ = lean_ctor_get(v_v_2687_, 33);
v_diseqs_2722_ = lean_ctor_get(v_v_2687_, 34);
v_assignment_2723_ = lean_ctor_get(v_v_2687_, 35);
v_caseSplits_2724_ = lean_ctor_get_uint8(v_v_2687_, sizeof(void*)*42);
v_conflict_x3f_2725_ = lean_ctor_get(v_v_2687_, 36);
v_diseqSplits_2726_ = lean_ctor_get(v_v_2687_, 37);
v_elimEqs_2727_ = lean_ctor_get(v_v_2687_, 38);
v_elimStack_2728_ = lean_ctor_get(v_v_2687_, 39);
v_occurs_2729_ = lean_ctor_get(v_v_2687_, 40);
v_ignored_2730_ = lean_ctor_get(v_v_2687_, 41);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_v_2687_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2732_ = v_v_2687_;
v_isShared_2733_ = v_isSharedCheck_2744_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_ignored_2730_);
lean_inc(v_occurs_2729_);
lean_inc(v_elimStack_2728_);
lean_inc(v_elimEqs_2727_);
lean_inc(v_diseqSplits_2726_);
lean_inc(v_conflict_x3f_2725_);
lean_inc(v_assignment_2723_);
lean_inc(v_diseqs_2722_);
lean_inc(v_uppers_2721_);
lean_inc(v_lowers_2720_);
lean_inc(v_varMap_2719_);
lean_inc(v_vars_2718_);
lean_inc(v_negFn_2717_);
lean_inc(v_subFn_2716_);
lean_inc(v_homomulFn_x3f_2715_);
lean_inc(v_nsmulFn_x3f_2714_);
lean_inc(v_zsmulFn_x3f_2713_);
lean_inc(v_nsmulFn_2712_);
lean_inc(v_zsmulFn_2711_);
lean_inc(v_addFn_2710_);
lean_inc(v_ltFn_x3f_2709_);
lean_inc(v_leFn_x3f_2708_);
lean_inc(v_one_x3f_2707_);
lean_inc(v_ofNatZero_2706_);
lean_inc(v_zero_2705_);
lean_inc(v_charInst_x3f_2704_);
lean_inc(v_fieldInst_x3f_2703_);
lean_inc(v_orderedRingInst_x3f_2702_);
lean_inc(v_commRingInst_x3f_2701_);
lean_inc(v_ringInst_x3f_2700_);
lean_inc(v_noNatDivInst_x3f_2699_);
lean_inc(v_isLinearInst_x3f_2698_);
lean_inc(v_orderedAddInst_x3f_2697_);
lean_inc(v_isPreorderInst_x3f_2696_);
lean_inc(v_lawfulOrderLTInst_x3f_2695_);
lean_inc(v_ltInst_x3f_2694_);
lean_inc(v_leInst_x3f_2693_);
lean_inc(v_intModuleInst_2692_);
lean_inc(v_u_2691_);
lean_inc(v_type_2690_);
lean_inc(v_ringId_x3f_2689_);
lean_inc(v_id_2688_);
lean_dec(v_v_2687_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2744_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2734_; lean_object* v_xs_x27_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
v___x_2734_ = lean_box(0);
v_xs_x27_2735_ = lean_array_fset(v_structs_2674_, v___y_2671_, v___x_2734_);
v___x_2736_ = l_Lean_PersistentArray_push___redArg(v_ignored_2730_, v_a_2672_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 41, v___x_2736_);
v___x_2738_ = v___x_2732_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_id_2688_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_ringId_x3f_2689_);
lean_ctor_set(v_reuseFailAlloc_2743_, 2, v_type_2690_);
lean_ctor_set(v_reuseFailAlloc_2743_, 3, v_u_2691_);
lean_ctor_set(v_reuseFailAlloc_2743_, 4, v_intModuleInst_2692_);
lean_ctor_set(v_reuseFailAlloc_2743_, 5, v_leInst_x3f_2693_);
lean_ctor_set(v_reuseFailAlloc_2743_, 6, v_ltInst_x3f_2694_);
lean_ctor_set(v_reuseFailAlloc_2743_, 7, v_lawfulOrderLTInst_x3f_2695_);
lean_ctor_set(v_reuseFailAlloc_2743_, 8, v_isPreorderInst_x3f_2696_);
lean_ctor_set(v_reuseFailAlloc_2743_, 9, v_orderedAddInst_x3f_2697_);
lean_ctor_set(v_reuseFailAlloc_2743_, 10, v_isLinearInst_x3f_2698_);
lean_ctor_set(v_reuseFailAlloc_2743_, 11, v_noNatDivInst_x3f_2699_);
lean_ctor_set(v_reuseFailAlloc_2743_, 12, v_ringInst_x3f_2700_);
lean_ctor_set(v_reuseFailAlloc_2743_, 13, v_commRingInst_x3f_2701_);
lean_ctor_set(v_reuseFailAlloc_2743_, 14, v_orderedRingInst_x3f_2702_);
lean_ctor_set(v_reuseFailAlloc_2743_, 15, v_fieldInst_x3f_2703_);
lean_ctor_set(v_reuseFailAlloc_2743_, 16, v_charInst_x3f_2704_);
lean_ctor_set(v_reuseFailAlloc_2743_, 17, v_zero_2705_);
lean_ctor_set(v_reuseFailAlloc_2743_, 18, v_ofNatZero_2706_);
lean_ctor_set(v_reuseFailAlloc_2743_, 19, v_one_x3f_2707_);
lean_ctor_set(v_reuseFailAlloc_2743_, 20, v_leFn_x3f_2708_);
lean_ctor_set(v_reuseFailAlloc_2743_, 21, v_ltFn_x3f_2709_);
lean_ctor_set(v_reuseFailAlloc_2743_, 22, v_addFn_2710_);
lean_ctor_set(v_reuseFailAlloc_2743_, 23, v_zsmulFn_2711_);
lean_ctor_set(v_reuseFailAlloc_2743_, 24, v_nsmulFn_2712_);
lean_ctor_set(v_reuseFailAlloc_2743_, 25, v_zsmulFn_x3f_2713_);
lean_ctor_set(v_reuseFailAlloc_2743_, 26, v_nsmulFn_x3f_2714_);
lean_ctor_set(v_reuseFailAlloc_2743_, 27, v_homomulFn_x3f_2715_);
lean_ctor_set(v_reuseFailAlloc_2743_, 28, v_subFn_2716_);
lean_ctor_set(v_reuseFailAlloc_2743_, 29, v_negFn_2717_);
lean_ctor_set(v_reuseFailAlloc_2743_, 30, v_vars_2718_);
lean_ctor_set(v_reuseFailAlloc_2743_, 31, v_varMap_2719_);
lean_ctor_set(v_reuseFailAlloc_2743_, 32, v_lowers_2720_);
lean_ctor_set(v_reuseFailAlloc_2743_, 33, v_uppers_2721_);
lean_ctor_set(v_reuseFailAlloc_2743_, 34, v_diseqs_2722_);
lean_ctor_set(v_reuseFailAlloc_2743_, 35, v_assignment_2723_);
lean_ctor_set(v_reuseFailAlloc_2743_, 36, v_conflict_x3f_2725_);
lean_ctor_set(v_reuseFailAlloc_2743_, 37, v_diseqSplits_2726_);
lean_ctor_set(v_reuseFailAlloc_2743_, 38, v_elimEqs_2727_);
lean_ctor_set(v_reuseFailAlloc_2743_, 39, v_elimStack_2728_);
lean_ctor_set(v_reuseFailAlloc_2743_, 40, v_occurs_2729_);
lean_ctor_set(v_reuseFailAlloc_2743_, 41, v___x_2736_);
lean_ctor_set_uint8(v_reuseFailAlloc_2743_, sizeof(void*)*42, v_caseSplits_2724_);
v___x_2738_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; lean_object* v___x_2741_; 
v___x_2739_ = lean_array_fset(v_xs_x27_2735_, v___y_2671_, v___x_2738_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 0, v___x_2739_);
v___x_2741_ = v___x_2685_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2739_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_typeIdOf_2675_);
lean_ctor_set(v_reuseFailAlloc_2742_, 2, v_exprToStructId_2676_);
lean_ctor_set(v_reuseFailAlloc_2742_, 3, v_exprToStructIdEntries_2677_);
lean_ctor_set(v_reuseFailAlloc_2742_, 4, v_forbiddenNatModules_2678_);
lean_ctor_set(v_reuseFailAlloc_2742_, 5, v_natStructs_2679_);
lean_ctor_set(v_reuseFailAlloc_2742_, 6, v_natTypeIdOf_2680_);
lean_ctor_set(v_reuseFailAlloc_2742_, 7, v_exprToNatStructId_2681_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed(lean_object* v___y_2754_, lean_object* v_a_2755_, lean_object* v_s_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(v___y_2754_, v_a_2755_, v_s_2756_);
lean_dec(v___y_2754_);
return v_res_2757_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3(void){
_start:
{
lean_object* v_cls_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v_cls_2765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_2767_ = l_Lean_Name_append(v___x_2766_, v_cls_2765_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object* v_c_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v_options_2806_; uint8_t v_hasTrace_2807_; 
v_options_2806_ = lean_ctor_get(v_a_2778_, 2);
v_hasTrace_2807_ = lean_ctor_get_uint8(v_options_2806_, sizeof(void*)*1);
if (v_hasTrace_2807_ == 0)
{
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
v___y_2792_ = v_a_2779_;
goto v___jp_2781_;
}
else
{
lean_object* v_inheritedTraceOptions_2808_; lean_object* v_cls_2809_; lean_object* v___x_2810_; uint8_t v___x_2811_; 
v_inheritedTraceOptions_2808_ = lean_ctor_get(v_a_2778_, 13);
v_cls_2809_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2810_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3);
v___x_2811_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2808_, v_options_2806_, v___x_2810_);
if (v___x_2811_ == 0)
{
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
v___y_2792_ = v_a_2779_;
goto v___jp_2781_;
}
else
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref(v___x_2812_);
v___x_2814_ = l_Lean_MessageData_ofExpr(v_a_2813_);
v___x_2815_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_2809_, v___x_2814_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_dec_ref(v___x_2815_);
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
v___y_2792_ = v_a_2779_;
goto v___jp_2781_;
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
v___jp_2781_:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2768_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___f_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2794_);
lean_dec_ref(v___x_2793_);
lean_inc(v___y_2782_);
v___f_2795_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2795_, 0, v___y_2782_);
lean_closure_set(v___f_2795_, 1, v_a_2794_);
v___x_2796_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2797_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2796_, v___f_2795_, v___y_2783_);
return v___x_2797_;
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
v_a_2798_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2793_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2793_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
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
lean_object* v_p_2851_; lean_object* v_fileName_2852_; lean_object* v_fileMap_2853_; lean_object* v_options_2854_; lean_object* v_currRecDepth_2855_; lean_object* v_maxRecDepth_2856_; lean_object* v_ref_2857_; lean_object* v_currNamespace_2858_; lean_object* v_openDecls_2859_; lean_object* v_initHeartbeats_2860_; lean_object* v_maxHeartbeats_2861_; lean_object* v_quotContext_2862_; lean_object* v_currMacroScope_2863_; uint8_t v_diag_2864_; lean_object* v_cancelTk_x3f_2865_; uint8_t v_suppressElabErrors_2866_; lean_object* v_inheritedTraceOptions_2867_; lean_object* v___x_2919_; uint8_t v___x_2920_; 
v_p_2851_ = lean_ctor_get(v_c_u2082_2838_, 0);
v_fileName_2852_ = lean_ctor_get(v_a_2848_, 0);
lean_inc_ref(v_fileName_2852_);
v_fileMap_2853_ = lean_ctor_get(v_a_2848_, 1);
lean_inc_ref(v_fileMap_2853_);
v_options_2854_ = lean_ctor_get(v_a_2848_, 2);
lean_inc_ref(v_options_2854_);
v_currRecDepth_2855_ = lean_ctor_get(v_a_2848_, 3);
lean_inc(v_currRecDepth_2855_);
v_maxRecDepth_2856_ = lean_ctor_get(v_a_2848_, 4);
lean_inc(v_maxRecDepth_2856_);
v_ref_2857_ = lean_ctor_get(v_a_2848_, 5);
lean_inc(v_ref_2857_);
v_currNamespace_2858_ = lean_ctor_get(v_a_2848_, 6);
lean_inc(v_currNamespace_2858_);
v_openDecls_2859_ = lean_ctor_get(v_a_2848_, 7);
lean_inc(v_openDecls_2859_);
v_initHeartbeats_2860_ = lean_ctor_get(v_a_2848_, 8);
lean_inc(v_initHeartbeats_2860_);
v_maxHeartbeats_2861_ = lean_ctor_get(v_a_2848_, 9);
lean_inc(v_maxHeartbeats_2861_);
v_quotContext_2862_ = lean_ctor_get(v_a_2848_, 10);
lean_inc(v_quotContext_2862_);
v_currMacroScope_2863_ = lean_ctor_get(v_a_2848_, 11);
lean_inc(v_currMacroScope_2863_);
v_diag_2864_ = lean_ctor_get_uint8(v_a_2848_, sizeof(void*)*14);
v_cancelTk_x3f_2865_ = lean_ctor_get(v_a_2848_, 12);
lean_inc(v_cancelTk_x3f_2865_);
v_suppressElabErrors_2866_ = lean_ctor_get_uint8(v_a_2848_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2867_ = lean_ctor_get(v_a_2848_, 13);
lean_inc_ref(v_inheritedTraceOptions_2867_);
lean_dec_ref(v_a_2848_);
v___x_2919_ = lean_unsigned_to_nat(0u);
v___x_2920_ = lean_nat_dec_eq(v_maxRecDepth_2856_, v___x_2919_);
if (v___x_2920_ == 0)
{
uint8_t v___x_2921_; 
v___x_2921_ = lean_nat_dec_eq(v_currRecDepth_2855_, v_maxRecDepth_2856_);
if (v___x_2921_ == 0)
{
goto v___jp_2868_;
}
else
{
lean_object* v___x_2922_; 
lean_dec_ref(v_inheritedTraceOptions_2867_);
lean_dec(v_cancelTk_x3f_2865_);
lean_dec(v_currMacroScope_2863_);
lean_dec(v_quotContext_2862_);
lean_dec(v_maxHeartbeats_2861_);
lean_dec(v_initHeartbeats_2860_);
lean_dec(v_openDecls_2859_);
lean_dec(v_currNamespace_2858_);
lean_dec(v_maxRecDepth_2856_);
lean_dec(v_currRecDepth_2855_);
lean_dec_ref(v_options_2854_);
lean_dec_ref(v_fileMap_2853_);
lean_dec_ref(v_fileName_2852_);
lean_dec_ref(v_c_u2082_2838_);
v___x_2922_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_2857_);
return v___x_2922_;
}
}
else
{
goto v___jp_2868_;
}
v___jp_2868_:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2869_ = lean_unsigned_to_nat(1u);
v___x_2870_ = lean_nat_add(v_currRecDepth_2855_, v___x_2869_);
lean_dec(v_currRecDepth_2855_);
v___x_2871_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2871_, 0, v_fileName_2852_);
lean_ctor_set(v___x_2871_, 1, v_fileMap_2853_);
lean_ctor_set(v___x_2871_, 2, v_options_2854_);
lean_ctor_set(v___x_2871_, 3, v___x_2870_);
lean_ctor_set(v___x_2871_, 4, v_maxRecDepth_2856_);
lean_ctor_set(v___x_2871_, 5, v_ref_2857_);
lean_ctor_set(v___x_2871_, 6, v_currNamespace_2858_);
lean_ctor_set(v___x_2871_, 7, v_openDecls_2859_);
lean_ctor_set(v___x_2871_, 8, v_initHeartbeats_2860_);
lean_ctor_set(v___x_2871_, 9, v_maxHeartbeats_2861_);
lean_ctor_set(v___x_2871_, 10, v_quotContext_2862_);
lean_ctor_set(v___x_2871_, 11, v_currMacroScope_2863_);
lean_ctor_set(v___x_2871_, 12, v_cancelTk_x3f_2865_);
lean_ctor_set(v___x_2871_, 13, v_inheritedTraceOptions_2867_);
lean_ctor_set_uint8(v___x_2871_, sizeof(void*)*14, v_diag_2864_);
lean_ctor_set_uint8(v___x_2871_, sizeof(void*)*14 + 1, v_suppressElabErrors_2866_);
v___x_2872_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2851_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v___x_2871_, v_a_2849_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2910_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2875_ = v___x_2872_;
v_isShared_2876_ = v_isSharedCheck_2910_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2872_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2910_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
if (lean_obj_tag(v_a_2873_) == 1)
{
lean_object* v_val_2877_; lean_object* v_snd_2878_; lean_object* v_snd_2879_; lean_object* v_fst_2880_; lean_object* v_fst_2881_; lean_object* v_p_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_del_object(v___x_2875_);
v_val_2877_ = lean_ctor_get(v_a_2873_, 0);
lean_inc(v_val_2877_);
lean_dec_ref(v_a_2873_);
v_snd_2878_ = lean_ctor_get(v_val_2877_, 1);
lean_inc(v_snd_2878_);
v_snd_2879_ = lean_ctor_get(v_snd_2878_, 1);
lean_inc(v_snd_2879_);
v_fst_2880_ = lean_ctor_get(v_val_2877_, 0);
lean_inc(v_fst_2880_);
lean_dec(v_val_2877_);
v_fst_2881_ = lean_ctor_get(v_snd_2878_, 0);
lean_inc(v_fst_2881_);
lean_dec(v_snd_2878_);
v_p_2882_ = lean_ctor_get(v_snd_2879_, 0);
v___x_2883_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2882_, v_fst_2881_);
lean_inc_ref(v_c_u2082_2838_);
v___x_2884_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v___x_2883_, v_fst_2881_, v_snd_2879_, v_fst_2880_, v_c_u2082_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v___x_2871_, v_a_2849_);
lean_dec(v_fst_2881_);
lean_dec(v___x_2883_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
lean_dec_ref(v___x_2884_);
if (lean_obj_tag(v_a_2885_) == 1)
{
lean_object* v_val_2886_; 
lean_dec_ref(v_c_u2082_2838_);
v_val_2886_ = lean_ctor_get(v_a_2885_, 0);
lean_inc(v_val_2886_);
lean_dec_ref(v_a_2885_);
v_c_u2082_2838_ = v_val_2886_;
v_a_2848_ = v___x_2871_;
goto _start;
}
else
{
lean_object* v___x_2888_; 
lean_dec(v_a_2885_);
v___x_2888_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_u2082_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v___x_2871_, v_a_2849_);
lean_dec_ref(v___x_2871_);
lean_dec_ref(v_c_u2082_2838_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2896_; 
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2896_ == 0)
{
lean_object* v_unused_2897_; 
v_unused_2897_ = lean_ctor_get(v___x_2888_, 0);
lean_dec(v_unused_2897_);
v___x_2890_ = v___x_2888_;
v_isShared_2891_ = v_isSharedCheck_2896_;
goto v_resetjp_2889_;
}
else
{
lean_dec(v___x_2888_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2896_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2892_; lean_object* v___x_2894_; 
v___x_2892_ = lean_box(0);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v___x_2892_);
v___x_2894_ = v___x_2890_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2892_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
v_a_2898_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2888_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2888_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2871_);
lean_dec_ref(v_c_u2082_2838_);
return v___x_2884_;
}
}
else
{
lean_object* v___x_2906_; lean_object* v___x_2908_; 
lean_dec(v_a_2873_);
lean_dec_ref(v___x_2871_);
v___x_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2906_, 0, v_c_u2082_2838_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v___x_2906_);
v___x_2908_ = v___x_2875_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2906_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec_ref(v___x_2871_);
lean_dec_ref(v_c_u2082_2838_);
v_a_2911_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2872_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2872_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object* v_c_u2082_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_u2082_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_);
lean_dec(v_a_2934_);
lean_dec(v_a_2932_);
lean_dec_ref(v_a_2931_);
lean_dec(v_a_2930_);
lean_dec_ref(v_a_2929_);
lean_dec(v_a_2928_);
lean_dec_ref(v_a_2927_);
lean_dec(v_a_2926_);
lean_dec(v_a_2925_);
lean_dec(v_a_2924_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object* v_val_2937_, lean_object* v_x_2938_, size_t v_x_2939_, size_t v_x_2940_){
_start:
{
if (lean_obj_tag(v_x_2938_) == 0)
{
lean_object* v_cs_2941_; size_t v_j_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; uint8_t v___x_2945_; 
v_cs_2941_ = lean_ctor_get(v_x_2938_, 0);
v_j_2942_ = lean_usize_shift_right(v_x_2939_, v_x_2940_);
v___x_2943_ = lean_usize_to_nat(v_j_2942_);
v___x_2944_ = lean_array_get_size(v_cs_2941_);
v___x_2945_ = lean_nat_dec_lt(v___x_2943_, v___x_2944_);
if (v___x_2945_ == 0)
{
lean_dec(v___x_2943_);
lean_dec_ref(v_val_2937_);
return v_x_2938_;
}
else
{
lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2963_; 
lean_inc_ref(v_cs_2941_);
v_isSharedCheck_2963_ = !lean_is_exclusive(v_x_2938_);
if (v_isSharedCheck_2963_ == 0)
{
lean_object* v_unused_2964_; 
v_unused_2964_ = lean_ctor_get(v_x_2938_, 0);
lean_dec(v_unused_2964_);
v___x_2947_ = v_x_2938_;
v_isShared_2948_ = v_isSharedCheck_2963_;
goto v_resetjp_2946_;
}
else
{
lean_dec(v_x_2938_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2963_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
size_t v___x_2949_; size_t v___x_2950_; size_t v___x_2951_; size_t v_i_2952_; size_t v___x_2953_; size_t v_shift_2954_; lean_object* v_v_2955_; lean_object* v___x_2956_; lean_object* v_xs_x27_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2961_; 
v___x_2949_ = ((size_t)1ULL);
v___x_2950_ = lean_usize_shift_left(v___x_2949_, v_x_2940_);
v___x_2951_ = lean_usize_sub(v___x_2950_, v___x_2949_);
v_i_2952_ = lean_usize_land(v_x_2939_, v___x_2951_);
v___x_2953_ = ((size_t)5ULL);
v_shift_2954_ = lean_usize_sub(v_x_2940_, v___x_2953_);
v_v_2955_ = lean_array_fget(v_cs_2941_, v___x_2943_);
v___x_2956_ = lean_box(0);
v_xs_x27_2957_ = lean_array_fset(v_cs_2941_, v___x_2943_, v___x_2956_);
v___x_2958_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2937_, v_v_2955_, v_i_2952_, v_shift_2954_);
v___x_2959_ = lean_array_fset(v_xs_x27_2957_, v___x_2943_, v___x_2958_);
lean_dec(v___x_2943_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 0, v___x_2959_);
v___x_2961_ = v___x_2947_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2959_);
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
else
{
lean_object* v_vs_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; uint8_t v___x_2968_; 
v_vs_2965_ = lean_ctor_get(v_x_2938_, 0);
v___x_2966_ = lean_usize_to_nat(v_x_2939_);
v___x_2967_ = lean_array_get_size(v_vs_2965_);
v___x_2968_ = lean_nat_dec_lt(v___x_2966_, v___x_2967_);
if (v___x_2968_ == 0)
{
lean_dec(v___x_2966_);
lean_dec_ref(v_val_2937_);
return v_x_2938_;
}
else
{
lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2980_; 
lean_inc_ref(v_vs_2965_);
v_isSharedCheck_2980_ = !lean_is_exclusive(v_x_2938_);
if (v_isSharedCheck_2980_ == 0)
{
lean_object* v_unused_2981_; 
v_unused_2981_ = lean_ctor_get(v_x_2938_, 0);
lean_dec(v_unused_2981_);
v___x_2970_ = v_x_2938_;
v_isShared_2971_ = v_isSharedCheck_2980_;
goto v_resetjp_2969_;
}
else
{
lean_dec(v_x_2938_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2980_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v_v_2972_; lean_object* v___x_2973_; lean_object* v_xs_x27_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2978_; 
v_v_2972_ = lean_array_fget(v_vs_2965_, v___x_2966_);
v___x_2973_ = lean_box(0);
v_xs_x27_2974_ = lean_array_fset(v_vs_2965_, v___x_2966_, v___x_2973_);
v___x_2975_ = l_Lean_PersistentArray_push___redArg(v_v_2972_, v_val_2937_);
v___x_2976_ = lean_array_fset(v_xs_x27_2974_, v___x_2966_, v___x_2975_);
lean_dec(v___x_2966_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 0, v___x_2976_);
v___x_2978_ = v___x_2970_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_val_2982_, lean_object* v_x_2983_, lean_object* v_x_2984_, lean_object* v_x_2985_){
_start:
{
size_t v_x_53643__boxed_2986_; size_t v_x_53644__boxed_2987_; lean_object* v_res_2988_; 
v_x_53643__boxed_2986_ = lean_unbox_usize(v_x_2984_);
lean_dec(v_x_2984_);
v_x_53644__boxed_2987_ = lean_unbox_usize(v_x_2985_);
lean_dec(v_x_2985_);
v_res_2988_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2982_, v_x_2983_, v_x_53643__boxed_2986_, v_x_53644__boxed_2987_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object* v_val_2989_, lean_object* v_t_2990_, lean_object* v_i_2991_){
_start:
{
lean_object* v_root_2992_; lean_object* v_tail_2993_; lean_object* v_size_2994_; size_t v_shift_2995_; lean_object* v_tailOff_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3020_; 
v_root_2992_ = lean_ctor_get(v_t_2990_, 0);
v_tail_2993_ = lean_ctor_get(v_t_2990_, 1);
v_size_2994_ = lean_ctor_get(v_t_2990_, 2);
v_shift_2995_ = lean_ctor_get_usize(v_t_2990_, 4);
v_tailOff_2996_ = lean_ctor_get(v_t_2990_, 3);
v_isSharedCheck_3020_ = !lean_is_exclusive(v_t_2990_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_2998_ = v_t_2990_;
v_isShared_2999_ = v_isSharedCheck_3020_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_tailOff_2996_);
lean_inc(v_size_2994_);
lean_inc(v_tail_2993_);
lean_inc(v_root_2992_);
lean_dec(v_t_2990_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3020_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
uint8_t v___x_3000_; 
v___x_3000_ = lean_nat_dec_le(v_tailOff_2996_, v_i_2991_);
if (v___x_3000_ == 0)
{
size_t v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3004_; 
v___x_3001_ = lean_usize_of_nat(v_i_2991_);
v___x_3002_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2989_, v_root_2992_, v___x_3001_, v_shift_2995_);
if (v_isShared_2999_ == 0)
{
lean_ctor_set(v___x_2998_, 0, v___x_3002_);
v___x_3004_ = v___x_2998_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_3002_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_tail_2993_);
lean_ctor_set(v_reuseFailAlloc_3005_, 2, v_size_2994_);
lean_ctor_set(v_reuseFailAlloc_3005_, 3, v_tailOff_2996_);
lean_ctor_set_usize(v_reuseFailAlloc_3005_, 4, v_shift_2995_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
else
{
lean_object* v___x_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v___x_3006_ = lean_nat_sub(v_i_2991_, v_tailOff_2996_);
v___x_3007_ = lean_array_get_size(v_tail_2993_);
v___x_3008_ = lean_nat_dec_lt(v___x_3006_, v___x_3007_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3010_; 
lean_dec(v___x_3006_);
lean_dec_ref(v_val_2989_);
if (v_isShared_2999_ == 0)
{
v___x_3010_ = v___x_2998_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_root_2992_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_tail_2993_);
lean_ctor_set(v_reuseFailAlloc_3011_, 2, v_size_2994_);
lean_ctor_set(v_reuseFailAlloc_3011_, 3, v_tailOff_2996_);
lean_ctor_set_usize(v_reuseFailAlloc_3011_, 4, v_shift_2995_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
else
{
lean_object* v_v_3012_; lean_object* v___x_3013_; lean_object* v_xs_x27_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3018_; 
v_v_3012_ = lean_array_fget(v_tail_2993_, v___x_3006_);
v___x_3013_ = lean_box(0);
v_xs_x27_3014_ = lean_array_fset(v_tail_2993_, v___x_3006_, v___x_3013_);
v___x_3015_ = l_Lean_PersistentArray_push___redArg(v_v_3012_, v_val_2989_);
v___x_3016_ = lean_array_fset(v_xs_x27_3014_, v___x_3006_, v___x_3015_);
lean_dec(v___x_3006_);
if (v_isShared_2999_ == 0)
{
lean_ctor_set(v___x_2998_, 1, v___x_3016_);
v___x_3018_ = v___x_2998_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_root_2992_);
lean_ctor_set(v_reuseFailAlloc_3019_, 1, v___x_3016_);
lean_ctor_set(v_reuseFailAlloc_3019_, 2, v_size_2994_);
lean_ctor_set(v_reuseFailAlloc_3019_, 3, v_tailOff_2996_);
lean_ctor_set_usize(v_reuseFailAlloc_3019_, 4, v_shift_2995_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object* v_val_3021_, lean_object* v_t_3022_, lean_object* v_i_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3021_, v_t_3022_, v_i_3023_);
lean_dec(v_i_3023_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(lean_object* v___y_3025_, lean_object* v_val_3026_, lean_object* v_v_3027_, lean_object* v_s_3028_){
_start:
{
lean_object* v_structs_3029_; lean_object* v_typeIdOf_3030_; lean_object* v_exprToStructId_3031_; lean_object* v_exprToStructIdEntries_3032_; lean_object* v_forbiddenNatModules_3033_; lean_object* v_natStructs_3034_; lean_object* v_natTypeIdOf_3035_; lean_object* v_exprToNatStructId_3036_; lean_object* v___x_3037_; uint8_t v___x_3038_; 
v_structs_3029_ = lean_ctor_get(v_s_3028_, 0);
v_typeIdOf_3030_ = lean_ctor_get(v_s_3028_, 1);
v_exprToStructId_3031_ = lean_ctor_get(v_s_3028_, 2);
v_exprToStructIdEntries_3032_ = lean_ctor_get(v_s_3028_, 3);
v_forbiddenNatModules_3033_ = lean_ctor_get(v_s_3028_, 4);
v_natStructs_3034_ = lean_ctor_get(v_s_3028_, 5);
v_natTypeIdOf_3035_ = lean_ctor_get(v_s_3028_, 6);
v_exprToNatStructId_3036_ = lean_ctor_get(v_s_3028_, 7);
v___x_3037_ = lean_array_get_size(v_structs_3029_);
v___x_3038_ = lean_nat_dec_lt(v___y_3025_, v___x_3037_);
if (v___x_3038_ == 0)
{
lean_dec_ref(v_val_3026_);
return v_s_3028_;
}
else
{
lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3100_; 
lean_inc_ref(v_exprToNatStructId_3036_);
lean_inc_ref(v_natTypeIdOf_3035_);
lean_inc_ref(v_natStructs_3034_);
lean_inc_ref(v_forbiddenNatModules_3033_);
lean_inc_ref(v_exprToStructIdEntries_3032_);
lean_inc_ref(v_exprToStructId_3031_);
lean_inc_ref(v_typeIdOf_3030_);
lean_inc_ref(v_structs_3029_);
v_isSharedCheck_3100_ = !lean_is_exclusive(v_s_3028_);
if (v_isSharedCheck_3100_ == 0)
{
lean_object* v_unused_3101_; lean_object* v_unused_3102_; lean_object* v_unused_3103_; lean_object* v_unused_3104_; lean_object* v_unused_3105_; lean_object* v_unused_3106_; lean_object* v_unused_3107_; lean_object* v_unused_3108_; 
v_unused_3101_ = lean_ctor_get(v_s_3028_, 7);
lean_dec(v_unused_3101_);
v_unused_3102_ = lean_ctor_get(v_s_3028_, 6);
lean_dec(v_unused_3102_);
v_unused_3103_ = lean_ctor_get(v_s_3028_, 5);
lean_dec(v_unused_3103_);
v_unused_3104_ = lean_ctor_get(v_s_3028_, 4);
lean_dec(v_unused_3104_);
v_unused_3105_ = lean_ctor_get(v_s_3028_, 3);
lean_dec(v_unused_3105_);
v_unused_3106_ = lean_ctor_get(v_s_3028_, 2);
lean_dec(v_unused_3106_);
v_unused_3107_ = lean_ctor_get(v_s_3028_, 1);
lean_dec(v_unused_3107_);
v_unused_3108_ = lean_ctor_get(v_s_3028_, 0);
lean_dec(v_unused_3108_);
v___x_3040_ = v_s_3028_;
v_isShared_3041_ = v_isSharedCheck_3100_;
goto v_resetjp_3039_;
}
else
{
lean_dec(v_s_3028_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3100_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v_v_3042_; lean_object* v_id_3043_; lean_object* v_ringId_x3f_3044_; lean_object* v_type_3045_; lean_object* v_u_3046_; lean_object* v_intModuleInst_3047_; lean_object* v_leInst_x3f_3048_; lean_object* v_ltInst_x3f_3049_; lean_object* v_lawfulOrderLTInst_x3f_3050_; lean_object* v_isPreorderInst_x3f_3051_; lean_object* v_orderedAddInst_x3f_3052_; lean_object* v_isLinearInst_x3f_3053_; lean_object* v_noNatDivInst_x3f_3054_; lean_object* v_ringInst_x3f_3055_; lean_object* v_commRingInst_x3f_3056_; lean_object* v_orderedRingInst_x3f_3057_; lean_object* v_fieldInst_x3f_3058_; lean_object* v_charInst_x3f_3059_; lean_object* v_zero_3060_; lean_object* v_ofNatZero_3061_; lean_object* v_one_x3f_3062_; lean_object* v_leFn_x3f_3063_; lean_object* v_ltFn_x3f_3064_; lean_object* v_addFn_3065_; lean_object* v_zsmulFn_3066_; lean_object* v_nsmulFn_3067_; lean_object* v_zsmulFn_x3f_3068_; lean_object* v_nsmulFn_x3f_3069_; lean_object* v_homomulFn_x3f_3070_; lean_object* v_subFn_3071_; lean_object* v_negFn_3072_; lean_object* v_vars_3073_; lean_object* v_varMap_3074_; lean_object* v_lowers_3075_; lean_object* v_uppers_3076_; lean_object* v_diseqs_3077_; lean_object* v_assignment_3078_; uint8_t v_caseSplits_3079_; lean_object* v_conflict_x3f_3080_; lean_object* v_diseqSplits_3081_; lean_object* v_elimEqs_3082_; lean_object* v_elimStack_3083_; lean_object* v_occurs_3084_; lean_object* v_ignored_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3099_; 
v_v_3042_ = lean_array_fget(v_structs_3029_, v___y_3025_);
v_id_3043_ = lean_ctor_get(v_v_3042_, 0);
v_ringId_x3f_3044_ = lean_ctor_get(v_v_3042_, 1);
v_type_3045_ = lean_ctor_get(v_v_3042_, 2);
v_u_3046_ = lean_ctor_get(v_v_3042_, 3);
v_intModuleInst_3047_ = lean_ctor_get(v_v_3042_, 4);
v_leInst_x3f_3048_ = lean_ctor_get(v_v_3042_, 5);
v_ltInst_x3f_3049_ = lean_ctor_get(v_v_3042_, 6);
v_lawfulOrderLTInst_x3f_3050_ = lean_ctor_get(v_v_3042_, 7);
v_isPreorderInst_x3f_3051_ = lean_ctor_get(v_v_3042_, 8);
v_orderedAddInst_x3f_3052_ = lean_ctor_get(v_v_3042_, 9);
v_isLinearInst_x3f_3053_ = lean_ctor_get(v_v_3042_, 10);
v_noNatDivInst_x3f_3054_ = lean_ctor_get(v_v_3042_, 11);
v_ringInst_x3f_3055_ = lean_ctor_get(v_v_3042_, 12);
v_commRingInst_x3f_3056_ = lean_ctor_get(v_v_3042_, 13);
v_orderedRingInst_x3f_3057_ = lean_ctor_get(v_v_3042_, 14);
v_fieldInst_x3f_3058_ = lean_ctor_get(v_v_3042_, 15);
v_charInst_x3f_3059_ = lean_ctor_get(v_v_3042_, 16);
v_zero_3060_ = lean_ctor_get(v_v_3042_, 17);
v_ofNatZero_3061_ = lean_ctor_get(v_v_3042_, 18);
v_one_x3f_3062_ = lean_ctor_get(v_v_3042_, 19);
v_leFn_x3f_3063_ = lean_ctor_get(v_v_3042_, 20);
v_ltFn_x3f_3064_ = lean_ctor_get(v_v_3042_, 21);
v_addFn_3065_ = lean_ctor_get(v_v_3042_, 22);
v_zsmulFn_3066_ = lean_ctor_get(v_v_3042_, 23);
v_nsmulFn_3067_ = lean_ctor_get(v_v_3042_, 24);
v_zsmulFn_x3f_3068_ = lean_ctor_get(v_v_3042_, 25);
v_nsmulFn_x3f_3069_ = lean_ctor_get(v_v_3042_, 26);
v_homomulFn_x3f_3070_ = lean_ctor_get(v_v_3042_, 27);
v_subFn_3071_ = lean_ctor_get(v_v_3042_, 28);
v_negFn_3072_ = lean_ctor_get(v_v_3042_, 29);
v_vars_3073_ = lean_ctor_get(v_v_3042_, 30);
v_varMap_3074_ = lean_ctor_get(v_v_3042_, 31);
v_lowers_3075_ = lean_ctor_get(v_v_3042_, 32);
v_uppers_3076_ = lean_ctor_get(v_v_3042_, 33);
v_diseqs_3077_ = lean_ctor_get(v_v_3042_, 34);
v_assignment_3078_ = lean_ctor_get(v_v_3042_, 35);
v_caseSplits_3079_ = lean_ctor_get_uint8(v_v_3042_, sizeof(void*)*42);
v_conflict_x3f_3080_ = lean_ctor_get(v_v_3042_, 36);
v_diseqSplits_3081_ = lean_ctor_get(v_v_3042_, 37);
v_elimEqs_3082_ = lean_ctor_get(v_v_3042_, 38);
v_elimStack_3083_ = lean_ctor_get(v_v_3042_, 39);
v_occurs_3084_ = lean_ctor_get(v_v_3042_, 40);
v_ignored_3085_ = lean_ctor_get(v_v_3042_, 41);
v_isSharedCheck_3099_ = !lean_is_exclusive(v_v_3042_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3087_ = v_v_3042_;
v_isShared_3088_ = v_isSharedCheck_3099_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_ignored_3085_);
lean_inc(v_occurs_3084_);
lean_inc(v_elimStack_3083_);
lean_inc(v_elimEqs_3082_);
lean_inc(v_diseqSplits_3081_);
lean_inc(v_conflict_x3f_3080_);
lean_inc(v_assignment_3078_);
lean_inc(v_diseqs_3077_);
lean_inc(v_uppers_3076_);
lean_inc(v_lowers_3075_);
lean_inc(v_varMap_3074_);
lean_inc(v_vars_3073_);
lean_inc(v_negFn_3072_);
lean_inc(v_subFn_3071_);
lean_inc(v_homomulFn_x3f_3070_);
lean_inc(v_nsmulFn_x3f_3069_);
lean_inc(v_zsmulFn_x3f_3068_);
lean_inc(v_nsmulFn_3067_);
lean_inc(v_zsmulFn_3066_);
lean_inc(v_addFn_3065_);
lean_inc(v_ltFn_x3f_3064_);
lean_inc(v_leFn_x3f_3063_);
lean_inc(v_one_x3f_3062_);
lean_inc(v_ofNatZero_3061_);
lean_inc(v_zero_3060_);
lean_inc(v_charInst_x3f_3059_);
lean_inc(v_fieldInst_x3f_3058_);
lean_inc(v_orderedRingInst_x3f_3057_);
lean_inc(v_commRingInst_x3f_3056_);
lean_inc(v_ringInst_x3f_3055_);
lean_inc(v_noNatDivInst_x3f_3054_);
lean_inc(v_isLinearInst_x3f_3053_);
lean_inc(v_orderedAddInst_x3f_3052_);
lean_inc(v_isPreorderInst_x3f_3051_);
lean_inc(v_lawfulOrderLTInst_x3f_3050_);
lean_inc(v_ltInst_x3f_3049_);
lean_inc(v_leInst_x3f_3048_);
lean_inc(v_intModuleInst_3047_);
lean_inc(v_u_3046_);
lean_inc(v_type_3045_);
lean_inc(v_ringId_x3f_3044_);
lean_inc(v_id_3043_);
lean_dec(v_v_3042_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3099_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3089_; lean_object* v_xs_x27_3090_; lean_object* v___x_3091_; lean_object* v___x_3093_; 
v___x_3089_ = lean_box(0);
v_xs_x27_3090_ = lean_array_fset(v_structs_3029_, v___y_3025_, v___x_3089_);
v___x_3091_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3026_, v_diseqs_3077_, v_v_3027_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 34, v___x_3091_);
v___x_3093_ = v___x_3087_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_id_3043_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_ringId_x3f_3044_);
lean_ctor_set(v_reuseFailAlloc_3098_, 2, v_type_3045_);
lean_ctor_set(v_reuseFailAlloc_3098_, 3, v_u_3046_);
lean_ctor_set(v_reuseFailAlloc_3098_, 4, v_intModuleInst_3047_);
lean_ctor_set(v_reuseFailAlloc_3098_, 5, v_leInst_x3f_3048_);
lean_ctor_set(v_reuseFailAlloc_3098_, 6, v_ltInst_x3f_3049_);
lean_ctor_set(v_reuseFailAlloc_3098_, 7, v_lawfulOrderLTInst_x3f_3050_);
lean_ctor_set(v_reuseFailAlloc_3098_, 8, v_isPreorderInst_x3f_3051_);
lean_ctor_set(v_reuseFailAlloc_3098_, 9, v_orderedAddInst_x3f_3052_);
lean_ctor_set(v_reuseFailAlloc_3098_, 10, v_isLinearInst_x3f_3053_);
lean_ctor_set(v_reuseFailAlloc_3098_, 11, v_noNatDivInst_x3f_3054_);
lean_ctor_set(v_reuseFailAlloc_3098_, 12, v_ringInst_x3f_3055_);
lean_ctor_set(v_reuseFailAlloc_3098_, 13, v_commRingInst_x3f_3056_);
lean_ctor_set(v_reuseFailAlloc_3098_, 14, v_orderedRingInst_x3f_3057_);
lean_ctor_set(v_reuseFailAlloc_3098_, 15, v_fieldInst_x3f_3058_);
lean_ctor_set(v_reuseFailAlloc_3098_, 16, v_charInst_x3f_3059_);
lean_ctor_set(v_reuseFailAlloc_3098_, 17, v_zero_3060_);
lean_ctor_set(v_reuseFailAlloc_3098_, 18, v_ofNatZero_3061_);
lean_ctor_set(v_reuseFailAlloc_3098_, 19, v_one_x3f_3062_);
lean_ctor_set(v_reuseFailAlloc_3098_, 20, v_leFn_x3f_3063_);
lean_ctor_set(v_reuseFailAlloc_3098_, 21, v_ltFn_x3f_3064_);
lean_ctor_set(v_reuseFailAlloc_3098_, 22, v_addFn_3065_);
lean_ctor_set(v_reuseFailAlloc_3098_, 23, v_zsmulFn_3066_);
lean_ctor_set(v_reuseFailAlloc_3098_, 24, v_nsmulFn_3067_);
lean_ctor_set(v_reuseFailAlloc_3098_, 25, v_zsmulFn_x3f_3068_);
lean_ctor_set(v_reuseFailAlloc_3098_, 26, v_nsmulFn_x3f_3069_);
lean_ctor_set(v_reuseFailAlloc_3098_, 27, v_homomulFn_x3f_3070_);
lean_ctor_set(v_reuseFailAlloc_3098_, 28, v_subFn_3071_);
lean_ctor_set(v_reuseFailAlloc_3098_, 29, v_negFn_3072_);
lean_ctor_set(v_reuseFailAlloc_3098_, 30, v_vars_3073_);
lean_ctor_set(v_reuseFailAlloc_3098_, 31, v_varMap_3074_);
lean_ctor_set(v_reuseFailAlloc_3098_, 32, v_lowers_3075_);
lean_ctor_set(v_reuseFailAlloc_3098_, 33, v_uppers_3076_);
lean_ctor_set(v_reuseFailAlloc_3098_, 34, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3098_, 35, v_assignment_3078_);
lean_ctor_set(v_reuseFailAlloc_3098_, 36, v_conflict_x3f_3080_);
lean_ctor_set(v_reuseFailAlloc_3098_, 37, v_diseqSplits_3081_);
lean_ctor_set(v_reuseFailAlloc_3098_, 38, v_elimEqs_3082_);
lean_ctor_set(v_reuseFailAlloc_3098_, 39, v_elimStack_3083_);
lean_ctor_set(v_reuseFailAlloc_3098_, 40, v_occurs_3084_);
lean_ctor_set(v_reuseFailAlloc_3098_, 41, v_ignored_3085_);
lean_ctor_set_uint8(v_reuseFailAlloc_3098_, sizeof(void*)*42, v_caseSplits_3079_);
v___x_3093_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3094_ = lean_array_fset(v_xs_x27_3090_, v___y_3025_, v___x_3093_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v___x_3094_);
v___x_3096_ = v___x_3040_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3094_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v_typeIdOf_3030_);
lean_ctor_set(v_reuseFailAlloc_3097_, 2, v_exprToStructId_3031_);
lean_ctor_set(v_reuseFailAlloc_3097_, 3, v_exprToStructIdEntries_3032_);
lean_ctor_set(v_reuseFailAlloc_3097_, 4, v_forbiddenNatModules_3033_);
lean_ctor_set(v_reuseFailAlloc_3097_, 5, v_natStructs_3034_);
lean_ctor_set(v_reuseFailAlloc_3097_, 6, v_natTypeIdOf_3035_);
lean_ctor_set(v_reuseFailAlloc_3097_, 7, v_exprToNatStructId_3036_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed(lean_object* v___y_3109_, lean_object* v_val_3110_, lean_object* v_v_3111_, lean_object* v_s_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(v___y_3109_, v_val_3110_, v_v_3111_, v_s_3112_);
lean_dec(v_v_3111_);
lean_dec(v___y_3109_);
return v_res_3113_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2(void){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3121_ = l_Lean_Name_append(v___x_3120_, v___x_3119_);
return v___x_3121_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3129_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3130_ = l_Lean_Name_append(v___x_3129_, v___x_3128_);
return v___x_3130_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7(void){
_start:
{
lean_object* v_cls_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v_cls_3135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3137_ = l_Lean_Name_append(v___x_3136_, v_cls_3135_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object* v_c_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_){
_start:
{
lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v_options_3209_; lean_object* v_inheritedTraceOptions_3210_; uint8_t v_hasTrace_3211_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; 
v_options_3209_ = lean_ctor_get(v_a_3148_, 2);
v_inheritedTraceOptions_3210_ = lean_ctor_get(v_a_3148_, 13);
v_hasTrace_3211_ = lean_ctor_get_uint8(v_options_3209_, sizeof(void*)*1);
if (v_hasTrace_3211_ == 0)
{
v___y_3213_ = v_a_3139_;
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
goto v___jp_3212_;
}
else
{
lean_object* v_cls_3282_; lean_object* v___x_3283_; uint8_t v___x_3284_; 
v_cls_3282_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3283_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_3284_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3210_, v_options_3209_, v___x_3283_);
if (v___x_3284_ == 0)
{
v___y_3213_ = v_a_3139_;
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
goto v___jp_3212_;
}
else
{
lean_object* v___x_3285_; 
v___x_3285_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3286_);
lean_dec_ref(v___x_3285_);
v___x_3287_ = l_Lean_MessageData_ofExpr(v_a_3286_);
v___x_3288_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_3282_, v___x_3287_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_dec_ref(v___x_3288_);
v___y_3213_ = v_a_3139_;
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
goto v___jp_3212_;
}
else
{
lean_dec_ref(v_c_3138_);
return v___x_3288_;
}
}
else
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
lean_dec_ref(v_c_3138_);
v_a_3289_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3285_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3285_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
}
v___jp_3151_:
{
lean_object* v___x_3168_; 
v___x_3168_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_3155_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v___f_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
lean_dec_ref(v___x_3168_);
lean_inc(v___y_3157_);
v___f_3169_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3169_, 0, v___y_3157_);
lean_closure_set(v___f_3169_, 1, v___y_3153_);
lean_closure_set(v___f_3169_, 2, v___y_3152_);
v___x_3170_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3171_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3170_, v___f_3169_, v___y_3158_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v___x_3172_; 
lean_dec_ref(v___x_3171_);
v___x_3172_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3185_; 
v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3175_ = v___x_3172_;
v_isShared_3176_ = v_isSharedCheck_3185_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3172_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3185_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
uint8_t v___x_3177_; uint8_t v___x_3178_; uint8_t v___x_3179_; 
v___x_3177_ = 0;
v___x_3178_ = lean_unbox(v_a_3173_);
lean_dec(v_a_3173_);
v___x_3179_ = l_Lean_instBEqLBool_beq(v___x_3178_, v___x_3177_);
if (v___x_3179_ == 0)
{
lean_object* v___x_3180_; lean_object* v___x_3182_; 
lean_dec(v___y_3154_);
v___x_3180_ = lean_box(0);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 0, v___x_3180_);
v___x_3182_ = v___x_3175_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3180_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
else
{
lean_object* v___x_3184_; 
lean_del_object(v___x_3175_);
v___x_3184_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_3154_, v___y_3157_, v___y_3158_);
return v___x_3184_;
}
}
}
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
lean_dec(v___y_3154_);
v_a_3186_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_3172_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3172_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
if (v_isShared_3189_ == 0)
{
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
else
{
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3154_);
return v___x_3171_;
}
}
else
{
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
return v___x_3168_;
}
}
v___jp_3194_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3207_, 0, v___y_3195_);
v___x_3208_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(v___x_3207_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
return v___x_3208_;
}
v___jp_3212_:
{
lean_object* v___x_3224_; 
lean_inc_ref(v___y_3222_);
v___x_3224_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_3138_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3273_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3227_ = v___x_3224_;
v_isShared_3228_ = v_isSharedCheck_3273_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3224_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3273_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
if (lean_obj_tag(v_a_3225_) == 1)
{
lean_object* v_val_3229_; lean_object* v_p_3230_; 
lean_del_object(v___x_3227_);
v_val_3229_ = lean_ctor_get(v_a_3225_, 0);
lean_inc(v_val_3229_);
lean_dec_ref(v_a_3225_);
v_p_3230_ = lean_ctor_get(v_val_3229_, 0);
if (lean_obj_tag(v_p_3230_) == 0)
{
lean_object* v_options_3231_; uint8_t v_hasTrace_3232_; 
v_options_3231_ = lean_ctor_get(v___y_3222_, 2);
v_hasTrace_3232_ = lean_ctor_get_uint8(v_options_3231_, sizeof(void*)*1);
if (v_hasTrace_3232_ == 0)
{
v___y_3195_ = v_val_3229_;
v___y_3196_ = v___y_3213_;
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
goto v___jp_3194_;
}
else
{
lean_object* v_inheritedTraceOptions_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; uint8_t v___x_3236_; 
v_inheritedTraceOptions_3233_ = lean_ctor_get(v___y_3222_, 13);
v___x_3234_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3235_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2);
v___x_3236_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3233_, v_options_3231_, v___x_3235_);
if (v___x_3236_ == 0)
{
v___y_3195_ = v_val_3229_;
v___y_3196_ = v___y_3213_;
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
goto v___jp_3194_;
}
else
{
lean_object* v___x_3237_; 
v___x_3237_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3229_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_a_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
lean_inc(v_a_3238_);
lean_dec_ref(v___x_3237_);
v___x_3239_ = l_Lean_MessageData_ofExpr(v_a_3238_);
v___x_3240_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3234_, v___x_3239_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_dec_ref(v___x_3240_);
v___y_3195_ = v_val_3229_;
v___y_3196_ = v___y_3213_;
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
goto v___jp_3194_;
}
else
{
lean_dec(v_val_3229_);
return v___x_3240_;
}
}
else
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3248_; 
lean_dec(v_val_3229_);
v_a_3241_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3243_ = v___x_3237_;
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3237_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3246_; 
if (v_isShared_3244_ == 0)
{
v___x_3246_ = v___x_3243_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_a_3241_);
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
}
}
else
{
lean_object* v_options_3249_; uint8_t v_hasTrace_3250_; 
lean_inc_ref(v_p_3230_);
v_options_3249_ = lean_ctor_get(v___y_3222_, 2);
v_hasTrace_3250_ = lean_ctor_get_uint8(v_options_3249_, sizeof(void*)*1);
if (v_hasTrace_3250_ == 0)
{
lean_object* v_v_3251_; 
v_v_3251_ = lean_ctor_get(v_p_3230_, 1);
lean_inc_n(v_v_3251_, 2);
lean_inc(v_val_3229_);
v___y_3152_ = v_v_3251_;
v___y_3153_ = v_val_3229_;
v___y_3154_ = v_v_3251_;
v___y_3155_ = v_p_3230_;
v___y_3156_ = v_val_3229_;
v___y_3157_ = v___y_3213_;
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
goto v___jp_3151_;
}
else
{
lean_object* v_v_3252_; lean_object* v_inheritedTraceOptions_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; uint8_t v___x_3256_; 
v_v_3252_ = lean_ctor_get(v_p_3230_, 1);
lean_inc(v_v_3252_);
v_inheritedTraceOptions_3253_ = lean_ctor_get(v___y_3222_, 13);
v___x_3254_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3255_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_3256_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3253_, v_options_3249_, v___x_3255_);
if (v___x_3256_ == 0)
{
lean_inc(v_val_3229_);
lean_inc(v_v_3252_);
v___y_3152_ = v_v_3252_;
v___y_3153_ = v_val_3229_;
v___y_3154_ = v_v_3252_;
v___y_3155_ = v_p_3230_;
v___y_3156_ = v_val_3229_;
v___y_3157_ = v___y_3213_;
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
goto v___jp_3151_;
}
else
{
lean_object* v___x_3257_; 
v___x_3257_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3229_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
lean_inc(v_a_3258_);
lean_dec_ref(v___x_3257_);
v___x_3259_ = l_Lean_MessageData_ofExpr(v_a_3258_);
v___x_3260_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3254_, v___x_3259_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_dec_ref(v___x_3260_);
lean_inc(v_val_3229_);
lean_inc(v_v_3252_);
v___y_3152_ = v_v_3252_;
v___y_3153_ = v_val_3229_;
v___y_3154_ = v_v_3252_;
v___y_3155_ = v_p_3230_;
v___y_3156_ = v_val_3229_;
v___y_3157_ = v___y_3213_;
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
goto v___jp_3151_;
}
else
{
lean_dec(v_v_3252_);
lean_dec_ref(v_p_3230_);
lean_dec(v_val_3229_);
return v___x_3260_;
}
}
else
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
lean_dec(v_v_3252_);
lean_dec_ref(v_p_3230_);
lean_dec(v_val_3229_);
v_a_3261_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3257_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3257_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3269_; lean_object* v___x_3271_; 
lean_dec(v_a_3225_);
v___x_3269_ = lean_box(0);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 0, v___x_3269_);
v___x_3271_ = v___x_3227_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3269_);
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
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
v_a_3274_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3224_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3224_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___boxed(lean_object* v_c_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_c_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
lean_dec(v_a_3308_);
lean_dec_ref(v_a_3307_);
lean_dec(v_a_3306_);
lean_dec_ref(v_a_3305_);
lean_dec(v_a_3304_);
lean_dec_ref(v_a_3303_);
lean_dec(v_a_3302_);
lean_dec_ref(v_a_3301_);
lean_dec(v_a_3300_);
lean_dec(v_a_3299_);
lean_dec(v_a_3298_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_3311_, lean_object* v_as_3312_, size_t v_sz_3313_, size_t v_i_3314_, lean_object* v_b_3315_){
_start:
{
uint8_t v___x_3316_; 
v___x_3316_ = lean_usize_dec_lt(v_i_3314_, v_sz_3313_);
if (v___x_3316_ == 0)
{
return v_b_3315_;
}
else
{
lean_object* v_snd_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3358_; 
v_snd_3317_ = lean_ctor_get(v_b_3315_, 1);
v_isSharedCheck_3358_ = !lean_is_exclusive(v_b_3315_);
if (v_isSharedCheck_3358_ == 0)
{
lean_object* v_unused_3359_; 
v_unused_3359_ = lean_ctor_get(v_b_3315_, 0);
lean_dec(v_unused_3359_);
v___x_3319_ = v_b_3315_;
v_isShared_3320_ = v_isSharedCheck_3358_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_snd_3317_);
lean_dec(v_b_3315_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3358_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v_fst_3321_; lean_object* v_snd_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3357_; 
v_fst_3321_ = lean_ctor_get(v_snd_3317_, 0);
v_snd_3322_ = lean_ctor_get(v_snd_3317_, 1);
v_isSharedCheck_3357_ = !lean_is_exclusive(v_snd_3317_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3324_ = v_snd_3317_;
v_isShared_3325_ = v_isSharedCheck_3357_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_snd_3322_);
lean_inc(v_fst_3321_);
lean_dec(v_snd_3317_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3357_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v_a_3326_; lean_object* v_p_3327_; lean_object* v___x_3328_; lean_object* v_a_3330_; lean_object* v_b_3337_; lean_object* v___x_3338_; uint8_t v___x_3339_; 
v_a_3326_ = lean_array_uget(v_as_3312_, v_i_3314_);
v_p_3327_ = lean_ctor_get(v_a_3326_, 0);
v___x_3328_ = lean_box(0);
v_b_3337_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3327_, v_x_3311_);
v___x_3338_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3339_ = lean_int_dec_eq(v_b_3337_, v___x_3338_);
if (v___x_3339_ == 0)
{
lean_object* v___x_3341_; 
lean_inc(v_a_3326_);
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 1, v_a_3326_);
lean_ctor_set(v___x_3319_, 0, v_b_3337_);
v___x_3341_ = v___x_3319_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_b_3337_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v_a_3326_);
v___x_3341_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3349_; 
v_isSharedCheck_3349_ = !lean_is_exclusive(v_a_3326_);
if (v_isSharedCheck_3349_ == 0)
{
lean_object* v_unused_3350_; lean_object* v_unused_3351_; 
v_unused_3350_ = lean_ctor_get(v_a_3326_, 1);
lean_dec(v_unused_3350_);
v_unused_3351_ = lean_ctor_get(v_a_3326_, 0);
lean_dec(v_unused_3351_);
v___x_3343_ = v_a_3326_;
v_isShared_3344_ = v_isSharedCheck_3349_;
goto v_resetjp_3342_;
}
else
{
lean_dec(v_a_3326_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3349_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v_todo_3345_; lean_object* v___x_3347_; 
v_todo_3345_ = lean_array_push(v_snd_3322_, v___x_3341_);
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 1, v_todo_3345_);
lean_ctor_set(v___x_3343_, 0, v_fst_3321_);
v___x_3347_ = v___x_3343_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_fst_3321_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v_todo_3345_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
v_a_3330_ = v___x_3347_;
goto v___jp_3329_;
}
}
}
}
else
{
lean_object* v_cs_x27_3353_; lean_object* v___x_3355_; 
lean_dec(v_b_3337_);
v_cs_x27_3353_ = l_Lean_PersistentArray_push___redArg(v_fst_3321_, v_a_3326_);
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 1, v_snd_3322_);
lean_ctor_set(v___x_3319_, 0, v_cs_x27_3353_);
v___x_3355_ = v___x_3319_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_cs_x27_3353_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v_snd_3322_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
v_a_3330_ = v___x_3355_;
goto v___jp_3329_;
}
}
v___jp_3329_:
{
lean_object* v___x_3332_; 
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 1, v_a_3330_);
lean_ctor_set(v___x_3324_, 0, v___x_3328_);
v___x_3332_ = v___x_3324_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3328_);
lean_ctor_set(v_reuseFailAlloc_3336_, 1, v_a_3330_);
v___x_3332_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
size_t v___x_3333_; size_t v___x_3334_; 
v___x_3333_ = ((size_t)1ULL);
v___x_3334_ = lean_usize_add(v_i_3314_, v___x_3333_);
v_i_3314_ = v___x_3334_;
v_b_3315_ = v___x_3332_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_3360_, lean_object* v_as_3361_, lean_object* v_sz_3362_, lean_object* v_i_3363_, lean_object* v_b_3364_){
_start:
{
size_t v_sz_boxed_3365_; size_t v_i_boxed_3366_; lean_object* v_res_3367_; 
v_sz_boxed_3365_ = lean_unbox_usize(v_sz_3362_);
lean_dec(v_sz_3362_);
v_i_boxed_3366_ = lean_unbox_usize(v_i_3363_);
lean_dec(v_i_3363_);
v_res_3367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3360_, v_as_3361_, v_sz_boxed_3365_, v_i_boxed_3366_, v_b_3364_);
lean_dec_ref(v_as_3361_);
lean_dec(v_x_3360_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(lean_object* v_x_3368_, lean_object* v_as_3369_, size_t v_sz_3370_, size_t v_i_3371_, lean_object* v_b_3372_){
_start:
{
uint8_t v___x_3373_; 
v___x_3373_ = lean_usize_dec_lt(v_i_3371_, v_sz_3370_);
if (v___x_3373_ == 0)
{
return v_b_3372_;
}
else
{
lean_object* v_snd_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3415_; 
v_snd_3374_ = lean_ctor_get(v_b_3372_, 1);
v_isSharedCheck_3415_ = !lean_is_exclusive(v_b_3372_);
if (v_isSharedCheck_3415_ == 0)
{
lean_object* v_unused_3416_; 
v_unused_3416_ = lean_ctor_get(v_b_3372_, 0);
lean_dec(v_unused_3416_);
v___x_3376_ = v_b_3372_;
v_isShared_3377_ = v_isSharedCheck_3415_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_snd_3374_);
lean_dec(v_b_3372_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3415_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v_fst_3378_; lean_object* v_snd_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3414_; 
v_fst_3378_ = lean_ctor_get(v_snd_3374_, 0);
v_snd_3379_ = lean_ctor_get(v_snd_3374_, 1);
v_isSharedCheck_3414_ = !lean_is_exclusive(v_snd_3374_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3381_ = v_snd_3374_;
v_isShared_3382_ = v_isSharedCheck_3414_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_snd_3379_);
lean_inc(v_fst_3378_);
lean_dec(v_snd_3374_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3414_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v_a_3383_; lean_object* v_p_3384_; lean_object* v___x_3385_; lean_object* v_a_3387_; lean_object* v_b_3394_; lean_object* v___x_3395_; uint8_t v___x_3396_; 
v_a_3383_ = lean_array_uget(v_as_3369_, v_i_3371_);
v_p_3384_ = lean_ctor_get(v_a_3383_, 0);
v___x_3385_ = lean_box(0);
v_b_3394_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3384_, v_x_3368_);
v___x_3395_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3396_ = lean_int_dec_eq(v_b_3394_, v___x_3395_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3398_; 
lean_inc(v_a_3383_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 1, v_a_3383_);
lean_ctor_set(v___x_3376_, 0, v_b_3394_);
v___x_3398_ = v___x_3376_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_b_3394_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v_a_3383_);
v___x_3398_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3406_; 
v_isSharedCheck_3406_ = !lean_is_exclusive(v_a_3383_);
if (v_isSharedCheck_3406_ == 0)
{
lean_object* v_unused_3407_; lean_object* v_unused_3408_; 
v_unused_3407_ = lean_ctor_get(v_a_3383_, 1);
lean_dec(v_unused_3407_);
v_unused_3408_ = lean_ctor_get(v_a_3383_, 0);
lean_dec(v_unused_3408_);
v___x_3400_ = v_a_3383_;
v_isShared_3401_ = v_isSharedCheck_3406_;
goto v_resetjp_3399_;
}
else
{
lean_dec(v_a_3383_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3406_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v_todo_3402_; lean_object* v___x_3404_; 
v_todo_3402_ = lean_array_push(v_snd_3379_, v___x_3398_);
if (v_isShared_3401_ == 0)
{
lean_ctor_set(v___x_3400_, 1, v_todo_3402_);
lean_ctor_set(v___x_3400_, 0, v_fst_3378_);
v___x_3404_ = v___x_3400_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_fst_3378_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v_todo_3402_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
v_a_3387_ = v___x_3404_;
goto v___jp_3386_;
}
}
}
}
else
{
lean_object* v_cs_x27_3410_; lean_object* v___x_3412_; 
lean_dec(v_b_3394_);
v_cs_x27_3410_ = l_Lean_PersistentArray_push___redArg(v_fst_3378_, v_a_3383_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 1, v_snd_3379_);
lean_ctor_set(v___x_3376_, 0, v_cs_x27_3410_);
v___x_3412_ = v___x_3376_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_cs_x27_3410_);
lean_ctor_set(v_reuseFailAlloc_3413_, 1, v_snd_3379_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
v_a_3387_ = v___x_3412_;
goto v___jp_3386_;
}
}
v___jp_3386_:
{
lean_object* v___x_3389_; 
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 1, v_a_3387_);
lean_ctor_set(v___x_3381_, 0, v___x_3385_);
v___x_3389_ = v___x_3381_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3385_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v_a_3387_);
v___x_3389_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
size_t v___x_3390_; size_t v___x_3391_; lean_object* v___x_3392_; 
v___x_3390_ = ((size_t)1ULL);
v___x_3391_ = lean_usize_add(v_i_3371_, v___x_3390_);
v___x_3392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3368_, v_as_3369_, v_sz_3370_, v___x_3391_, v___x_3389_);
return v___x_3392_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_3417_, lean_object* v_as_3418_, lean_object* v_sz_3419_, lean_object* v_i_3420_, lean_object* v_b_3421_){
_start:
{
size_t v_sz_boxed_3422_; size_t v_i_boxed_3423_; lean_object* v_res_3424_; 
v_sz_boxed_3422_ = lean_unbox_usize(v_sz_3419_);
lean_dec(v_sz_3419_);
v_i_boxed_3423_ = lean_unbox_usize(v_i_3420_);
lean_dec(v_i_3420_);
v_res_3424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3417_, v_as_3418_, v_sz_boxed_3422_, v_i_boxed_3423_, v_b_3421_);
lean_dec_ref(v_as_3418_);
lean_dec(v_x_3417_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_3425_, lean_object* v_as_3426_, size_t v_sz_3427_, size_t v_i_3428_, lean_object* v_b_3429_){
_start:
{
uint8_t v___x_3430_; 
v___x_3430_ = lean_usize_dec_lt(v_i_3428_, v_sz_3427_);
if (v___x_3430_ == 0)
{
return v_b_3429_;
}
else
{
lean_object* v_snd_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3472_; 
v_snd_3431_ = lean_ctor_get(v_b_3429_, 1);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_b_3429_);
if (v_isSharedCheck_3472_ == 0)
{
lean_object* v_unused_3473_; 
v_unused_3473_ = lean_ctor_get(v_b_3429_, 0);
lean_dec(v_unused_3473_);
v___x_3433_ = v_b_3429_;
v_isShared_3434_ = v_isSharedCheck_3472_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_snd_3431_);
lean_dec(v_b_3429_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3472_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v_fst_3435_; lean_object* v_snd_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3471_; 
v_fst_3435_ = lean_ctor_get(v_snd_3431_, 0);
v_snd_3436_ = lean_ctor_get(v_snd_3431_, 1);
v_isSharedCheck_3471_ = !lean_is_exclusive(v_snd_3431_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3438_ = v_snd_3431_;
v_isShared_3439_ = v_isSharedCheck_3471_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_snd_3436_);
lean_inc(v_fst_3435_);
lean_dec(v_snd_3431_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3471_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v_a_3440_; lean_object* v_p_3441_; lean_object* v___x_3442_; lean_object* v_a_3444_; lean_object* v_b_3451_; lean_object* v___x_3452_; uint8_t v___x_3453_; 
v_a_3440_ = lean_array_uget(v_as_3426_, v_i_3428_);
v_p_3441_ = lean_ctor_get(v_a_3440_, 0);
v___x_3442_ = lean_box(0);
v_b_3451_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3441_, v_x_3425_);
v___x_3452_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3453_ = lean_int_dec_eq(v_b_3451_, v___x_3452_);
if (v___x_3453_ == 0)
{
lean_object* v___x_3455_; 
lean_inc(v_a_3440_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 1, v_a_3440_);
lean_ctor_set(v___x_3433_, 0, v_b_3451_);
v___x_3455_ = v___x_3433_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_b_3451_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v_a_3440_);
v___x_3455_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3463_; 
v_isSharedCheck_3463_ = !lean_is_exclusive(v_a_3440_);
if (v_isSharedCheck_3463_ == 0)
{
lean_object* v_unused_3464_; lean_object* v_unused_3465_; 
v_unused_3464_ = lean_ctor_get(v_a_3440_, 1);
lean_dec(v_unused_3464_);
v_unused_3465_ = lean_ctor_get(v_a_3440_, 0);
lean_dec(v_unused_3465_);
v___x_3457_ = v_a_3440_;
v_isShared_3458_ = v_isSharedCheck_3463_;
goto v_resetjp_3456_;
}
else
{
lean_dec(v_a_3440_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3463_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v_todo_3459_; lean_object* v___x_3461_; 
v_todo_3459_ = lean_array_push(v_snd_3436_, v___x_3455_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 1, v_todo_3459_);
lean_ctor_set(v___x_3457_, 0, v_fst_3435_);
v___x_3461_ = v___x_3457_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_fst_3435_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v_todo_3459_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
v_a_3444_ = v___x_3461_;
goto v___jp_3443_;
}
}
}
}
else
{
lean_object* v_cs_x27_3467_; lean_object* v___x_3469_; 
lean_dec(v_b_3451_);
v_cs_x27_3467_ = l_Lean_PersistentArray_push___redArg(v_fst_3435_, v_a_3440_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 1, v_snd_3436_);
lean_ctor_set(v___x_3433_, 0, v_cs_x27_3467_);
v___x_3469_ = v___x_3433_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_cs_x27_3467_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_snd_3436_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
v_a_3444_ = v___x_3469_;
goto v___jp_3443_;
}
}
v___jp_3443_:
{
lean_object* v___x_3446_; 
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v_a_3444_);
lean_ctor_set(v___x_3438_, 0, v___x_3442_);
v___x_3446_ = v___x_3438_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v_a_3444_);
v___x_3446_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
size_t v___x_3447_; size_t v___x_3448_; 
v___x_3447_ = ((size_t)1ULL);
v___x_3448_ = lean_usize_add(v_i_3428_, v___x_3447_);
v_i_3428_ = v___x_3448_;
v_b_3429_ = v___x_3446_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3474_, lean_object* v_as_3475_, lean_object* v_sz_3476_, lean_object* v_i_3477_, lean_object* v_b_3478_){
_start:
{
size_t v_sz_boxed_3479_; size_t v_i_boxed_3480_; lean_object* v_res_3481_; 
v_sz_boxed_3479_ = lean_unbox_usize(v_sz_3476_);
lean_dec(v_sz_3476_);
v_i_boxed_3480_ = lean_unbox_usize(v_i_3477_);
lean_dec(v_i_3477_);
v_res_3481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3474_, v_as_3475_, v_sz_boxed_3479_, v_i_boxed_3480_, v_b_3478_);
lean_dec_ref(v_as_3475_);
lean_dec(v_x_3474_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_3482_, lean_object* v_as_3483_, size_t v_sz_3484_, size_t v_i_3485_, lean_object* v_b_3486_){
_start:
{
uint8_t v___x_3487_; 
v___x_3487_ = lean_usize_dec_lt(v_i_3485_, v_sz_3484_);
if (v___x_3487_ == 0)
{
return v_b_3486_;
}
else
{
lean_object* v_snd_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3529_; 
v_snd_3488_ = lean_ctor_get(v_b_3486_, 1);
v_isSharedCheck_3529_ = !lean_is_exclusive(v_b_3486_);
if (v_isSharedCheck_3529_ == 0)
{
lean_object* v_unused_3530_; 
v_unused_3530_ = lean_ctor_get(v_b_3486_, 0);
lean_dec(v_unused_3530_);
v___x_3490_ = v_b_3486_;
v_isShared_3491_ = v_isSharedCheck_3529_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_snd_3488_);
lean_dec(v_b_3486_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3529_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v_fst_3492_; lean_object* v_snd_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3528_; 
v_fst_3492_ = lean_ctor_get(v_snd_3488_, 0);
v_snd_3493_ = lean_ctor_get(v_snd_3488_, 1);
v_isSharedCheck_3528_ = !lean_is_exclusive(v_snd_3488_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3495_ = v_snd_3488_;
v_isShared_3496_ = v_isSharedCheck_3528_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_snd_3493_);
lean_inc(v_fst_3492_);
lean_dec(v_snd_3488_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3528_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v_a_3497_; lean_object* v_p_3498_; lean_object* v___x_3499_; lean_object* v_a_3501_; lean_object* v_b_3508_; lean_object* v___x_3509_; uint8_t v___x_3510_; 
v_a_3497_ = lean_array_uget(v_as_3483_, v_i_3485_);
v_p_3498_ = lean_ctor_get(v_a_3497_, 0);
v___x_3499_ = lean_box(0);
v_b_3508_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3498_, v_x_3482_);
v___x_3509_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3510_ = lean_int_dec_eq(v_b_3508_, v___x_3509_);
if (v___x_3510_ == 0)
{
lean_object* v___x_3512_; 
lean_inc(v_a_3497_);
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 1, v_a_3497_);
lean_ctor_set(v___x_3490_, 0, v_b_3508_);
v___x_3512_ = v___x_3490_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_b_3508_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v_a_3497_);
v___x_3512_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3520_; 
v_isSharedCheck_3520_ = !lean_is_exclusive(v_a_3497_);
if (v_isSharedCheck_3520_ == 0)
{
lean_object* v_unused_3521_; lean_object* v_unused_3522_; 
v_unused_3521_ = lean_ctor_get(v_a_3497_, 1);
lean_dec(v_unused_3521_);
v_unused_3522_ = lean_ctor_get(v_a_3497_, 0);
lean_dec(v_unused_3522_);
v___x_3514_ = v_a_3497_;
v_isShared_3515_ = v_isSharedCheck_3520_;
goto v_resetjp_3513_;
}
else
{
lean_dec(v_a_3497_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3520_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v_todo_3516_; lean_object* v___x_3518_; 
v_todo_3516_ = lean_array_push(v_snd_3493_, v___x_3512_);
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 1, v_todo_3516_);
lean_ctor_set(v___x_3514_, 0, v_fst_3492_);
v___x_3518_ = v___x_3514_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_fst_3492_);
lean_ctor_set(v_reuseFailAlloc_3519_, 1, v_todo_3516_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
v_a_3501_ = v___x_3518_;
goto v___jp_3500_;
}
}
}
}
else
{
lean_object* v_cs_x27_3524_; lean_object* v___x_3526_; 
lean_dec(v_b_3508_);
v_cs_x27_3524_ = l_Lean_PersistentArray_push___redArg(v_fst_3492_, v_a_3497_);
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 1, v_snd_3493_);
lean_ctor_set(v___x_3490_, 0, v_cs_x27_3524_);
v___x_3526_ = v___x_3490_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_cs_x27_3524_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v_snd_3493_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
v_a_3501_ = v___x_3526_;
goto v___jp_3500_;
}
}
v___jp_3500_:
{
lean_object* v___x_3503_; 
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 1, v_a_3501_);
lean_ctor_set(v___x_3495_, 0, v___x_3499_);
v___x_3503_ = v___x_3495_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3499_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v_a_3501_);
v___x_3503_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
size_t v___x_3504_; size_t v___x_3505_; lean_object* v___x_3506_; 
v___x_3504_ = ((size_t)1ULL);
v___x_3505_ = lean_usize_add(v_i_3485_, v___x_3504_);
v___x_3506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3482_, v_as_3483_, v_sz_3484_, v___x_3505_, v___x_3503_);
return v___x_3506_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_3531_, lean_object* v_as_3532_, lean_object* v_sz_3533_, lean_object* v_i_3534_, lean_object* v_b_3535_){
_start:
{
size_t v_sz_boxed_3536_; size_t v_i_boxed_3537_; lean_object* v_res_3538_; 
v_sz_boxed_3536_ = lean_unbox_usize(v_sz_3533_);
lean_dec(v_sz_3533_);
v_i_boxed_3537_ = lean_unbox_usize(v_i_3534_);
lean_dec(v_i_3534_);
v_res_3538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3531_, v_as_3532_, v_sz_boxed_3536_, v_i_boxed_3537_, v_b_3535_);
lean_dec_ref(v_as_3532_);
lean_dec(v_x_3531_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(lean_object* v_init_3539_, lean_object* v_x_3540_, lean_object* v_n_3541_, lean_object* v_b_3542_){
_start:
{
if (lean_obj_tag(v_n_3541_) == 0)
{
lean_object* v_cs_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; size_t v_sz_3546_; size_t v___x_3547_; lean_object* v___x_3548_; lean_object* v_fst_3549_; 
v_cs_3543_ = lean_ctor_get(v_n_3541_, 0);
v___x_3544_ = lean_box(0);
v___x_3545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
lean_ctor_set(v___x_3545_, 1, v_b_3542_);
v_sz_3546_ = lean_array_size(v_cs_3543_);
v___x_3547_ = ((size_t)0ULL);
v___x_3548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3539_, v_x_3540_, v_cs_3543_, v_sz_3546_, v___x_3547_, v___x_3545_);
v_fst_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_fst_3549_);
if (lean_obj_tag(v_fst_3549_) == 0)
{
lean_object* v_snd_3550_; lean_object* v___x_3551_; 
v_snd_3550_ = lean_ctor_get(v___x_3548_, 1);
lean_inc(v_snd_3550_);
lean_dec_ref(v___x_3548_);
v___x_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3551_, 0, v_snd_3550_);
return v___x_3551_;
}
else
{
lean_object* v_val_3552_; 
lean_dec_ref(v___x_3548_);
v_val_3552_ = lean_ctor_get(v_fst_3549_, 0);
lean_inc(v_val_3552_);
lean_dec_ref(v_fst_3549_);
return v_val_3552_;
}
}
else
{
lean_object* v_vs_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; size_t v_sz_3556_; size_t v___x_3557_; lean_object* v___x_3558_; lean_object* v_fst_3559_; 
v_vs_3553_ = lean_ctor_get(v_n_3541_, 0);
v___x_3554_ = lean_box(0);
v___x_3555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3554_);
lean_ctor_set(v___x_3555_, 1, v_b_3542_);
v_sz_3556_ = lean_array_size(v_vs_3553_);
v___x_3557_ = ((size_t)0ULL);
v___x_3558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3540_, v_vs_3553_, v_sz_3556_, v___x_3557_, v___x_3555_);
v_fst_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_fst_3559_);
if (lean_obj_tag(v_fst_3559_) == 0)
{
lean_object* v_snd_3560_; lean_object* v___x_3561_; 
v_snd_3560_ = lean_ctor_get(v___x_3558_, 1);
lean_inc(v_snd_3560_);
lean_dec_ref(v___x_3558_);
v___x_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3561_, 0, v_snd_3560_);
return v___x_3561_;
}
else
{
lean_object* v_val_3562_; 
lean_dec_ref(v___x_3558_);
v_val_3562_ = lean_ctor_get(v_fst_3559_, 0);
lean_inc(v_val_3562_);
lean_dec_ref(v_fst_3559_);
return v_val_3562_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3563_, lean_object* v_x_3564_, lean_object* v_as_3565_, size_t v_sz_3566_, size_t v_i_3567_, lean_object* v_b_3568_){
_start:
{
uint8_t v___x_3569_; 
v___x_3569_ = lean_usize_dec_lt(v_i_3567_, v_sz_3566_);
if (v___x_3569_ == 0)
{
return v_b_3568_;
}
else
{
lean_object* v_snd_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3588_; 
v_snd_3570_ = lean_ctor_get(v_b_3568_, 1);
v_isSharedCheck_3588_ = !lean_is_exclusive(v_b_3568_);
if (v_isSharedCheck_3588_ == 0)
{
lean_object* v_unused_3589_; 
v_unused_3589_ = lean_ctor_get(v_b_3568_, 0);
lean_dec(v_unused_3589_);
v___x_3572_ = v_b_3568_;
v_isShared_3573_ = v_isSharedCheck_3588_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_snd_3570_);
lean_dec(v_b_3568_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3588_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v_a_3574_; lean_object* v___x_3575_; 
v_a_3574_ = lean_array_uget_borrowed(v_as_3565_, v_i_3567_);
lean_inc(v_snd_3570_);
v___x_3575_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3563_, v_x_3564_, v_a_3574_, v_snd_3570_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v___x_3576_; lean_object* v___x_3578_; 
v___x_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3575_);
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 0, v___x_3576_);
v___x_3578_ = v___x_3572_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3576_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_snd_3570_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3581_; lean_object* v___x_3583_; 
lean_dec(v_snd_3570_);
v_a_3580_ = lean_ctor_get(v___x_3575_, 0);
lean_inc(v_a_3580_);
lean_dec_ref(v___x_3575_);
v___x_3581_ = lean_box(0);
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 1, v_a_3580_);
lean_ctor_set(v___x_3572_, 0, v___x_3581_);
v___x_3583_ = v___x_3572_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3581_);
lean_ctor_set(v_reuseFailAlloc_3587_, 1, v_a_3580_);
v___x_3583_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
size_t v___x_3584_; size_t v___x_3585_; 
v___x_3584_ = ((size_t)1ULL);
v___x_3585_ = lean_usize_add(v_i_3567_, v___x_3584_);
v_i_3567_ = v___x_3585_;
v_b_3568_ = v___x_3583_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3590_, lean_object* v_x_3591_, lean_object* v_as_3592_, lean_object* v_sz_3593_, lean_object* v_i_3594_, lean_object* v_b_3595_){
_start:
{
size_t v_sz_boxed_3596_; size_t v_i_boxed_3597_; lean_object* v_res_3598_; 
v_sz_boxed_3596_ = lean_unbox_usize(v_sz_3593_);
lean_dec(v_sz_3593_);
v_i_boxed_3597_ = lean_unbox_usize(v_i_3594_);
lean_dec(v_i_3594_);
v_res_3598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3590_, v_x_3591_, v_as_3592_, v_sz_boxed_3596_, v_i_boxed_3597_, v_b_3595_);
lean_dec_ref(v_as_3592_);
lean_dec(v_x_3591_);
lean_dec_ref(v_init_3590_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3599_, lean_object* v_x_3600_, lean_object* v_n_3601_, lean_object* v_b_3602_){
_start:
{
lean_object* v_res_3603_; 
v_res_3603_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3599_, v_x_3600_, v_n_3601_, v_b_3602_);
lean_dec_ref(v_n_3601_);
lean_dec(v_x_3600_);
lean_dec_ref(v_init_3599_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object* v_x_3604_, lean_object* v_t_3605_, lean_object* v_init_3606_){
_start:
{
lean_object* v_root_3607_; lean_object* v_tail_3608_; lean_object* v___x_3609_; 
v_root_3607_ = lean_ctor_get(v_t_3605_, 0);
v_tail_3608_ = lean_ctor_get(v_t_3605_, 1);
lean_inc_ref(v_init_3606_);
v___x_3609_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3606_, v_x_3604_, v_root_3607_, v_init_3606_);
lean_dec_ref(v_init_3606_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref(v___x_3609_);
return v_a_3610_;
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; size_t v_sz_3614_; size_t v___x_3615_; lean_object* v___x_3616_; lean_object* v_fst_3617_; 
v_a_3611_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3611_);
lean_dec_ref(v___x_3609_);
v___x_3612_ = lean_box(0);
v___x_3613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3612_);
lean_ctor_set(v___x_3613_, 1, v_a_3611_);
v_sz_3614_ = lean_array_size(v_tail_3608_);
v___x_3615_ = ((size_t)0ULL);
v___x_3616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3604_, v_tail_3608_, v_sz_3614_, v___x_3615_, v___x_3613_);
v_fst_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_fst_3617_);
if (lean_obj_tag(v_fst_3617_) == 0)
{
lean_object* v_snd_3618_; 
v_snd_3618_ = lean_ctor_get(v___x_3616_, 1);
lean_inc(v_snd_3618_);
lean_dec_ref(v___x_3616_);
return v_snd_3618_;
}
else
{
lean_object* v_val_3619_; 
lean_dec_ref(v___x_3616_);
v_val_3619_ = lean_ctor_get(v_fst_3617_, 0);
lean_inc(v_val_3619_);
lean_dec_ref(v_fst_3617_);
return v_val_3619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object* v_x_3620_, lean_object* v_t_3621_, lean_object* v_init_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3620_, v_t_3621_, v_init_3622_);
lean_dec_ref(v_t_3621_);
lean_dec(v_x_3620_);
return v_res_3623_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3624_ = lean_unsigned_to_nat(32u);
v___x_3625_ = lean_mk_empty_array_with_capacity(v___x_3624_);
v___x_3626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3625_);
return v___x_3626_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1(void){
_start:
{
size_t v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v_cs_x27_3632_; 
v___x_3627_ = ((size_t)5ULL);
v___x_3628_ = lean_unsigned_to_nat(0u);
v___x_3629_ = lean_unsigned_to_nat(32u);
v___x_3630_ = lean_mk_empty_array_with_capacity(v___x_3629_);
v___x_3631_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0);
v_cs_x27_3632_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_3632_, 0, v___x_3631_);
lean_ctor_set(v_cs_x27_3632_, 1, v___x_3630_);
lean_ctor_set(v_cs_x27_3632_, 2, v___x_3628_);
lean_ctor_set(v_cs_x27_3632_, 3, v___x_3628_);
lean_ctor_set_usize(v_cs_x27_3632_, 4, v___x_3627_);
return v_cs_x27_3632_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_3635_; lean_object* v_cs_x27_3636_; lean_object* v___x_3637_; 
v_todo_3635_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2));
v_cs_x27_3636_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1);
v___x_3637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3637_, 0, v_cs_x27_3636_);
lean_ctor_set(v___x_3637_, 1, v_todo_3635_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object* v_x_3638_, lean_object* v_cs_3639_){
_start:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v_fst_3642_; lean_object* v_snd_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3650_; 
v___x_3640_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3);
v___x_3641_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3638_, v_cs_3639_, v___x_3640_);
v_fst_3642_ = lean_ctor_get(v___x_3641_, 0);
v_snd_3643_ = lean_ctor_get(v___x_3641_, 1);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3645_ = v___x_3641_;
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_snd_3643_);
lean_inc(v_fst_3642_);
lean_dec(v___x_3641_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3648_; 
if (v_isShared_3646_ == 0)
{
v___x_3648_ = v___x_3645_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_fst_3642_);
lean_ctor_set(v_reuseFailAlloc_3649_, 1, v_snd_3643_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object* v_x_3651_, lean_object* v_cs_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3651_, v_cs_3652_);
lean_dec_ref(v_cs_3652_);
lean_dec(v_x_3651_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object* v_x_3654_, lean_object* v_cs_3655_){
_start:
{
lean_object* v___x_3656_; 
v___x_3656_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3654_, v_cs_3655_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object* v_x_3657_, lean_object* v_cs_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(v_x_3657_, v_cs_3658_);
lean_dec_ref(v_cs_3658_);
lean_dec(v_x_3657_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(lean_object* v_a_3660_, lean_object* v_y_3661_, lean_object* v_fst_3662_, lean_object* v_s_3663_){
_start:
{
lean_object* v_structs_3664_; lean_object* v_typeIdOf_3665_; lean_object* v_exprToStructId_3666_; lean_object* v_exprToStructIdEntries_3667_; lean_object* v_forbiddenNatModules_3668_; lean_object* v_natStructs_3669_; lean_object* v_natTypeIdOf_3670_; lean_object* v_exprToNatStructId_3671_; lean_object* v___x_3672_; uint8_t v___x_3673_; 
v_structs_3664_ = lean_ctor_get(v_s_3663_, 0);
v_typeIdOf_3665_ = lean_ctor_get(v_s_3663_, 1);
v_exprToStructId_3666_ = lean_ctor_get(v_s_3663_, 2);
v_exprToStructIdEntries_3667_ = lean_ctor_get(v_s_3663_, 3);
v_forbiddenNatModules_3668_ = lean_ctor_get(v_s_3663_, 4);
v_natStructs_3669_ = lean_ctor_get(v_s_3663_, 5);
v_natTypeIdOf_3670_ = lean_ctor_get(v_s_3663_, 6);
v_exprToNatStructId_3671_ = lean_ctor_get(v_s_3663_, 7);
v___x_3672_ = lean_array_get_size(v_structs_3664_);
v___x_3673_ = lean_nat_dec_lt(v_a_3660_, v___x_3672_);
if (v___x_3673_ == 0)
{
lean_dec_ref(v_fst_3662_);
return v_s_3663_;
}
else
{
lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3735_; 
lean_inc_ref(v_exprToNatStructId_3671_);
lean_inc_ref(v_natTypeIdOf_3670_);
lean_inc_ref(v_natStructs_3669_);
lean_inc_ref(v_forbiddenNatModules_3668_);
lean_inc_ref(v_exprToStructIdEntries_3667_);
lean_inc_ref(v_exprToStructId_3666_);
lean_inc_ref(v_typeIdOf_3665_);
lean_inc_ref(v_structs_3664_);
v_isSharedCheck_3735_ = !lean_is_exclusive(v_s_3663_);
if (v_isSharedCheck_3735_ == 0)
{
lean_object* v_unused_3736_; lean_object* v_unused_3737_; lean_object* v_unused_3738_; lean_object* v_unused_3739_; lean_object* v_unused_3740_; lean_object* v_unused_3741_; lean_object* v_unused_3742_; lean_object* v_unused_3743_; 
v_unused_3736_ = lean_ctor_get(v_s_3663_, 7);
lean_dec(v_unused_3736_);
v_unused_3737_ = lean_ctor_get(v_s_3663_, 6);
lean_dec(v_unused_3737_);
v_unused_3738_ = lean_ctor_get(v_s_3663_, 5);
lean_dec(v_unused_3738_);
v_unused_3739_ = lean_ctor_get(v_s_3663_, 4);
lean_dec(v_unused_3739_);
v_unused_3740_ = lean_ctor_get(v_s_3663_, 3);
lean_dec(v_unused_3740_);
v_unused_3741_ = lean_ctor_get(v_s_3663_, 2);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v_s_3663_, 1);
lean_dec(v_unused_3742_);
v_unused_3743_ = lean_ctor_get(v_s_3663_, 0);
lean_dec(v_unused_3743_);
v___x_3675_ = v_s_3663_;
v_isShared_3676_ = v_isSharedCheck_3735_;
goto v_resetjp_3674_;
}
else
{
lean_dec(v_s_3663_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3735_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v_v_3677_; lean_object* v_id_3678_; lean_object* v_ringId_x3f_3679_; lean_object* v_type_3680_; lean_object* v_u_3681_; lean_object* v_intModuleInst_3682_; lean_object* v_leInst_x3f_3683_; lean_object* v_ltInst_x3f_3684_; lean_object* v_lawfulOrderLTInst_x3f_3685_; lean_object* v_isPreorderInst_x3f_3686_; lean_object* v_orderedAddInst_x3f_3687_; lean_object* v_isLinearInst_x3f_3688_; lean_object* v_noNatDivInst_x3f_3689_; lean_object* v_ringInst_x3f_3690_; lean_object* v_commRingInst_x3f_3691_; lean_object* v_orderedRingInst_x3f_3692_; lean_object* v_fieldInst_x3f_3693_; lean_object* v_charInst_x3f_3694_; lean_object* v_zero_3695_; lean_object* v_ofNatZero_3696_; lean_object* v_one_x3f_3697_; lean_object* v_leFn_x3f_3698_; lean_object* v_ltFn_x3f_3699_; lean_object* v_addFn_3700_; lean_object* v_zsmulFn_3701_; lean_object* v_nsmulFn_3702_; lean_object* v_zsmulFn_x3f_3703_; lean_object* v_nsmulFn_x3f_3704_; lean_object* v_homomulFn_x3f_3705_; lean_object* v_subFn_3706_; lean_object* v_negFn_3707_; lean_object* v_vars_3708_; lean_object* v_varMap_3709_; lean_object* v_lowers_3710_; lean_object* v_uppers_3711_; lean_object* v_diseqs_3712_; lean_object* v_assignment_3713_; uint8_t v_caseSplits_3714_; lean_object* v_conflict_x3f_3715_; lean_object* v_diseqSplits_3716_; lean_object* v_elimEqs_3717_; lean_object* v_elimStack_3718_; lean_object* v_occurs_3719_; lean_object* v_ignored_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3734_; 
v_v_3677_ = lean_array_fget(v_structs_3664_, v_a_3660_);
v_id_3678_ = lean_ctor_get(v_v_3677_, 0);
v_ringId_x3f_3679_ = lean_ctor_get(v_v_3677_, 1);
v_type_3680_ = lean_ctor_get(v_v_3677_, 2);
v_u_3681_ = lean_ctor_get(v_v_3677_, 3);
v_intModuleInst_3682_ = lean_ctor_get(v_v_3677_, 4);
v_leInst_x3f_3683_ = lean_ctor_get(v_v_3677_, 5);
v_ltInst_x3f_3684_ = lean_ctor_get(v_v_3677_, 6);
v_lawfulOrderLTInst_x3f_3685_ = lean_ctor_get(v_v_3677_, 7);
v_isPreorderInst_x3f_3686_ = lean_ctor_get(v_v_3677_, 8);
v_orderedAddInst_x3f_3687_ = lean_ctor_get(v_v_3677_, 9);
v_isLinearInst_x3f_3688_ = lean_ctor_get(v_v_3677_, 10);
v_noNatDivInst_x3f_3689_ = lean_ctor_get(v_v_3677_, 11);
v_ringInst_x3f_3690_ = lean_ctor_get(v_v_3677_, 12);
v_commRingInst_x3f_3691_ = lean_ctor_get(v_v_3677_, 13);
v_orderedRingInst_x3f_3692_ = lean_ctor_get(v_v_3677_, 14);
v_fieldInst_x3f_3693_ = lean_ctor_get(v_v_3677_, 15);
v_charInst_x3f_3694_ = lean_ctor_get(v_v_3677_, 16);
v_zero_3695_ = lean_ctor_get(v_v_3677_, 17);
v_ofNatZero_3696_ = lean_ctor_get(v_v_3677_, 18);
v_one_x3f_3697_ = lean_ctor_get(v_v_3677_, 19);
v_leFn_x3f_3698_ = lean_ctor_get(v_v_3677_, 20);
v_ltFn_x3f_3699_ = lean_ctor_get(v_v_3677_, 21);
v_addFn_3700_ = lean_ctor_get(v_v_3677_, 22);
v_zsmulFn_3701_ = lean_ctor_get(v_v_3677_, 23);
v_nsmulFn_3702_ = lean_ctor_get(v_v_3677_, 24);
v_zsmulFn_x3f_3703_ = lean_ctor_get(v_v_3677_, 25);
v_nsmulFn_x3f_3704_ = lean_ctor_get(v_v_3677_, 26);
v_homomulFn_x3f_3705_ = lean_ctor_get(v_v_3677_, 27);
v_subFn_3706_ = lean_ctor_get(v_v_3677_, 28);
v_negFn_3707_ = lean_ctor_get(v_v_3677_, 29);
v_vars_3708_ = lean_ctor_get(v_v_3677_, 30);
v_varMap_3709_ = lean_ctor_get(v_v_3677_, 31);
v_lowers_3710_ = lean_ctor_get(v_v_3677_, 32);
v_uppers_3711_ = lean_ctor_get(v_v_3677_, 33);
v_diseqs_3712_ = lean_ctor_get(v_v_3677_, 34);
v_assignment_3713_ = lean_ctor_get(v_v_3677_, 35);
v_caseSplits_3714_ = lean_ctor_get_uint8(v_v_3677_, sizeof(void*)*42);
v_conflict_x3f_3715_ = lean_ctor_get(v_v_3677_, 36);
v_diseqSplits_3716_ = lean_ctor_get(v_v_3677_, 37);
v_elimEqs_3717_ = lean_ctor_get(v_v_3677_, 38);
v_elimStack_3718_ = lean_ctor_get(v_v_3677_, 39);
v_occurs_3719_ = lean_ctor_get(v_v_3677_, 40);
v_ignored_3720_ = lean_ctor_get(v_v_3677_, 41);
v_isSharedCheck_3734_ = !lean_is_exclusive(v_v_3677_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3722_ = v_v_3677_;
v_isShared_3723_ = v_isSharedCheck_3734_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_ignored_3720_);
lean_inc(v_occurs_3719_);
lean_inc(v_elimStack_3718_);
lean_inc(v_elimEqs_3717_);
lean_inc(v_diseqSplits_3716_);
lean_inc(v_conflict_x3f_3715_);
lean_inc(v_assignment_3713_);
lean_inc(v_diseqs_3712_);
lean_inc(v_uppers_3711_);
lean_inc(v_lowers_3710_);
lean_inc(v_varMap_3709_);
lean_inc(v_vars_3708_);
lean_inc(v_negFn_3707_);
lean_inc(v_subFn_3706_);
lean_inc(v_homomulFn_x3f_3705_);
lean_inc(v_nsmulFn_x3f_3704_);
lean_inc(v_zsmulFn_x3f_3703_);
lean_inc(v_nsmulFn_3702_);
lean_inc(v_zsmulFn_3701_);
lean_inc(v_addFn_3700_);
lean_inc(v_ltFn_x3f_3699_);
lean_inc(v_leFn_x3f_3698_);
lean_inc(v_one_x3f_3697_);
lean_inc(v_ofNatZero_3696_);
lean_inc(v_zero_3695_);
lean_inc(v_charInst_x3f_3694_);
lean_inc(v_fieldInst_x3f_3693_);
lean_inc(v_orderedRingInst_x3f_3692_);
lean_inc(v_commRingInst_x3f_3691_);
lean_inc(v_ringInst_x3f_3690_);
lean_inc(v_noNatDivInst_x3f_3689_);
lean_inc(v_isLinearInst_x3f_3688_);
lean_inc(v_orderedAddInst_x3f_3687_);
lean_inc(v_isPreorderInst_x3f_3686_);
lean_inc(v_lawfulOrderLTInst_x3f_3685_);
lean_inc(v_ltInst_x3f_3684_);
lean_inc(v_leInst_x3f_3683_);
lean_inc(v_intModuleInst_3682_);
lean_inc(v_u_3681_);
lean_inc(v_type_3680_);
lean_inc(v_ringId_x3f_3679_);
lean_inc(v_id_3678_);
lean_dec(v_v_3677_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3734_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3724_; lean_object* v_xs_x27_3725_; lean_object* v___x_3726_; lean_object* v___x_3728_; 
v___x_3724_ = lean_box(0);
v_xs_x27_3725_ = lean_array_fset(v_structs_3664_, v_a_3660_, v___x_3724_);
v___x_3726_ = l_Lean_PersistentArray_set___redArg(v_diseqs_3712_, v_y_3661_, v_fst_3662_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 34, v___x_3726_);
v___x_3728_ = v___x_3722_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_id_3678_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_ringId_x3f_3679_);
lean_ctor_set(v_reuseFailAlloc_3733_, 2, v_type_3680_);
lean_ctor_set(v_reuseFailAlloc_3733_, 3, v_u_3681_);
lean_ctor_set(v_reuseFailAlloc_3733_, 4, v_intModuleInst_3682_);
lean_ctor_set(v_reuseFailAlloc_3733_, 5, v_leInst_x3f_3683_);
lean_ctor_set(v_reuseFailAlloc_3733_, 6, v_ltInst_x3f_3684_);
lean_ctor_set(v_reuseFailAlloc_3733_, 7, v_lawfulOrderLTInst_x3f_3685_);
lean_ctor_set(v_reuseFailAlloc_3733_, 8, v_isPreorderInst_x3f_3686_);
lean_ctor_set(v_reuseFailAlloc_3733_, 9, v_orderedAddInst_x3f_3687_);
lean_ctor_set(v_reuseFailAlloc_3733_, 10, v_isLinearInst_x3f_3688_);
lean_ctor_set(v_reuseFailAlloc_3733_, 11, v_noNatDivInst_x3f_3689_);
lean_ctor_set(v_reuseFailAlloc_3733_, 12, v_ringInst_x3f_3690_);
lean_ctor_set(v_reuseFailAlloc_3733_, 13, v_commRingInst_x3f_3691_);
lean_ctor_set(v_reuseFailAlloc_3733_, 14, v_orderedRingInst_x3f_3692_);
lean_ctor_set(v_reuseFailAlloc_3733_, 15, v_fieldInst_x3f_3693_);
lean_ctor_set(v_reuseFailAlloc_3733_, 16, v_charInst_x3f_3694_);
lean_ctor_set(v_reuseFailAlloc_3733_, 17, v_zero_3695_);
lean_ctor_set(v_reuseFailAlloc_3733_, 18, v_ofNatZero_3696_);
lean_ctor_set(v_reuseFailAlloc_3733_, 19, v_one_x3f_3697_);
lean_ctor_set(v_reuseFailAlloc_3733_, 20, v_leFn_x3f_3698_);
lean_ctor_set(v_reuseFailAlloc_3733_, 21, v_ltFn_x3f_3699_);
lean_ctor_set(v_reuseFailAlloc_3733_, 22, v_addFn_3700_);
lean_ctor_set(v_reuseFailAlloc_3733_, 23, v_zsmulFn_3701_);
lean_ctor_set(v_reuseFailAlloc_3733_, 24, v_nsmulFn_3702_);
lean_ctor_set(v_reuseFailAlloc_3733_, 25, v_zsmulFn_x3f_3703_);
lean_ctor_set(v_reuseFailAlloc_3733_, 26, v_nsmulFn_x3f_3704_);
lean_ctor_set(v_reuseFailAlloc_3733_, 27, v_homomulFn_x3f_3705_);
lean_ctor_set(v_reuseFailAlloc_3733_, 28, v_subFn_3706_);
lean_ctor_set(v_reuseFailAlloc_3733_, 29, v_negFn_3707_);
lean_ctor_set(v_reuseFailAlloc_3733_, 30, v_vars_3708_);
lean_ctor_set(v_reuseFailAlloc_3733_, 31, v_varMap_3709_);
lean_ctor_set(v_reuseFailAlloc_3733_, 32, v_lowers_3710_);
lean_ctor_set(v_reuseFailAlloc_3733_, 33, v_uppers_3711_);
lean_ctor_set(v_reuseFailAlloc_3733_, 34, v___x_3726_);
lean_ctor_set(v_reuseFailAlloc_3733_, 35, v_assignment_3713_);
lean_ctor_set(v_reuseFailAlloc_3733_, 36, v_conflict_x3f_3715_);
lean_ctor_set(v_reuseFailAlloc_3733_, 37, v_diseqSplits_3716_);
lean_ctor_set(v_reuseFailAlloc_3733_, 38, v_elimEqs_3717_);
lean_ctor_set(v_reuseFailAlloc_3733_, 39, v_elimStack_3718_);
lean_ctor_set(v_reuseFailAlloc_3733_, 40, v_occurs_3719_);
lean_ctor_set(v_reuseFailAlloc_3733_, 41, v_ignored_3720_);
lean_ctor_set_uint8(v_reuseFailAlloc_3733_, sizeof(void*)*42, v_caseSplits_3714_);
v___x_3728_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
lean_object* v___x_3729_; lean_object* v___x_3731_; 
v___x_3729_ = lean_array_fset(v_xs_x27_3725_, v_a_3660_, v___x_3728_);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v___x_3729_);
v___x_3731_ = v___x_3675_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3729_);
lean_ctor_set(v_reuseFailAlloc_3732_, 1, v_typeIdOf_3665_);
lean_ctor_set(v_reuseFailAlloc_3732_, 2, v_exprToStructId_3666_);
lean_ctor_set(v_reuseFailAlloc_3732_, 3, v_exprToStructIdEntries_3667_);
lean_ctor_set(v_reuseFailAlloc_3732_, 4, v_forbiddenNatModules_3668_);
lean_ctor_set(v_reuseFailAlloc_3732_, 5, v_natStructs_3669_);
lean_ctor_set(v_reuseFailAlloc_3732_, 6, v_natTypeIdOf_3670_);
lean_ctor_set(v_reuseFailAlloc_3732_, 7, v_exprToNatStructId_3671_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed(lean_object* v_a_3744_, lean_object* v_y_3745_, lean_object* v_fst_3746_, lean_object* v_s_3747_){
_start:
{
lean_object* v_res_3748_; 
v_res_3748_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(v_a_3744_, v_y_3745_, v_fst_3746_, v_s_3747_);
lean_dec(v_y_3745_);
lean_dec(v_a_3744_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object* v_a_3749_, lean_object* v_x_3750_, lean_object* v_c_3751_, lean_object* v_as_3752_, size_t v_sz_3753_, size_t v_i_3754_, lean_object* v_b_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v_a_3769_; uint8_t v___x_3773_; 
v___x_3773_ = lean_usize_dec_lt(v_i_3754_, v_sz_3753_);
if (v___x_3773_ == 0)
{
lean_object* v___x_3774_; 
lean_dec_ref(v_c_3751_);
v___x_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3774_, 0, v_b_3755_);
return v___x_3774_;
}
else
{
lean_object* v_a_3775_; lean_object* v_fst_3776_; lean_object* v_snd_3777_; lean_object* v___x_3778_; 
lean_dec_ref(v_b_3755_);
v_a_3775_ = lean_array_uget_borrowed(v_as_3752_, v_i_3754_);
v_fst_3776_ = lean_ctor_get(v_a_3775_, 0);
v_snd_3777_ = lean_ctor_get(v_a_3775_, 1);
lean_inc(v_snd_3777_);
lean_inc(v_fst_3776_);
lean_inc_ref(v_c_3751_);
v___x_3778_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_3749_, v_x_3750_, v_c_3751_, v_fst_3776_, v_snd_3777_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; lean_object* v___x_3780_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3779_);
lean_dec_ref(v___x_3778_);
v___x_3780_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
if (lean_obj_tag(v_a_3779_) == 1)
{
lean_object* v_val_3781_; lean_object* v___x_3782_; 
v_val_3781_ = lean_ctor_get(v_a_3779_, 0);
lean_inc(v_val_3781_);
lean_dec_ref(v_a_3779_);
v___x_3782_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_val_3781_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v___x_3783_; 
lean_dec_ref(v___x_3782_);
v___x_3783_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3793_; 
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3786_ = v___x_3783_;
v_isShared_3787_ = v_isSharedCheck_3793_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3783_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3793_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
uint8_t v___x_3788_; 
v___x_3788_ = lean_unbox(v_a_3784_);
lean_dec(v_a_3784_);
if (v___x_3788_ == 0)
{
lean_del_object(v___x_3786_);
v_a_3769_ = v___x_3780_;
goto v___jp_3768_;
}
else
{
lean_object* v___x_3789_; lean_object* v___x_3791_; 
lean_dec_ref(v_c_3751_);
v___x_3789_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 0, v___x_3789_);
v___x_3791_ = v___x_3786_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3789_);
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
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_dec_ref(v_c_3751_);
v_a_3794_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3783_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3783_);
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
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
lean_dec_ref(v_c_3751_);
v_a_3802_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3782_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3782_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
else
{
lean_object* v___x_3810_; 
lean_dec(v_a_3779_);
v___x_3810_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_snd_3777_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_dec_ref(v___x_3810_);
v_a_3769_ = v___x_3780_;
goto v___jp_3768_;
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_dec_ref(v_c_3751_);
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3810_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3810_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
lean_dec_ref(v_c_3751_);
v_a_3819_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3821_ = v___x_3778_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3778_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3819_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
v___jp_3768_:
{
size_t v___x_3770_; size_t v___x_3771_; 
v___x_3770_ = ((size_t)1ULL);
v___x_3771_ = lean_usize_add(v_i_3754_, v___x_3770_);
lean_inc_ref(v_a_3769_);
v_i_3754_ = v___x_3771_;
v_b_3755_ = v_a_3769_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object** _args){
lean_object* v_a_3827_ = _args[0];
lean_object* v_x_3828_ = _args[1];
lean_object* v_c_3829_ = _args[2];
lean_object* v_as_3830_ = _args[3];
lean_object* v_sz_3831_ = _args[4];
lean_object* v_i_3832_ = _args[5];
lean_object* v_b_3833_ = _args[6];
lean_object* v___y_3834_ = _args[7];
lean_object* v___y_3835_ = _args[8];
lean_object* v___y_3836_ = _args[9];
lean_object* v___y_3837_ = _args[10];
lean_object* v___y_3838_ = _args[11];
lean_object* v___y_3839_ = _args[12];
lean_object* v___y_3840_ = _args[13];
lean_object* v___y_3841_ = _args[14];
lean_object* v___y_3842_ = _args[15];
lean_object* v___y_3843_ = _args[16];
lean_object* v___y_3844_ = _args[17];
lean_object* v___y_3845_ = _args[18];
_start:
{
size_t v_sz_boxed_3846_; size_t v_i_boxed_3847_; lean_object* v_res_3848_; 
v_sz_boxed_3846_ = lean_unbox_usize(v_sz_3831_);
lean_dec(v_sz_3831_);
v_i_boxed_3847_ = lean_unbox_usize(v_i_3832_);
lean_dec(v_i_3832_);
v_res_3848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3827_, v_x_3828_, v_c_3829_, v_as_3830_, v_sz_boxed_3846_, v_i_boxed_3847_, v_b_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v_as_3830_);
lean_dec(v_x_3828_);
lean_dec(v_a_3827_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object* v_a_3849_, lean_object* v_x_3850_, lean_object* v_c_3851_, lean_object* v_y_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_){
_start:
{
lean_object* v___x_3865_; 
v___x_3865_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3925_; 
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3868_ = v___x_3865_;
v_isShared_3869_ = v_isSharedCheck_3925_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3865_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3925_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
uint8_t v___x_3870_; 
v___x_3870_ = lean_unbox(v_a_3866_);
lean_dec(v_a_3866_);
if (v___x_3870_ == 0)
{
lean_object* v___x_3871_; 
lean_del_object(v___x_3868_);
v___x_3871_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; lean_object* v___y_3874_; lean_object* v_diseqs_3907_; lean_object* v_size_3908_; lean_object* v___x_3909_; uint8_t v___x_3910_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3872_);
lean_dec_ref(v___x_3871_);
v_diseqs_3907_ = lean_ctor_get(v_a_3872_, 34);
lean_inc_ref(v_diseqs_3907_);
lean_dec(v_a_3872_);
v_size_3908_ = lean_ctor_get(v_diseqs_3907_, 2);
v___x_3909_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_3910_ = lean_nat_dec_lt(v_y_3852_, v_size_3908_);
if (v___x_3910_ == 0)
{
lean_object* v___x_3911_; 
lean_dec_ref(v_diseqs_3907_);
v___x_3911_ = l_outOfBounds___redArg(v___x_3909_);
v___y_3874_ = v___x_3911_;
goto v___jp_3873_;
}
else
{
lean_object* v___x_3912_; 
v___x_3912_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3909_, v_diseqs_3907_, v_y_3852_);
lean_dec_ref(v_diseqs_3907_);
v___y_3874_ = v___x_3912_;
goto v___jp_3873_;
}
v___jp_3873_:
{
lean_object* v___x_3875_; lean_object* v_fst_3876_; lean_object* v_snd_3877_; lean_object* v___f_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3875_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3850_, v___y_3874_);
lean_dec_ref(v___y_3874_);
v_fst_3876_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_fst_3876_);
v_snd_3877_ = lean_ctor_get(v___x_3875_, 1);
lean_inc(v_snd_3877_);
lean_dec_ref(v___x_3875_);
lean_inc(v_a_3853_);
v___f_3878_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3878_, 0, v_a_3853_);
lean_closure_set(v___f_3878_, 1, v_y_3852_);
lean_closure_set(v___f_3878_, 2, v_fst_3876_);
v___x_3879_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3880_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3879_, v___f_3878_, v_a_3854_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v___x_3881_; lean_object* v___x_3882_; size_t v_sz_3883_; size_t v___x_3884_; lean_object* v___x_3885_; 
lean_dec_ref(v___x_3880_);
v___x_3881_ = lean_box(0);
v___x_3882_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_3883_ = lean_array_size(v_snd_3877_);
v___x_3884_ = ((size_t)0ULL);
v___x_3885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3849_, v_x_3850_, v_c_3851_, v_snd_3877_, v_sz_3883_, v___x_3884_, v___x_3882_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_);
lean_dec(v_snd_3877_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3898_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3888_ = v___x_3885_;
v_isShared_3889_ = v_isSharedCheck_3898_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3885_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3898_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v_fst_3890_; 
v_fst_3890_ = lean_ctor_get(v_a_3886_, 0);
lean_inc(v_fst_3890_);
lean_dec(v_a_3886_);
if (lean_obj_tag(v_fst_3890_) == 0)
{
lean_object* v___x_3892_; 
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3881_);
v___x_3892_ = v___x_3888_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v___x_3881_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
else
{
lean_object* v_val_3894_; lean_object* v___x_3896_; 
v_val_3894_ = lean_ctor_get(v_fst_3890_, 0);
lean_inc(v_val_3894_);
lean_dec_ref(v_fst_3890_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v_val_3894_);
v___x_3896_ = v___x_3888_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_val_3894_);
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
v_a_3899_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3901_ = v___x_3885_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3885_);
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
else
{
lean_dec(v_snd_3877_);
lean_dec_ref(v_c_3851_);
return v___x_3880_;
}
}
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
lean_dec(v_y_3852_);
lean_dec_ref(v_c_3851_);
v_a_3913_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3871_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3871_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
else
{
lean_object* v___x_3921_; lean_object* v___x_3923_; 
lean_dec(v_y_3852_);
lean_dec_ref(v_c_3851_);
v___x_3921_ = lean_box(0);
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 0, v___x_3921_);
v___x_3923_ = v___x_3868_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3921_);
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
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3933_; 
lean_dec(v_y_3852_);
lean_dec_ref(v_c_3851_);
v_a_3926_ = lean_ctor_get(v___x_3865_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3928_ = v___x_3865_;
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3865_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3931_; 
if (v_isShared_3929_ == 0)
{
v___x_3931_ = v___x_3928_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3926_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object* v_a_3934_, lean_object* v_x_3935_, lean_object* v_c_3936_, lean_object* v_y_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_){
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v_a_3934_, v_x_3935_, v_c_3936_, v_y_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
lean_dec(v_a_3948_);
lean_dec_ref(v_a_3947_);
lean_dec(v_a_3946_);
lean_dec_ref(v_a_3945_);
lean_dec(v_a_3944_);
lean_dec_ref(v_a_3943_);
lean_dec(v_a_3942_);
lean_dec_ref(v_a_3941_);
lean_dec(v_a_3940_);
lean_dec(v_a_3939_);
lean_dec(v_a_3938_);
lean_dec(v_x_3935_);
lean_dec(v_a_3934_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object* v_a_3951_, lean_object* v_x_3952_, lean_object* v_c_3953_, lean_object* v_y_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_){
_start:
{
lean_object* v___x_3967_; 
lean_inc(v_y_3954_);
lean_inc_ref(v_c_3953_);
lean_inc(v_x_3952_);
lean_inc(v_a_3951_);
v___x_3967_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_3951_, v_x_3952_, v_c_3953_, v_y_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v___x_3968_; 
lean_dec_ref(v___x_3967_);
lean_inc(v_y_3954_);
lean_inc_ref(v_c_3953_);
lean_inc(v_x_3952_);
lean_inc(v_a_3951_);
v___x_3968_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_3951_, v_x_3952_, v_c_3953_, v_y_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v___x_3969_; lean_object* v___x_3970_; 
lean_dec_ref(v___x_3968_);
v___x_3969_ = lean_nat_to_int(v_a_3951_);
v___x_3970_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v___x_3969_, v_x_3952_, v_c_3953_, v_y_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_);
lean_dec(v_x_3952_);
lean_dec(v___x_3969_);
return v___x_3970_;
}
else
{
lean_dec(v_y_3954_);
lean_dec_ref(v_c_3953_);
lean_dec(v_x_3952_);
lean_dec(v_a_3951_);
return v___x_3968_;
}
}
else
{
lean_dec(v_y_3954_);
lean_dec_ref(v_c_3953_);
lean_dec(v_x_3952_);
lean_dec(v_a_3951_);
return v___x_3967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object* v_a_3971_, lean_object* v_x_3972_, lean_object* v_c_3973_, lean_object* v_y_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_3971_, v_x_3972_, v_c_3973_, v_y_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_a_3981_);
lean_dec_ref(v_a_3980_);
lean_dec(v_a_3979_);
lean_dec_ref(v_a_3978_);
lean_dec(v_a_3977_);
lean_dec(v_a_3976_);
lean_dec(v_a_3975_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(lean_object* v_a_3988_, lean_object* v_x_3989_, lean_object* v_s_3990_){
_start:
{
lean_object* v_structs_3991_; lean_object* v_typeIdOf_3992_; lean_object* v_exprToStructId_3993_; lean_object* v_exprToStructIdEntries_3994_; lean_object* v_forbiddenNatModules_3995_; lean_object* v_natStructs_3996_; lean_object* v_natTypeIdOf_3997_; lean_object* v_exprToNatStructId_3998_; lean_object* v___x_3999_; uint8_t v___x_4000_; 
v_structs_3991_ = lean_ctor_get(v_s_3990_, 0);
v_typeIdOf_3992_ = lean_ctor_get(v_s_3990_, 1);
v_exprToStructId_3993_ = lean_ctor_get(v_s_3990_, 2);
v_exprToStructIdEntries_3994_ = lean_ctor_get(v_s_3990_, 3);
v_forbiddenNatModules_3995_ = lean_ctor_get(v_s_3990_, 4);
v_natStructs_3996_ = lean_ctor_get(v_s_3990_, 5);
v_natTypeIdOf_3997_ = lean_ctor_get(v_s_3990_, 6);
v_exprToNatStructId_3998_ = lean_ctor_get(v_s_3990_, 7);
v___x_3999_ = lean_array_get_size(v_structs_3991_);
v___x_4000_ = lean_nat_dec_lt(v_a_3988_, v___x_3999_);
if (v___x_4000_ == 0)
{
return v_s_3990_;
}
else
{
lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4063_; 
lean_inc_ref(v_exprToNatStructId_3998_);
lean_inc_ref(v_natTypeIdOf_3997_);
lean_inc_ref(v_natStructs_3996_);
lean_inc_ref(v_forbiddenNatModules_3995_);
lean_inc_ref(v_exprToStructIdEntries_3994_);
lean_inc_ref(v_exprToStructId_3993_);
lean_inc_ref(v_typeIdOf_3992_);
lean_inc_ref(v_structs_3991_);
v_isSharedCheck_4063_ = !lean_is_exclusive(v_s_3990_);
if (v_isSharedCheck_4063_ == 0)
{
lean_object* v_unused_4064_; lean_object* v_unused_4065_; lean_object* v_unused_4066_; lean_object* v_unused_4067_; lean_object* v_unused_4068_; lean_object* v_unused_4069_; lean_object* v_unused_4070_; lean_object* v_unused_4071_; 
v_unused_4064_ = lean_ctor_get(v_s_3990_, 7);
lean_dec(v_unused_4064_);
v_unused_4065_ = lean_ctor_get(v_s_3990_, 6);
lean_dec(v_unused_4065_);
v_unused_4066_ = lean_ctor_get(v_s_3990_, 5);
lean_dec(v_unused_4066_);
v_unused_4067_ = lean_ctor_get(v_s_3990_, 4);
lean_dec(v_unused_4067_);
v_unused_4068_ = lean_ctor_get(v_s_3990_, 3);
lean_dec(v_unused_4068_);
v_unused_4069_ = lean_ctor_get(v_s_3990_, 2);
lean_dec(v_unused_4069_);
v_unused_4070_ = lean_ctor_get(v_s_3990_, 1);
lean_dec(v_unused_4070_);
v_unused_4071_ = lean_ctor_get(v_s_3990_, 0);
lean_dec(v_unused_4071_);
v___x_4002_ = v_s_3990_;
v_isShared_4003_ = v_isSharedCheck_4063_;
goto v_resetjp_4001_;
}
else
{
lean_dec(v_s_3990_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4063_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v_v_4004_; lean_object* v_id_4005_; lean_object* v_ringId_x3f_4006_; lean_object* v_type_4007_; lean_object* v_u_4008_; lean_object* v_intModuleInst_4009_; lean_object* v_leInst_x3f_4010_; lean_object* v_ltInst_x3f_4011_; lean_object* v_lawfulOrderLTInst_x3f_4012_; lean_object* v_isPreorderInst_x3f_4013_; lean_object* v_orderedAddInst_x3f_4014_; lean_object* v_isLinearInst_x3f_4015_; lean_object* v_noNatDivInst_x3f_4016_; lean_object* v_ringInst_x3f_4017_; lean_object* v_commRingInst_x3f_4018_; lean_object* v_orderedRingInst_x3f_4019_; lean_object* v_fieldInst_x3f_4020_; lean_object* v_charInst_x3f_4021_; lean_object* v_zero_4022_; lean_object* v_ofNatZero_4023_; lean_object* v_one_x3f_4024_; lean_object* v_leFn_x3f_4025_; lean_object* v_ltFn_x3f_4026_; lean_object* v_addFn_4027_; lean_object* v_zsmulFn_4028_; lean_object* v_nsmulFn_4029_; lean_object* v_zsmulFn_x3f_4030_; lean_object* v_nsmulFn_x3f_4031_; lean_object* v_homomulFn_x3f_4032_; lean_object* v_subFn_4033_; lean_object* v_negFn_4034_; lean_object* v_vars_4035_; lean_object* v_varMap_4036_; lean_object* v_lowers_4037_; lean_object* v_uppers_4038_; lean_object* v_diseqs_4039_; lean_object* v_assignment_4040_; uint8_t v_caseSplits_4041_; lean_object* v_conflict_x3f_4042_; lean_object* v_diseqSplits_4043_; lean_object* v_elimEqs_4044_; lean_object* v_elimStack_4045_; lean_object* v_occurs_4046_; lean_object* v_ignored_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4062_; 
v_v_4004_ = lean_array_fget(v_structs_3991_, v_a_3988_);
v_id_4005_ = lean_ctor_get(v_v_4004_, 0);
v_ringId_x3f_4006_ = lean_ctor_get(v_v_4004_, 1);
v_type_4007_ = lean_ctor_get(v_v_4004_, 2);
v_u_4008_ = lean_ctor_get(v_v_4004_, 3);
v_intModuleInst_4009_ = lean_ctor_get(v_v_4004_, 4);
v_leInst_x3f_4010_ = lean_ctor_get(v_v_4004_, 5);
v_ltInst_x3f_4011_ = lean_ctor_get(v_v_4004_, 6);
v_lawfulOrderLTInst_x3f_4012_ = lean_ctor_get(v_v_4004_, 7);
v_isPreorderInst_x3f_4013_ = lean_ctor_get(v_v_4004_, 8);
v_orderedAddInst_x3f_4014_ = lean_ctor_get(v_v_4004_, 9);
v_isLinearInst_x3f_4015_ = lean_ctor_get(v_v_4004_, 10);
v_noNatDivInst_x3f_4016_ = lean_ctor_get(v_v_4004_, 11);
v_ringInst_x3f_4017_ = lean_ctor_get(v_v_4004_, 12);
v_commRingInst_x3f_4018_ = lean_ctor_get(v_v_4004_, 13);
v_orderedRingInst_x3f_4019_ = lean_ctor_get(v_v_4004_, 14);
v_fieldInst_x3f_4020_ = lean_ctor_get(v_v_4004_, 15);
v_charInst_x3f_4021_ = lean_ctor_get(v_v_4004_, 16);
v_zero_4022_ = lean_ctor_get(v_v_4004_, 17);
v_ofNatZero_4023_ = lean_ctor_get(v_v_4004_, 18);
v_one_x3f_4024_ = lean_ctor_get(v_v_4004_, 19);
v_leFn_x3f_4025_ = lean_ctor_get(v_v_4004_, 20);
v_ltFn_x3f_4026_ = lean_ctor_get(v_v_4004_, 21);
v_addFn_4027_ = lean_ctor_get(v_v_4004_, 22);
v_zsmulFn_4028_ = lean_ctor_get(v_v_4004_, 23);
v_nsmulFn_4029_ = lean_ctor_get(v_v_4004_, 24);
v_zsmulFn_x3f_4030_ = lean_ctor_get(v_v_4004_, 25);
v_nsmulFn_x3f_4031_ = lean_ctor_get(v_v_4004_, 26);
v_homomulFn_x3f_4032_ = lean_ctor_get(v_v_4004_, 27);
v_subFn_4033_ = lean_ctor_get(v_v_4004_, 28);
v_negFn_4034_ = lean_ctor_get(v_v_4004_, 29);
v_vars_4035_ = lean_ctor_get(v_v_4004_, 30);
v_varMap_4036_ = lean_ctor_get(v_v_4004_, 31);
v_lowers_4037_ = lean_ctor_get(v_v_4004_, 32);
v_uppers_4038_ = lean_ctor_get(v_v_4004_, 33);
v_diseqs_4039_ = lean_ctor_get(v_v_4004_, 34);
v_assignment_4040_ = lean_ctor_get(v_v_4004_, 35);
v_caseSplits_4041_ = lean_ctor_get_uint8(v_v_4004_, sizeof(void*)*42);
v_conflict_x3f_4042_ = lean_ctor_get(v_v_4004_, 36);
v_diseqSplits_4043_ = lean_ctor_get(v_v_4004_, 37);
v_elimEqs_4044_ = lean_ctor_get(v_v_4004_, 38);
v_elimStack_4045_ = lean_ctor_get(v_v_4004_, 39);
v_occurs_4046_ = lean_ctor_get(v_v_4004_, 40);
v_ignored_4047_ = lean_ctor_get(v_v_4004_, 41);
v_isSharedCheck_4062_ = !lean_is_exclusive(v_v_4004_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4049_ = v_v_4004_;
v_isShared_4050_ = v_isSharedCheck_4062_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_ignored_4047_);
lean_inc(v_occurs_4046_);
lean_inc(v_elimStack_4045_);
lean_inc(v_elimEqs_4044_);
lean_inc(v_diseqSplits_4043_);
lean_inc(v_conflict_x3f_4042_);
lean_inc(v_assignment_4040_);
lean_inc(v_diseqs_4039_);
lean_inc(v_uppers_4038_);
lean_inc(v_lowers_4037_);
lean_inc(v_varMap_4036_);
lean_inc(v_vars_4035_);
lean_inc(v_negFn_4034_);
lean_inc(v_subFn_4033_);
lean_inc(v_homomulFn_x3f_4032_);
lean_inc(v_nsmulFn_x3f_4031_);
lean_inc(v_zsmulFn_x3f_4030_);
lean_inc(v_nsmulFn_4029_);
lean_inc(v_zsmulFn_4028_);
lean_inc(v_addFn_4027_);
lean_inc(v_ltFn_x3f_4026_);
lean_inc(v_leFn_x3f_4025_);
lean_inc(v_one_x3f_4024_);
lean_inc(v_ofNatZero_4023_);
lean_inc(v_zero_4022_);
lean_inc(v_charInst_x3f_4021_);
lean_inc(v_fieldInst_x3f_4020_);
lean_inc(v_orderedRingInst_x3f_4019_);
lean_inc(v_commRingInst_x3f_4018_);
lean_inc(v_ringInst_x3f_4017_);
lean_inc(v_noNatDivInst_x3f_4016_);
lean_inc(v_isLinearInst_x3f_4015_);
lean_inc(v_orderedAddInst_x3f_4014_);
lean_inc(v_isPreorderInst_x3f_4013_);
lean_inc(v_lawfulOrderLTInst_x3f_4012_);
lean_inc(v_ltInst_x3f_4011_);
lean_inc(v_leInst_x3f_4010_);
lean_inc(v_intModuleInst_4009_);
lean_inc(v_u_4008_);
lean_inc(v_type_4007_);
lean_inc(v_ringId_x3f_4006_);
lean_inc(v_id_4005_);
lean_dec(v_v_4004_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4062_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4051_; lean_object* v_xs_x27_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4056_; 
v___x_4051_ = lean_box(0);
v_xs_x27_4052_ = lean_array_fset(v_structs_3991_, v_a_3988_, v___x_4051_);
v___x_4053_ = lean_box(1);
v___x_4054_ = l_Lean_PersistentArray_set___redArg(v_occurs_4046_, v_x_3989_, v___x_4053_);
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 40, v___x_4054_);
v___x_4056_ = v___x_4049_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_id_4005_);
lean_ctor_set(v_reuseFailAlloc_4061_, 1, v_ringId_x3f_4006_);
lean_ctor_set(v_reuseFailAlloc_4061_, 2, v_type_4007_);
lean_ctor_set(v_reuseFailAlloc_4061_, 3, v_u_4008_);
lean_ctor_set(v_reuseFailAlloc_4061_, 4, v_intModuleInst_4009_);
lean_ctor_set(v_reuseFailAlloc_4061_, 5, v_leInst_x3f_4010_);
lean_ctor_set(v_reuseFailAlloc_4061_, 6, v_ltInst_x3f_4011_);
lean_ctor_set(v_reuseFailAlloc_4061_, 7, v_lawfulOrderLTInst_x3f_4012_);
lean_ctor_set(v_reuseFailAlloc_4061_, 8, v_isPreorderInst_x3f_4013_);
lean_ctor_set(v_reuseFailAlloc_4061_, 9, v_orderedAddInst_x3f_4014_);
lean_ctor_set(v_reuseFailAlloc_4061_, 10, v_isLinearInst_x3f_4015_);
lean_ctor_set(v_reuseFailAlloc_4061_, 11, v_noNatDivInst_x3f_4016_);
lean_ctor_set(v_reuseFailAlloc_4061_, 12, v_ringInst_x3f_4017_);
lean_ctor_set(v_reuseFailAlloc_4061_, 13, v_commRingInst_x3f_4018_);
lean_ctor_set(v_reuseFailAlloc_4061_, 14, v_orderedRingInst_x3f_4019_);
lean_ctor_set(v_reuseFailAlloc_4061_, 15, v_fieldInst_x3f_4020_);
lean_ctor_set(v_reuseFailAlloc_4061_, 16, v_charInst_x3f_4021_);
lean_ctor_set(v_reuseFailAlloc_4061_, 17, v_zero_4022_);
lean_ctor_set(v_reuseFailAlloc_4061_, 18, v_ofNatZero_4023_);
lean_ctor_set(v_reuseFailAlloc_4061_, 19, v_one_x3f_4024_);
lean_ctor_set(v_reuseFailAlloc_4061_, 20, v_leFn_x3f_4025_);
lean_ctor_set(v_reuseFailAlloc_4061_, 21, v_ltFn_x3f_4026_);
lean_ctor_set(v_reuseFailAlloc_4061_, 22, v_addFn_4027_);
lean_ctor_set(v_reuseFailAlloc_4061_, 23, v_zsmulFn_4028_);
lean_ctor_set(v_reuseFailAlloc_4061_, 24, v_nsmulFn_4029_);
lean_ctor_set(v_reuseFailAlloc_4061_, 25, v_zsmulFn_x3f_4030_);
lean_ctor_set(v_reuseFailAlloc_4061_, 26, v_nsmulFn_x3f_4031_);
lean_ctor_set(v_reuseFailAlloc_4061_, 27, v_homomulFn_x3f_4032_);
lean_ctor_set(v_reuseFailAlloc_4061_, 28, v_subFn_4033_);
lean_ctor_set(v_reuseFailAlloc_4061_, 29, v_negFn_4034_);
lean_ctor_set(v_reuseFailAlloc_4061_, 30, v_vars_4035_);
lean_ctor_set(v_reuseFailAlloc_4061_, 31, v_varMap_4036_);
lean_ctor_set(v_reuseFailAlloc_4061_, 32, v_lowers_4037_);
lean_ctor_set(v_reuseFailAlloc_4061_, 33, v_uppers_4038_);
lean_ctor_set(v_reuseFailAlloc_4061_, 34, v_diseqs_4039_);
lean_ctor_set(v_reuseFailAlloc_4061_, 35, v_assignment_4040_);
lean_ctor_set(v_reuseFailAlloc_4061_, 36, v_conflict_x3f_4042_);
lean_ctor_set(v_reuseFailAlloc_4061_, 37, v_diseqSplits_4043_);
lean_ctor_set(v_reuseFailAlloc_4061_, 38, v_elimEqs_4044_);
lean_ctor_set(v_reuseFailAlloc_4061_, 39, v_elimStack_4045_);
lean_ctor_set(v_reuseFailAlloc_4061_, 40, v___x_4054_);
lean_ctor_set(v_reuseFailAlloc_4061_, 41, v_ignored_4047_);
lean_ctor_set_uint8(v_reuseFailAlloc_4061_, sizeof(void*)*42, v_caseSplits_4041_);
v___x_4056_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
lean_object* v___x_4057_; lean_object* v___x_4059_; 
v___x_4057_ = lean_array_fset(v_xs_x27_4052_, v_a_3988_, v___x_4056_);
if (v_isShared_4003_ == 0)
{
lean_ctor_set(v___x_4002_, 0, v___x_4057_);
v___x_4059_ = v___x_4002_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4057_);
lean_ctor_set(v_reuseFailAlloc_4060_, 1, v_typeIdOf_3992_);
lean_ctor_set(v_reuseFailAlloc_4060_, 2, v_exprToStructId_3993_);
lean_ctor_set(v_reuseFailAlloc_4060_, 3, v_exprToStructIdEntries_3994_);
lean_ctor_set(v_reuseFailAlloc_4060_, 4, v_forbiddenNatModules_3995_);
lean_ctor_set(v_reuseFailAlloc_4060_, 5, v_natStructs_3996_);
lean_ctor_set(v_reuseFailAlloc_4060_, 6, v_natTypeIdOf_3997_);
lean_ctor_set(v_reuseFailAlloc_4060_, 7, v_exprToNatStructId_3998_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed(lean_object* v_a_4072_, lean_object* v_x_4073_, lean_object* v_s_4074_){
_start:
{
lean_object* v_res_4075_; 
v_res_4075_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(v_a_4072_, v_x_4073_, v_s_4074_);
lean_dec(v_x_4073_);
lean_dec(v_a_4072_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object* v_a_4076_, lean_object* v_x_4077_, lean_object* v_c_4078_, lean_object* v_init_4079_, lean_object* v_x_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
if (lean_obj_tag(v_x_4080_) == 0)
{
lean_object* v_k_4093_; lean_object* v_l_4094_; lean_object* v_r_4095_; lean_object* v___x_4096_; 
v_k_4093_ = lean_ctor_get(v_x_4080_, 1);
lean_inc(v_k_4093_);
v_l_4094_ = lean_ctor_get(v_x_4080_, 3);
lean_inc(v_l_4094_);
v_r_4095_ = lean_ctor_get(v_x_4080_, 4);
lean_inc(v_r_4095_);
lean_dec_ref(v_x_4080_);
lean_inc_ref(v_c_4078_);
lean_inc(v_x_4077_);
lean_inc(v_a_4076_);
v___x_4096_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4076_, v_x_4077_, v_c_4078_, v_init_4079_, v_l_4094_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v___x_4097_; 
lean_dec_ref(v___x_4096_);
lean_inc_ref(v_c_4078_);
lean_inc(v_x_4077_);
lean_inc(v_a_4076_);
v___x_4097_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4076_, v_x_4077_, v_c_4078_, v_k_4093_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v___x_4098_; 
lean_dec_ref(v___x_4097_);
v___x_4098_ = lean_box(0);
v_init_4079_ = v___x_4098_;
v_x_4080_ = v_r_4095_;
goto _start;
}
else
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4107_; 
lean_dec(v_r_4095_);
lean_dec_ref(v_c_4078_);
lean_dec(v_x_4077_);
lean_dec(v_a_4076_);
v_a_4100_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4102_ = v___x_4097_;
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4097_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
else
{
lean_dec(v_r_4095_);
lean_dec(v_k_4093_);
lean_dec_ref(v_c_4078_);
lean_dec(v_x_4077_);
lean_dec(v_a_4076_);
return v___x_4096_;
}
}
else
{
lean_object* v___x_4108_; lean_object* v___x_4109_; 
lean_dec_ref(v_c_4078_);
lean_dec(v_x_4077_);
lean_dec(v_a_4076_);
v___x_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4108_, 0, v_init_4079_);
v___x_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4108_);
return v___x_4109_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object** _args){
lean_object* v_a_4110_ = _args[0];
lean_object* v_x_4111_ = _args[1];
lean_object* v_c_4112_ = _args[2];
lean_object* v_init_4113_ = _args[3];
lean_object* v_x_4114_ = _args[4];
lean_object* v___y_4115_ = _args[5];
lean_object* v___y_4116_ = _args[6];
lean_object* v___y_4117_ = _args[7];
lean_object* v___y_4118_ = _args[8];
lean_object* v___y_4119_ = _args[9];
lean_object* v___y_4120_ = _args[10];
lean_object* v___y_4121_ = _args[11];
lean_object* v___y_4122_ = _args[12];
lean_object* v___y_4123_ = _args[13];
lean_object* v___y_4124_ = _args[14];
lean_object* v___y_4125_ = _args[15];
lean_object* v___y_4126_ = _args[16];
_start:
{
lean_object* v_res_4127_; 
v_res_4127_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4110_, v_x_4111_, v_c_4112_, v_init_4113_, v_x_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec(v___y_4116_);
lean_dec(v___y_4115_);
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object* v_a_4128_, lean_object* v_x_4129_, lean_object* v_c_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_){
_start:
{
lean_object* v___x_4143_; 
v___x_4143_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; lean_object* v_occurs_4145_; lean_object* v_size_4146_; lean_object* v___f_4147_; lean_object* v___y_4149_; lean_object* v___x_4171_; uint8_t v___x_4172_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4144_);
lean_dec_ref(v___x_4143_);
v_occurs_4145_ = lean_ctor_get(v_a_4144_, 40);
lean_inc_ref(v_occurs_4145_);
lean_dec(v_a_4144_);
v_size_4146_ = lean_ctor_get(v_occurs_4145_, 2);
lean_inc(v_x_4129_);
lean_inc(v_a_4131_);
v___f_4147_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4147_, 0, v_a_4131_);
lean_closure_set(v___f_4147_, 1, v_x_4129_);
v___x_4171_ = lean_box(1);
v___x_4172_ = lean_nat_dec_lt(v_x_4129_, v_size_4146_);
if (v___x_4172_ == 0)
{
lean_object* v___x_4173_; 
lean_dec_ref(v_occurs_4145_);
v___x_4173_ = l_outOfBounds___redArg(v___x_4171_);
v___y_4149_ = v___x_4173_;
goto v___jp_4148_;
}
else
{
lean_object* v___x_4174_; 
v___x_4174_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4171_, v_occurs_4145_, v_x_4129_);
lean_dec_ref(v_occurs_4145_);
v___y_4149_ = v___x_4174_;
goto v___jp_4148_;
}
v___jp_4148_:
{
lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4150_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4151_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4150_, v___f_4147_, v_a_4132_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v___x_4152_; 
lean_dec_ref(v___x_4151_);
lean_inc_ref(v_c_4130_);
lean_inc_n(v_x_4129_, 2);
lean_inc(v_a_4128_);
v___x_4152_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4128_, v_x_4129_, v_c_4130_, v_x_4129_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v___x_4153_; lean_object* v___x_4154_; 
lean_dec_ref(v___x_4152_);
v___x_4153_ = lean_box(0);
v___x_4154_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4128_, v_x_4129_, v_c_4130_, v___x_4153_, v___y_4149_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4161_; 
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4161_ == 0)
{
lean_object* v_unused_4162_; 
v_unused_4162_ = lean_ctor_get(v___x_4154_, 0);
lean_dec(v_unused_4162_);
v___x_4156_ = v___x_4154_;
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
else
{
lean_dec(v___x_4154_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4159_; 
if (v_isShared_4157_ == 0)
{
lean_ctor_set(v___x_4156_, 0, v___x_4153_);
v___x_4159_ = v___x_4156_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4153_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
else
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4170_; 
v_a_4163_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4170_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4165_ = v___x_4154_;
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4154_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4168_; 
if (v_isShared_4166_ == 0)
{
v___x_4168_ = v___x_4165_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v_a_4163_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
return v___x_4168_;
}
}
}
}
else
{
lean_dec(v___y_4149_);
lean_dec_ref(v_c_4130_);
lean_dec(v_x_4129_);
lean_dec(v_a_4128_);
return v___x_4152_;
}
}
else
{
lean_dec(v___y_4149_);
lean_dec_ref(v_c_4130_);
lean_dec(v_x_4129_);
lean_dec(v_a_4128_);
return v___x_4151_;
}
}
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
lean_dec_ref(v_c_4130_);
lean_dec(v_x_4129_);
lean_dec(v_a_4128_);
v_a_4175_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___x_4143_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___x_4143_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___boxed(lean_object* v_a_4183_, lean_object* v_x_4184_, lean_object* v_c_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v_a_4183_, v_x_4184_, v_c_4185_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_);
lean_dec(v_a_4196_);
lean_dec_ref(v_a_4195_);
lean_dec(v_a_4194_);
lean_dec_ref(v_a_4193_);
lean_dec(v_a_4192_);
lean_dec_ref(v_a_4191_);
lean_dec(v_a_4190_);
lean_dec_ref(v_a_4189_);
lean_dec(v_a_4188_);
lean_dec(v_a_4187_);
lean_dec(v_a_4186_);
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(lean_object* v_c_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_){
_start:
{
lean_object* v_p_4216_; 
v_p_4216_ = lean_ctor_get(v_c_4199_, 0);
if (lean_obj_tag(v_p_4216_) == 1)
{
lean_object* v_k_4217_; lean_object* v_v_4218_; lean_object* v_p_4219_; lean_object* v_y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___x_4270_; lean_object* v___x_4271_; uint8_t v___x_4272_; 
v_k_4217_ = lean_ctor_get(v_p_4216_, 0);
v_v_4218_ = lean_ctor_get(v_p_4216_, 1);
v_p_4219_ = lean_ctor_get(v_p_4216_, 2);
v___x_4270_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_4271_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4272_ = lean_int_dec_eq(v_k_4217_, v___x_4271_);
if (v___x_4272_ == 0)
{
uint8_t v___x_4273_; 
v___x_4273_ = lean_int_dec_eq(v_k_4217_, v___x_4270_);
if (v___x_4273_ == 0)
{
goto v___jp_4212_;
}
else
{
if (lean_obj_tag(v_p_4219_) == 1)
{
lean_object* v_k_4274_; lean_object* v_v_4275_; lean_object* v_p_4276_; uint8_t v___x_4277_; 
v_k_4274_ = lean_ctor_get(v_p_4219_, 0);
v_v_4275_ = lean_ctor_get(v_p_4219_, 1);
v_p_4276_ = lean_ctor_get(v_p_4219_, 2);
v___x_4277_ = lean_int_dec_eq(v_k_4274_, v___x_4271_);
if (v___x_4277_ == 0)
{
goto v___jp_4212_;
}
else
{
if (lean_obj_tag(v_p_4276_) == 0)
{
v_y_4221_ = v_v_4275_;
v___y_4222_ = v_a_4200_;
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
goto v___jp_4220_;
}
else
{
goto v___jp_4212_;
}
}
}
else
{
goto v___jp_4212_;
}
}
}
else
{
if (lean_obj_tag(v_p_4219_) == 1)
{
lean_object* v_k_4278_; lean_object* v_v_4279_; lean_object* v_p_4280_; uint8_t v___x_4281_; 
v_k_4278_ = lean_ctor_get(v_p_4219_, 0);
v_v_4279_ = lean_ctor_get(v_p_4219_, 1);
v_p_4280_ = lean_ctor_get(v_p_4219_, 2);
v___x_4281_ = lean_int_dec_eq(v_k_4278_, v___x_4270_);
if (v___x_4281_ == 0)
{
goto v___jp_4212_;
}
else
{
if (lean_obj_tag(v_p_4280_) == 0)
{
v_y_4221_ = v_v_4279_;
v___y_4222_ = v_a_4200_;
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
goto v___jp_4220_;
}
else
{
goto v___jp_4212_;
}
}
}
else
{
goto v___jp_4212_;
}
}
v___jp_4220_:
{
lean_object* v___x_4233_; 
v___x_4233_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_v_4218_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v_a_4234_; lean_object* v___x_4235_; 
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_a_4234_);
lean_dec_ref(v___x_4233_);
v___x_4235_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; lean_object* v___x_4237_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
lean_inc(v_a_4236_);
lean_dec_ref(v___x_4235_);
v___x_4237_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_4234_, v_a_4236_, v___y_4223_);
lean_dec(v_a_4236_);
lean_dec(v_a_4234_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4253_; 
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4240_ = v___x_4237_;
v_isShared_4241_ = v_isSharedCheck_4253_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4237_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4253_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
uint8_t v___x_4242_; 
v___x_4242_ = lean_unbox(v_a_4238_);
lean_dec(v_a_4238_);
if (v___x_4242_ == 0)
{
uint8_t v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4246_; 
v___x_4243_ = 1;
v___x_4244_ = lean_box(v___x_4243_);
if (v_isShared_4241_ == 0)
{
lean_ctor_set(v___x_4240_, 0, v___x_4244_);
v___x_4246_ = v___x_4240_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v___x_4244_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
else
{
uint8_t v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4251_; 
v___x_4248_ = 0;
v___x_4249_ = lean_box(v___x_4248_);
if (v_isShared_4241_ == 0)
{
lean_ctor_set(v___x_4240_, 0, v___x_4249_);
v___x_4251_ = v___x_4240_;
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
}
}
else
{
return v___x_4237_;
}
}
else
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4261_; 
lean_dec(v_a_4234_);
v_a_4254_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4256_ = v___x_4235_;
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4235_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4259_; 
if (v_isShared_4257_ == 0)
{
v___x_4259_ = v___x_4256_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_a_4254_);
v___x_4259_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
return v___x_4259_;
}
}
}
}
else
{
lean_object* v_a_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4269_; 
v_a_4262_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4264_ = v___x_4233_;
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_a_4262_);
lean_dec(v___x_4233_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4267_; 
if (v_isShared_4265_ == 0)
{
v___x_4267_ = v___x_4264_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_a_4262_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
}
}
}
else
{
goto v___jp_4212_;
}
v___jp_4212_:
{
uint8_t v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4213_ = 0;
v___x_4214_ = lean_box(v___x_4213_);
v___x_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4214_);
return v___x_4215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq___boxed(lean_object* v_c_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_){
_start:
{
lean_object* v_res_4295_; 
v_res_4295_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v_c_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_);
lean_dec(v_a_4293_);
lean_dec_ref(v_a_4292_);
lean_dec(v_a_4291_);
lean_dec_ref(v_a_4290_);
lean_dec(v_a_4289_);
lean_dec_ref(v_a_4288_);
lean_dec(v_a_4287_);
lean_dec_ref(v_a_4286_);
lean_dec(v_a_4285_);
lean_dec(v_a_4284_);
lean_dec(v_a_4283_);
lean_dec_ref(v_c_4282_);
return v_res_4295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(lean_object* v_c_4296_){
_start:
{
lean_object* v_p_4298_; 
v_p_4298_ = lean_ctor_get(v_c_4296_, 0);
if (lean_obj_tag(v_p_4298_) == 1)
{
lean_object* v_k_4299_; lean_object* v___x_4300_; uint8_t v___x_4301_; 
v_k_4299_ = lean_ctor_get(v_p_4298_, 0);
v___x_4300_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_4301_ = lean_int_dec_lt(v_k_4299_, v___x_4300_);
if (v___x_4301_ == 0)
{
lean_object* v___x_4302_; 
v___x_4302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4302_, 0, v_c_4296_);
return v___x_4302_;
}
else
{
lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v___x_4303_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_4298_);
v___x_4304_ = l_Lean_Grind_Linarith_Poly_mul(v_p_4298_, v___x_4303_);
v___x_4305_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4305_, 0, v_c_4296_);
v___x_4306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4304_);
lean_ctor_set(v___x_4306_, 1, v___x_4305_);
v___x_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4306_);
return v___x_4307_;
}
}
else
{
lean_object* v___x_4308_; 
v___x_4308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4308_, 0, v_c_4296_);
return v___x_4308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg___boxed(lean_object* v_c_4309_, lean_object* v_a_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4309_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(lean_object* v_c_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_){
_start:
{
lean_object* v___x_4325_; 
v___x_4325_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4312_);
return v___x_4325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___boxed(lean_object* v_c_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(v_c_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_, v_a_4337_);
lean_dec(v_a_4337_);
lean_dec_ref(v_a_4336_);
lean_dec(v_a_4335_);
lean_dec_ref(v_a_4334_);
lean_dec(v_a_4333_);
lean_dec_ref(v_a_4332_);
lean_dec(v_a_4331_);
lean_dec_ref(v_a_4330_);
lean_dec(v_a_4329_);
lean_dec(v_a_4328_);
lean_dec(v_a_4327_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(lean_object* v___y_4340_, lean_object* v_snd_4341_, lean_object* v_fst_4342_, lean_object* v_s_4343_){
_start:
{
lean_object* v_structs_4344_; lean_object* v_typeIdOf_4345_; lean_object* v_exprToStructId_4346_; lean_object* v_exprToStructIdEntries_4347_; lean_object* v_forbiddenNatModules_4348_; lean_object* v_natStructs_4349_; lean_object* v_natTypeIdOf_4350_; lean_object* v_exprToNatStructId_4351_; lean_object* v___x_4352_; uint8_t v___x_4353_; 
v_structs_4344_ = lean_ctor_get(v_s_4343_, 0);
v_typeIdOf_4345_ = lean_ctor_get(v_s_4343_, 1);
v_exprToStructId_4346_ = lean_ctor_get(v_s_4343_, 2);
v_exprToStructIdEntries_4347_ = lean_ctor_get(v_s_4343_, 3);
v_forbiddenNatModules_4348_ = lean_ctor_get(v_s_4343_, 4);
v_natStructs_4349_ = lean_ctor_get(v_s_4343_, 5);
v_natTypeIdOf_4350_ = lean_ctor_get(v_s_4343_, 6);
v_exprToNatStructId_4351_ = lean_ctor_get(v_s_4343_, 7);
v___x_4352_ = lean_array_get_size(v_structs_4344_);
v___x_4353_ = lean_nat_dec_lt(v___y_4340_, v___x_4352_);
if (v___x_4353_ == 0)
{
lean_dec(v_fst_4342_);
lean_dec_ref(v_snd_4341_);
return v_s_4343_;
}
else
{
lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4417_; 
lean_inc_ref(v_exprToNatStructId_4351_);
lean_inc_ref(v_natTypeIdOf_4350_);
lean_inc_ref(v_natStructs_4349_);
lean_inc_ref(v_forbiddenNatModules_4348_);
lean_inc_ref(v_exprToStructIdEntries_4347_);
lean_inc_ref(v_exprToStructId_4346_);
lean_inc_ref(v_typeIdOf_4345_);
lean_inc_ref(v_structs_4344_);
v_isSharedCheck_4417_ = !lean_is_exclusive(v_s_4343_);
if (v_isSharedCheck_4417_ == 0)
{
lean_object* v_unused_4418_; lean_object* v_unused_4419_; lean_object* v_unused_4420_; lean_object* v_unused_4421_; lean_object* v_unused_4422_; lean_object* v_unused_4423_; lean_object* v_unused_4424_; lean_object* v_unused_4425_; 
v_unused_4418_ = lean_ctor_get(v_s_4343_, 7);
lean_dec(v_unused_4418_);
v_unused_4419_ = lean_ctor_get(v_s_4343_, 6);
lean_dec(v_unused_4419_);
v_unused_4420_ = lean_ctor_get(v_s_4343_, 5);
lean_dec(v_unused_4420_);
v_unused_4421_ = lean_ctor_get(v_s_4343_, 4);
lean_dec(v_unused_4421_);
v_unused_4422_ = lean_ctor_get(v_s_4343_, 3);
lean_dec(v_unused_4422_);
v_unused_4423_ = lean_ctor_get(v_s_4343_, 2);
lean_dec(v_unused_4423_);
v_unused_4424_ = lean_ctor_get(v_s_4343_, 1);
lean_dec(v_unused_4424_);
v_unused_4425_ = lean_ctor_get(v_s_4343_, 0);
lean_dec(v_unused_4425_);
v___x_4355_ = v_s_4343_;
v_isShared_4356_ = v_isSharedCheck_4417_;
goto v_resetjp_4354_;
}
else
{
lean_dec(v_s_4343_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4417_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v_v_4357_; lean_object* v_id_4358_; lean_object* v_ringId_x3f_4359_; lean_object* v_type_4360_; lean_object* v_u_4361_; lean_object* v_intModuleInst_4362_; lean_object* v_leInst_x3f_4363_; lean_object* v_ltInst_x3f_4364_; lean_object* v_lawfulOrderLTInst_x3f_4365_; lean_object* v_isPreorderInst_x3f_4366_; lean_object* v_orderedAddInst_x3f_4367_; lean_object* v_isLinearInst_x3f_4368_; lean_object* v_noNatDivInst_x3f_4369_; lean_object* v_ringInst_x3f_4370_; lean_object* v_commRingInst_x3f_4371_; lean_object* v_orderedRingInst_x3f_4372_; lean_object* v_fieldInst_x3f_4373_; lean_object* v_charInst_x3f_4374_; lean_object* v_zero_4375_; lean_object* v_ofNatZero_4376_; lean_object* v_one_x3f_4377_; lean_object* v_leFn_x3f_4378_; lean_object* v_ltFn_x3f_4379_; lean_object* v_addFn_4380_; lean_object* v_zsmulFn_4381_; lean_object* v_nsmulFn_4382_; lean_object* v_zsmulFn_x3f_4383_; lean_object* v_nsmulFn_x3f_4384_; lean_object* v_homomulFn_x3f_4385_; lean_object* v_subFn_4386_; lean_object* v_negFn_4387_; lean_object* v_vars_4388_; lean_object* v_varMap_4389_; lean_object* v_lowers_4390_; lean_object* v_uppers_4391_; lean_object* v_diseqs_4392_; lean_object* v_assignment_4393_; uint8_t v_caseSplits_4394_; lean_object* v_conflict_x3f_4395_; lean_object* v_diseqSplits_4396_; lean_object* v_elimEqs_4397_; lean_object* v_elimStack_4398_; lean_object* v_occurs_4399_; lean_object* v_ignored_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4416_; 
v_v_4357_ = lean_array_fget(v_structs_4344_, v___y_4340_);
v_id_4358_ = lean_ctor_get(v_v_4357_, 0);
v_ringId_x3f_4359_ = lean_ctor_get(v_v_4357_, 1);
v_type_4360_ = lean_ctor_get(v_v_4357_, 2);
v_u_4361_ = lean_ctor_get(v_v_4357_, 3);
v_intModuleInst_4362_ = lean_ctor_get(v_v_4357_, 4);
v_leInst_x3f_4363_ = lean_ctor_get(v_v_4357_, 5);
v_ltInst_x3f_4364_ = lean_ctor_get(v_v_4357_, 6);
v_lawfulOrderLTInst_x3f_4365_ = lean_ctor_get(v_v_4357_, 7);
v_isPreorderInst_x3f_4366_ = lean_ctor_get(v_v_4357_, 8);
v_orderedAddInst_x3f_4367_ = lean_ctor_get(v_v_4357_, 9);
v_isLinearInst_x3f_4368_ = lean_ctor_get(v_v_4357_, 10);
v_noNatDivInst_x3f_4369_ = lean_ctor_get(v_v_4357_, 11);
v_ringInst_x3f_4370_ = lean_ctor_get(v_v_4357_, 12);
v_commRingInst_x3f_4371_ = lean_ctor_get(v_v_4357_, 13);
v_orderedRingInst_x3f_4372_ = lean_ctor_get(v_v_4357_, 14);
v_fieldInst_x3f_4373_ = lean_ctor_get(v_v_4357_, 15);
v_charInst_x3f_4374_ = lean_ctor_get(v_v_4357_, 16);
v_zero_4375_ = lean_ctor_get(v_v_4357_, 17);
v_ofNatZero_4376_ = lean_ctor_get(v_v_4357_, 18);
v_one_x3f_4377_ = lean_ctor_get(v_v_4357_, 19);
v_leFn_x3f_4378_ = lean_ctor_get(v_v_4357_, 20);
v_ltFn_x3f_4379_ = lean_ctor_get(v_v_4357_, 21);
v_addFn_4380_ = lean_ctor_get(v_v_4357_, 22);
v_zsmulFn_4381_ = lean_ctor_get(v_v_4357_, 23);
v_nsmulFn_4382_ = lean_ctor_get(v_v_4357_, 24);
v_zsmulFn_x3f_4383_ = lean_ctor_get(v_v_4357_, 25);
v_nsmulFn_x3f_4384_ = lean_ctor_get(v_v_4357_, 26);
v_homomulFn_x3f_4385_ = lean_ctor_get(v_v_4357_, 27);
v_subFn_4386_ = lean_ctor_get(v_v_4357_, 28);
v_negFn_4387_ = lean_ctor_get(v_v_4357_, 29);
v_vars_4388_ = lean_ctor_get(v_v_4357_, 30);
v_varMap_4389_ = lean_ctor_get(v_v_4357_, 31);
v_lowers_4390_ = lean_ctor_get(v_v_4357_, 32);
v_uppers_4391_ = lean_ctor_get(v_v_4357_, 33);
v_diseqs_4392_ = lean_ctor_get(v_v_4357_, 34);
v_assignment_4393_ = lean_ctor_get(v_v_4357_, 35);
v_caseSplits_4394_ = lean_ctor_get_uint8(v_v_4357_, sizeof(void*)*42);
v_conflict_x3f_4395_ = lean_ctor_get(v_v_4357_, 36);
v_diseqSplits_4396_ = lean_ctor_get(v_v_4357_, 37);
v_elimEqs_4397_ = lean_ctor_get(v_v_4357_, 38);
v_elimStack_4398_ = lean_ctor_get(v_v_4357_, 39);
v_occurs_4399_ = lean_ctor_get(v_v_4357_, 40);
v_ignored_4400_ = lean_ctor_get(v_v_4357_, 41);
v_isSharedCheck_4416_ = !lean_is_exclusive(v_v_4357_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4402_ = v_v_4357_;
v_isShared_4403_ = v_isSharedCheck_4416_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_ignored_4400_);
lean_inc(v_occurs_4399_);
lean_inc(v_elimStack_4398_);
lean_inc(v_elimEqs_4397_);
lean_inc(v_diseqSplits_4396_);
lean_inc(v_conflict_x3f_4395_);
lean_inc(v_assignment_4393_);
lean_inc(v_diseqs_4392_);
lean_inc(v_uppers_4391_);
lean_inc(v_lowers_4390_);
lean_inc(v_varMap_4389_);
lean_inc(v_vars_4388_);
lean_inc(v_negFn_4387_);
lean_inc(v_subFn_4386_);
lean_inc(v_homomulFn_x3f_4385_);
lean_inc(v_nsmulFn_x3f_4384_);
lean_inc(v_zsmulFn_x3f_4383_);
lean_inc(v_nsmulFn_4382_);
lean_inc(v_zsmulFn_4381_);
lean_inc(v_addFn_4380_);
lean_inc(v_ltFn_x3f_4379_);
lean_inc(v_leFn_x3f_4378_);
lean_inc(v_one_x3f_4377_);
lean_inc(v_ofNatZero_4376_);
lean_inc(v_zero_4375_);
lean_inc(v_charInst_x3f_4374_);
lean_inc(v_fieldInst_x3f_4373_);
lean_inc(v_orderedRingInst_x3f_4372_);
lean_inc(v_commRingInst_x3f_4371_);
lean_inc(v_ringInst_x3f_4370_);
lean_inc(v_noNatDivInst_x3f_4369_);
lean_inc(v_isLinearInst_x3f_4368_);
lean_inc(v_orderedAddInst_x3f_4367_);
lean_inc(v_isPreorderInst_x3f_4366_);
lean_inc(v_lawfulOrderLTInst_x3f_4365_);
lean_inc(v_ltInst_x3f_4364_);
lean_inc(v_leInst_x3f_4363_);
lean_inc(v_intModuleInst_4362_);
lean_inc(v_u_4361_);
lean_inc(v_type_4360_);
lean_inc(v_ringId_x3f_4359_);
lean_inc(v_id_4358_);
lean_dec(v_v_4357_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4416_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4404_; lean_object* v_xs_x27_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4410_; 
v___x_4404_ = lean_box(0);
v_xs_x27_4405_ = lean_array_fset(v_structs_4344_, v___y_4340_, v___x_4404_);
v___x_4406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4406_, 0, v_snd_4341_);
v___x_4407_ = l_Lean_PersistentArray_set___redArg(v_elimEqs_4397_, v_fst_4342_, v___x_4406_);
v___x_4408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4408_, 0, v_fst_4342_);
lean_ctor_set(v___x_4408_, 1, v_elimStack_4398_);
if (v_isShared_4403_ == 0)
{
lean_ctor_set(v___x_4402_, 39, v___x_4408_);
lean_ctor_set(v___x_4402_, 38, v___x_4407_);
v___x_4410_ = v___x_4402_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_id_4358_);
lean_ctor_set(v_reuseFailAlloc_4415_, 1, v_ringId_x3f_4359_);
lean_ctor_set(v_reuseFailAlloc_4415_, 2, v_type_4360_);
lean_ctor_set(v_reuseFailAlloc_4415_, 3, v_u_4361_);
lean_ctor_set(v_reuseFailAlloc_4415_, 4, v_intModuleInst_4362_);
lean_ctor_set(v_reuseFailAlloc_4415_, 5, v_leInst_x3f_4363_);
lean_ctor_set(v_reuseFailAlloc_4415_, 6, v_ltInst_x3f_4364_);
lean_ctor_set(v_reuseFailAlloc_4415_, 7, v_lawfulOrderLTInst_x3f_4365_);
lean_ctor_set(v_reuseFailAlloc_4415_, 8, v_isPreorderInst_x3f_4366_);
lean_ctor_set(v_reuseFailAlloc_4415_, 9, v_orderedAddInst_x3f_4367_);
lean_ctor_set(v_reuseFailAlloc_4415_, 10, v_isLinearInst_x3f_4368_);
lean_ctor_set(v_reuseFailAlloc_4415_, 11, v_noNatDivInst_x3f_4369_);
lean_ctor_set(v_reuseFailAlloc_4415_, 12, v_ringInst_x3f_4370_);
lean_ctor_set(v_reuseFailAlloc_4415_, 13, v_commRingInst_x3f_4371_);
lean_ctor_set(v_reuseFailAlloc_4415_, 14, v_orderedRingInst_x3f_4372_);
lean_ctor_set(v_reuseFailAlloc_4415_, 15, v_fieldInst_x3f_4373_);
lean_ctor_set(v_reuseFailAlloc_4415_, 16, v_charInst_x3f_4374_);
lean_ctor_set(v_reuseFailAlloc_4415_, 17, v_zero_4375_);
lean_ctor_set(v_reuseFailAlloc_4415_, 18, v_ofNatZero_4376_);
lean_ctor_set(v_reuseFailAlloc_4415_, 19, v_one_x3f_4377_);
lean_ctor_set(v_reuseFailAlloc_4415_, 20, v_leFn_x3f_4378_);
lean_ctor_set(v_reuseFailAlloc_4415_, 21, v_ltFn_x3f_4379_);
lean_ctor_set(v_reuseFailAlloc_4415_, 22, v_addFn_4380_);
lean_ctor_set(v_reuseFailAlloc_4415_, 23, v_zsmulFn_4381_);
lean_ctor_set(v_reuseFailAlloc_4415_, 24, v_nsmulFn_4382_);
lean_ctor_set(v_reuseFailAlloc_4415_, 25, v_zsmulFn_x3f_4383_);
lean_ctor_set(v_reuseFailAlloc_4415_, 26, v_nsmulFn_x3f_4384_);
lean_ctor_set(v_reuseFailAlloc_4415_, 27, v_homomulFn_x3f_4385_);
lean_ctor_set(v_reuseFailAlloc_4415_, 28, v_subFn_4386_);
lean_ctor_set(v_reuseFailAlloc_4415_, 29, v_negFn_4387_);
lean_ctor_set(v_reuseFailAlloc_4415_, 30, v_vars_4388_);
lean_ctor_set(v_reuseFailAlloc_4415_, 31, v_varMap_4389_);
lean_ctor_set(v_reuseFailAlloc_4415_, 32, v_lowers_4390_);
lean_ctor_set(v_reuseFailAlloc_4415_, 33, v_uppers_4391_);
lean_ctor_set(v_reuseFailAlloc_4415_, 34, v_diseqs_4392_);
lean_ctor_set(v_reuseFailAlloc_4415_, 35, v_assignment_4393_);
lean_ctor_set(v_reuseFailAlloc_4415_, 36, v_conflict_x3f_4395_);
lean_ctor_set(v_reuseFailAlloc_4415_, 37, v_diseqSplits_4396_);
lean_ctor_set(v_reuseFailAlloc_4415_, 38, v___x_4407_);
lean_ctor_set(v_reuseFailAlloc_4415_, 39, v___x_4408_);
lean_ctor_set(v_reuseFailAlloc_4415_, 40, v_occurs_4399_);
lean_ctor_set(v_reuseFailAlloc_4415_, 41, v_ignored_4400_);
lean_ctor_set_uint8(v_reuseFailAlloc_4415_, sizeof(void*)*42, v_caseSplits_4394_);
v___x_4410_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
lean_object* v___x_4411_; lean_object* v___x_4413_; 
v___x_4411_ = lean_array_fset(v_xs_x27_4405_, v___y_4340_, v___x_4410_);
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 0, v___x_4411_);
v___x_4413_ = v___x_4355_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v___x_4411_);
lean_ctor_set(v_reuseFailAlloc_4414_, 1, v_typeIdOf_4345_);
lean_ctor_set(v_reuseFailAlloc_4414_, 2, v_exprToStructId_4346_);
lean_ctor_set(v_reuseFailAlloc_4414_, 3, v_exprToStructIdEntries_4347_);
lean_ctor_set(v_reuseFailAlloc_4414_, 4, v_forbiddenNatModules_4348_);
lean_ctor_set(v_reuseFailAlloc_4414_, 5, v_natStructs_4349_);
lean_ctor_set(v_reuseFailAlloc_4414_, 6, v_natTypeIdOf_4350_);
lean_ctor_set(v_reuseFailAlloc_4414_, 7, v_exprToNatStructId_4351_);
v___x_4413_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
return v___x_4413_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed(lean_object* v___y_4426_, lean_object* v_snd_4427_, lean_object* v_fst_4428_, lean_object* v_s_4429_){
_start:
{
lean_object* v_res_4430_; 
v_res_4430_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(v___y_4426_, v_snd_4427_, v_fst_4428_, v_s_4429_);
lean_dec(v___y_4426_);
return v_res_4430_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1(void){
_start:
{
lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___x_4432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0));
v___x_4433_ = l_Lean_stringToMessageData(v___x_4432_);
return v___x_4433_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4(void){
_start:
{
lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
v___x_4439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4440_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4441_ = l_Lean_Name_append(v___x_4440_, v___x_4439_);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object* v_c_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_){
_start:
{
lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4492_; lean_object* v___y_4493_; lean_object* v___y_4494_; lean_object* v___y_4495_; lean_object* v_options_4521_; lean_object* v_inheritedTraceOptions_4522_; uint8_t v_hasTrace_4523_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v_options_4540_; lean_object* v_inheritedTraceOptions_4541_; lean_object* v___y_4542_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; lean_object* v___y_4568_; lean_object* v___y_4569_; 
v_options_4521_ = lean_ctor_get(v_a_4452_, 2);
v_inheritedTraceOptions_4522_ = lean_ctor_get(v_a_4452_, 13);
v_hasTrace_4523_ = lean_ctor_get_uint8(v_options_4521_, sizeof(void*)*1);
if (v_hasTrace_4523_ == 0)
{
v___y_4559_ = v_a_4443_;
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
goto v___jp_4558_;
}
else
{
lean_object* v_cls_4665_; lean_object* v___x_4666_; uint8_t v___x_4667_; 
v_cls_4665_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_4666_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_4667_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4522_, v_options_4521_, v___x_4666_);
if (v___x_4667_ == 0)
{
v___y_4559_ = v_a_4443_;
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
goto v___jp_4558_;
}
else
{
lean_object* v___x_4668_; 
v___x_4668_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_4442_, v_a_4443_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_object* v_a_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; 
v_a_4669_ = lean_ctor_get(v___x_4668_, 0);
lean_inc(v_a_4669_);
lean_dec_ref(v___x_4668_);
v___x_4670_ = l_Lean_MessageData_ofExpr(v_a_4669_);
v___x_4671_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4665_, v___x_4670_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_dec_ref(v___x_4671_);
v___y_4559_ = v_a_4443_;
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
goto v___jp_4558_;
}
else
{
lean_dec_ref(v_c_4442_);
return v___x_4671_;
}
}
else
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4679_; 
lean_dec_ref(v_c_4442_);
v_a_4672_ = lean_ctor_get(v___x_4668_, 0);
v_isSharedCheck_4679_ = !lean_is_exclusive(v___x_4668_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4674_ = v___x_4668_;
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4668_);
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
}
v___jp_4455_:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4456_ = lean_box(0);
v___x_4457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4457_, 0, v___x_4456_);
return v___x_4457_;
}
v___jp_4458_:
{
lean_object* v___f_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
lean_inc(v___y_4464_);
v___f_4475_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4475_, 0, v___y_4464_);
lean_closure_set(v___f_4475_, 1, v___y_4459_);
lean_closure_set(v___f_4475_, 2, v___y_4460_);
v___x_4476_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4477_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4476_, v___f_4475_, v___y_4465_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v___x_4478_; 
lean_dec_ref(v___x_4477_);
v___x_4478_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v___y_4463_, v___y_4462_, v___y_4461_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_);
return v___x_4478_;
}
else
{
lean_dec(v___y_4463_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
return v___x_4477_;
}
}
v___jp_4479_:
{
lean_object* v___x_4496_; 
v___x_4496_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_);
if (lean_obj_tag(v___x_4496_) == 0)
{
lean_object* v_a_4497_; uint8_t v_caseSplits_4498_; 
v_a_4497_ = lean_ctor_get(v___x_4496_, 0);
lean_inc(v_a_4497_);
lean_dec_ref(v___x_4496_);
v_caseSplits_4498_ = lean_ctor_get_uint8(v_a_4497_, sizeof(void*)*42);
lean_dec(v_a_4497_);
if (v_caseSplits_4498_ == 0)
{
lean_object* v___x_4499_; 
v___x_4499_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v___y_4482_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_);
if (lean_obj_tag(v___x_4499_) == 0)
{
lean_object* v_a_4500_; uint8_t v___x_4501_; 
v_a_4500_ = lean_ctor_get(v___x_4499_, 0);
lean_inc(v_a_4500_);
lean_dec_ref(v___x_4499_);
v___x_4501_ = lean_unbox(v_a_4500_);
lean_dec(v_a_4500_);
if (v___x_4501_ == 0)
{
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
v___y_4469_ = v___y_4490_;
v___y_4470_ = v___y_4491_;
v___y_4471_ = v___y_4492_;
v___y_4472_ = v___y_4493_;
v___y_4473_ = v___y_4494_;
v___y_4474_ = v___y_4495_;
goto v___jp_4458_;
}
else
{
lean_object* v___x_4502_; lean_object* v_a_4503_; lean_object* v___x_4504_; 
lean_inc_ref(v___y_4482_);
v___x_4502_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v___y_4482_);
v_a_4503_ = lean_ctor_get(v___x_4502_, 0);
lean_inc(v_a_4503_);
lean_dec_ref(v___x_4502_);
v___x_4504_ = l_Lean_Meta_Grind_Arith_Linear_propagateImpEq(v_a_4503_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_);
if (lean_obj_tag(v___x_4504_) == 0)
{
lean_dec_ref(v___x_4504_);
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
v___y_4469_ = v___y_4490_;
v___y_4470_ = v___y_4491_;
v___y_4471_ = v___y_4492_;
v___y_4472_ = v___y_4493_;
v___y_4473_ = v___y_4494_;
v___y_4474_ = v___y_4495_;
goto v___jp_4458_;
}
else
{
lean_dec(v___y_4484_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
return v___x_4504_;
}
}
}
else
{
lean_object* v_a_4505_; lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4512_; 
lean_dec(v___y_4484_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
v_a_4505_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4507_ = v___x_4499_;
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
else
{
lean_inc(v_a_4505_);
lean_dec(v___x_4499_);
v___x_4507_ = lean_box(0);
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
v_resetjp_4506_:
{
lean_object* v___x_4510_; 
if (v_isShared_4508_ == 0)
{
v___x_4510_ = v___x_4507_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4505_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
return v___x_4510_;
}
}
}
}
else
{
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
v___y_4469_ = v___y_4490_;
v___y_4470_ = v___y_4491_;
v___y_4471_ = v___y_4492_;
v___y_4472_ = v___y_4493_;
v___y_4473_ = v___y_4494_;
v___y_4474_ = v___y_4495_;
goto v___jp_4458_;
}
}
else
{
lean_object* v_a_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4520_; 
lean_dec(v___y_4484_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
v_a_4513_ = lean_ctor_get(v___x_4496_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4515_ = v___x_4496_;
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_a_4513_);
lean_dec(v___x_4496_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4518_; 
if (v_isShared_4516_ == 0)
{
v___x_4518_ = v___x_4515_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4513_);
v___x_4518_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
return v___x_4518_;
}
}
}
}
v___jp_4524_:
{
lean_object* v___x_4543_; lean_object* v___x_4544_; uint8_t v___x_4545_; 
v___x_4543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_4544_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_4545_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4541_, v_options_4540_, v___x_4544_);
if (v___x_4545_ == 0)
{
v___y_4480_ = v___y_4525_;
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
v___y_4495_ = v___y_4542_;
goto v___jp_4479_;
}
else
{
lean_object* v___x_4546_; 
v___x_4546_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v___y_4527_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4542_);
if (lean_obj_tag(v___x_4546_) == 0)
{
lean_object* v_a_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
v_a_4547_ = lean_ctor_get(v___x_4546_, 0);
lean_inc(v_a_4547_);
lean_dec_ref(v___x_4546_);
v___x_4548_ = l_Lean_MessageData_ofExpr(v_a_4547_);
v___x_4549_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4543_, v___x_4548_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4542_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_dec_ref(v___x_4549_);
v___y_4480_ = v___y_4525_;
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
v___y_4495_ = v___y_4542_;
goto v___jp_4479_;
}
else
{
lean_dec(v___y_4529_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
return v___x_4549_;
}
}
else
{
lean_object* v_a_4550_; lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4557_; 
lean_dec(v___y_4529_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
v_a_4550_ = lean_ctor_get(v___x_4546_, 0);
v_isSharedCheck_4557_ = !lean_is_exclusive(v___x_4546_);
if (v_isSharedCheck_4557_ == 0)
{
v___x_4552_ = v___x_4546_;
v_isShared_4553_ = v_isSharedCheck_4557_;
goto v_resetjp_4551_;
}
else
{
lean_inc(v_a_4550_);
lean_dec(v___x_4546_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4557_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
lean_object* v___x_4555_; 
if (v_isShared_4553_ == 0)
{
v___x_4555_ = v___x_4552_;
goto v_reusejp_4554_;
}
else
{
lean_object* v_reuseFailAlloc_4556_; 
v_reuseFailAlloc_4556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4556_, 0, v_a_4550_);
v___x_4555_ = v_reuseFailAlloc_4556_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
return v___x_4555_;
}
}
}
}
}
v___jp_4558_:
{
lean_object* v___x_4570_; 
lean_inc_ref(v___y_4568_);
v___x_4570_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_4442_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
if (lean_obj_tag(v___x_4570_) == 0)
{
lean_object* v_a_4571_; lean_object* v_p_4572_; lean_object* v___x_4573_; uint8_t v___x_4574_; 
v_a_4571_ = lean_ctor_get(v___x_4570_, 0);
lean_inc(v_a_4571_);
lean_dec_ref(v___x_4570_);
v_p_4572_ = lean_ctor_get(v_a_4571_, 0);
v___x_4573_ = lean_box(0);
v___x_4574_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_4572_, v___x_4573_);
if (v___x_4574_ == 0)
{
lean_object* v___x_4575_; 
v___x_4575_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_a_4571_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
if (lean_obj_tag(v___x_4575_) == 0)
{
lean_object* v_a_4576_; lean_object* v_snd_4577_; lean_object* v_options_4578_; uint8_t v_hasTrace_4579_; 
v_a_4576_ = lean_ctor_get(v___x_4575_, 0);
lean_inc(v_a_4576_);
lean_dec_ref(v___x_4575_);
v_snd_4577_ = lean_ctor_get(v_a_4576_, 1);
lean_inc(v_snd_4577_);
v_options_4578_ = lean_ctor_get(v___y_4568_, 2);
v_hasTrace_4579_ = lean_ctor_get_uint8(v_options_4578_, sizeof(void*)*1);
if (v_hasTrace_4579_ == 0)
{
lean_object* v_fst_4580_; lean_object* v_fst_4581_; lean_object* v_snd_4582_; 
v_fst_4580_ = lean_ctor_get(v_a_4576_, 0);
lean_inc(v_fst_4580_);
lean_dec(v_a_4576_);
v_fst_4581_ = lean_ctor_get(v_snd_4577_, 0);
lean_inc_n(v_fst_4581_, 2);
v_snd_4582_ = lean_ctor_get(v_snd_4577_, 1);
lean_inc_n(v_snd_4582_, 2);
lean_dec(v_snd_4577_);
v___y_4480_ = v_snd_4582_;
v___y_4481_ = v_fst_4581_;
v___y_4482_ = v_snd_4582_;
v___y_4483_ = v_fst_4581_;
v___y_4484_ = v_fst_4580_;
v___y_4485_ = v___y_4559_;
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
goto v___jp_4479_;
}
else
{
lean_object* v_fst_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4629_; 
v_fst_4583_ = lean_ctor_get(v_a_4576_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v_a_4576_);
if (v_isSharedCheck_4629_ == 0)
{
lean_object* v_unused_4630_; 
v_unused_4630_ = lean_ctor_get(v_a_4576_, 1);
lean_dec(v_unused_4630_);
v___x_4585_ = v_a_4576_;
v_isShared_4586_ = v_isSharedCheck_4629_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_fst_4583_);
lean_dec(v_a_4576_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4629_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v_fst_4587_; lean_object* v_snd_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4628_; 
v_fst_4587_ = lean_ctor_get(v_snd_4577_, 0);
v_snd_4588_ = lean_ctor_get(v_snd_4577_, 1);
v_isSharedCheck_4628_ = !lean_is_exclusive(v_snd_4577_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4590_ = v_snd_4577_;
v_isShared_4591_ = v_isSharedCheck_4628_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_snd_4588_);
lean_inc(v_fst_4587_);
lean_dec(v_snd_4577_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4628_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v_inheritedTraceOptions_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; uint8_t v___x_4595_; 
v_inheritedTraceOptions_4592_ = lean_ctor_get(v___y_4568_, 13);
v___x_4593_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_4594_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_4595_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4592_, v_options_4578_, v___x_4594_);
if (v___x_4595_ == 0)
{
lean_del_object(v___x_4590_);
lean_del_object(v___x_4585_);
lean_inc(v_fst_4587_);
lean_inc(v_snd_4588_);
v___y_4525_ = v_snd_4588_;
v___y_4526_ = v_fst_4587_;
v___y_4527_ = v_snd_4588_;
v___y_4528_ = v_fst_4587_;
v___y_4529_ = v_fst_4583_;
v___y_4530_ = v___y_4559_;
v___y_4531_ = v___y_4560_;
v___y_4532_ = v___y_4561_;
v___y_4533_ = v___y_4562_;
v___y_4534_ = v___y_4563_;
v___y_4535_ = v___y_4564_;
v___y_4536_ = v___y_4565_;
v___y_4537_ = v___y_4566_;
v___y_4538_ = v___y_4567_;
v___y_4539_ = v___y_4568_;
v_options_4540_ = v_options_4578_;
v_inheritedTraceOptions_4541_ = v_inheritedTraceOptions_4592_;
v___y_4542_ = v___y_4569_;
goto v___jp_4524_;
}
else
{
lean_object* v___x_4596_; 
v___x_4596_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_4587_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v_a_4597_; lean_object* v___x_4598_; 
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
lean_inc(v_a_4597_);
lean_dec_ref(v___x_4596_);
v___x_4598_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_4588_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4603_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
lean_inc(v_a_4599_);
lean_dec_ref(v___x_4598_);
v___x_4600_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1);
v___x_4601_ = l_Lean_MessageData_ofExpr(v_a_4597_);
if (v_isShared_4591_ == 0)
{
lean_ctor_set_tag(v___x_4590_, 7);
lean_ctor_set(v___x_4590_, 1, v___x_4601_);
lean_ctor_set(v___x_4590_, 0, v___x_4600_);
v___x_4603_ = v___x_4590_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v___x_4600_);
lean_ctor_set(v_reuseFailAlloc_4611_, 1, v___x_4601_);
v___x_4603_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
lean_object* v___x_4604_; lean_object* v___x_4606_; 
v___x_4604_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_4586_ == 0)
{
lean_ctor_set_tag(v___x_4585_, 7);
lean_ctor_set(v___x_4585_, 1, v___x_4604_);
lean_ctor_set(v___x_4585_, 0, v___x_4603_);
v___x_4606_ = v___x_4585_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v___x_4603_);
lean_ctor_set(v_reuseFailAlloc_4610_, 1, v___x_4604_);
v___x_4606_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4607_ = l_Lean_MessageData_ofExpr(v_a_4599_);
v___x_4608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4606_);
lean_ctor_set(v___x_4608_, 1, v___x_4607_);
v___x_4609_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4593_, v___x_4608_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_dec_ref(v___x_4609_);
lean_inc(v_fst_4587_);
lean_inc(v_snd_4588_);
v___y_4525_ = v_snd_4588_;
v___y_4526_ = v_fst_4587_;
v___y_4527_ = v_snd_4588_;
v___y_4528_ = v_fst_4587_;
v___y_4529_ = v_fst_4583_;
v___y_4530_ = v___y_4559_;
v___y_4531_ = v___y_4560_;
v___y_4532_ = v___y_4561_;
v___y_4533_ = v___y_4562_;
v___y_4534_ = v___y_4563_;
v___y_4535_ = v___y_4564_;
v___y_4536_ = v___y_4565_;
v___y_4537_ = v___y_4566_;
v___y_4538_ = v___y_4567_;
v___y_4539_ = v___y_4568_;
v_options_4540_ = v_options_4578_;
v_inheritedTraceOptions_4541_ = v_inheritedTraceOptions_4592_;
v___y_4542_ = v___y_4569_;
goto v___jp_4524_;
}
else
{
lean_dec(v_snd_4588_);
lean_dec(v_fst_4587_);
lean_dec(v_fst_4583_);
return v___x_4609_;
}
}
}
}
else
{
lean_object* v_a_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4619_; 
lean_dec(v_a_4597_);
lean_del_object(v___x_4590_);
lean_dec(v_snd_4588_);
lean_dec(v_fst_4587_);
lean_del_object(v___x_4585_);
lean_dec(v_fst_4583_);
v_a_4612_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4619_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4614_ = v___x_4598_;
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_a_4612_);
lean_dec(v___x_4598_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v___x_4617_; 
if (v_isShared_4615_ == 0)
{
v___x_4617_ = v___x_4614_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v_a_4612_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
}
}
}
}
else
{
lean_object* v_a_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4627_; 
lean_del_object(v___x_4590_);
lean_dec(v_snd_4588_);
lean_dec(v_fst_4587_);
lean_del_object(v___x_4585_);
lean_dec(v_fst_4583_);
v_a_4620_ = lean_ctor_get(v___x_4596_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4622_ = v___x_4596_;
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_a_4620_);
lean_dec(v___x_4596_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___x_4625_; 
if (v_isShared_4623_ == 0)
{
v___x_4625_ = v___x_4622_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v_a_4620_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
return v___x_4625_;
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
lean_object* v_a_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4638_; 
v_a_4631_ = lean_ctor_get(v___x_4575_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4575_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4633_ = v___x_4575_;
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_a_4631_);
lean_dec(v___x_4575_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v___x_4636_; 
if (v_isShared_4634_ == 0)
{
v___x_4636_ = v___x_4633_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_a_4631_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
}
}
else
{
lean_object* v_options_4639_; uint8_t v_hasTrace_4640_; 
v_options_4639_ = lean_ctor_get(v___y_4568_, 2);
v_hasTrace_4640_ = lean_ctor_get_uint8(v_options_4639_, sizeof(void*)*1);
if (v_hasTrace_4640_ == 0)
{
lean_dec(v_a_4571_);
goto v___jp_4455_;
}
else
{
lean_object* v_inheritedTraceOptions_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; uint8_t v___x_4644_; 
v_inheritedTraceOptions_4641_ = lean_ctor_get(v___y_4568_, 13);
v___x_4642_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4643_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4);
v___x_4644_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4641_, v_options_4639_, v___x_4643_);
if (v___x_4644_ == 0)
{
lean_dec(v_a_4571_);
goto v___jp_4455_;
}
else
{
lean_object* v___x_4645_; 
v___x_4645_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_a_4571_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
lean_dec(v_a_4571_);
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_object* v_a_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v_a_4646_ = lean_ctor_get(v___x_4645_, 0);
lean_inc(v_a_4646_);
lean_dec_ref(v___x_4645_);
v___x_4647_ = l_Lean_MessageData_ofExpr(v_a_4646_);
v___x_4648_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4642_, v___x_4647_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
if (lean_obj_tag(v___x_4648_) == 0)
{
lean_dec_ref(v___x_4648_);
goto v___jp_4455_;
}
else
{
return v___x_4648_;
}
}
else
{
lean_object* v_a_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4656_; 
v_a_4649_ = lean_ctor_get(v___x_4645_, 0);
v_isSharedCheck_4656_ = !lean_is_exclusive(v___x_4645_);
if (v_isSharedCheck_4656_ == 0)
{
v___x_4651_ = v___x_4645_;
v_isShared_4652_ = v_isSharedCheck_4656_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_a_4649_);
lean_dec(v___x_4645_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4656_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
lean_object* v___x_4654_; 
if (v_isShared_4652_ == 0)
{
v___x_4654_ = v___x_4651_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4655_; 
v_reuseFailAlloc_4655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4655_, 0, v_a_4649_);
v___x_4654_ = v_reuseFailAlloc_4655_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
return v___x_4654_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4664_; 
v_a_4657_ = lean_ctor_get(v___x_4570_, 0);
v_isSharedCheck_4664_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4664_ == 0)
{
v___x_4659_ = v___x_4570_;
v_isShared_4660_ = v_isSharedCheck_4664_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_a_4657_);
lean_dec(v___x_4570_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4664_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
lean_object* v___x_4662_; 
if (v_isShared_4660_ == 0)
{
v___x_4662_ = v___x_4659_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_a_4657_);
v___x_4662_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
return v___x_4662_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object* v_c_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_){
_start:
{
lean_object* v_res_4693_; 
v_res_4693_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v_c_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_);
lean_dec(v_a_4691_);
lean_dec_ref(v_a_4690_);
lean_dec(v_a_4689_);
lean_dec_ref(v_a_4688_);
lean_dec(v_a_4687_);
lean_dec_ref(v_a_4686_);
lean_dec(v_a_4685_);
lean_dec_ref(v_a_4684_);
lean_dec(v_a_4683_);
lean_dec(v_a_4682_);
lean_dec(v_a_4681_);
return v_res_4693_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2(void){
_start:
{
lean_object* v_cls_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; 
v_cls_4698_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4699_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4700_ = l_Lean_Name_append(v___x_4699_, v_cls_4698_);
return v___x_4700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object* v_a_4701_, lean_object* v_b_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_){
_start:
{
lean_object* v_options_4711_; uint8_t v_hasTrace_4712_; 
v_options_4711_ = lean_ctor_get(v_a_4705_, 2);
v_hasTrace_4712_ = lean_ctor_get_uint8(v_options_4711_, sizeof(void*)*1);
if (v_hasTrace_4712_ == 0)
{
lean_dec_ref(v_b_4702_);
lean_dec_ref(v_a_4701_);
goto v___jp_4708_;
}
else
{
lean_object* v_inheritedTraceOptions_4713_; lean_object* v_cls_4714_; lean_object* v___x_4715_; uint8_t v___x_4716_; 
v_inheritedTraceOptions_4713_ = lean_ctor_get(v_a_4705_, 13);
v_cls_4714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4715_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2);
v___x_4716_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4713_, v_options_4711_, v___x_4715_);
if (v___x_4716_ == 0)
{
lean_dec_ref(v_b_4702_);
lean_dec_ref(v_a_4701_);
goto v___jp_4708_;
}
else
{
lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; 
v___x_4717_ = l_Lean_MessageData_ofExpr(v_a_4701_);
v___x_4718_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_4719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4719_, 0, v___x_4717_);
lean_ctor_set(v___x_4719_, 1, v___x_4718_);
v___x_4720_ = l_Lean_MessageData_ofExpr(v_b_4702_);
v___x_4721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4719_);
lean_ctor_set(v___x_4721_, 1, v___x_4720_);
v___x_4722_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4714_, v___x_4721_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_);
return v___x_4722_;
}
}
v___jp_4708_:
{
lean_object* v___x_4709_; lean_object* v___x_4710_; 
v___x_4709_ = lean_box(0);
v___x_4710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4710_, 0, v___x_4709_);
return v___x_4710_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object* v_a_4723_, lean_object* v_b_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_){
_start:
{
lean_object* v_res_4730_; 
v_res_4730_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4723_, v_b_4724_, v_a_4725_, v_a_4726_, v_a_4727_, v_a_4728_);
lean_dec(v_a_4728_);
lean_dec_ref(v_a_4727_);
lean_dec(v_a_4726_);
lean_dec_ref(v_a_4725_);
return v_res_4730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object* v_a_4731_, lean_object* v_b_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_){
_start:
{
lean_object* v___x_4745_; 
v___x_4745_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4731_, v_b_4732_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_);
return v___x_4745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object* v_a_4746_, lean_object* v_b_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_){
_start:
{
lean_object* v_res_4760_; 
v_res_4760_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(v_a_4746_, v_b_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_);
lean_dec(v_a_4758_);
lean_dec_ref(v_a_4757_);
lean_dec(v_a_4756_);
lean_dec_ref(v_a_4755_);
lean_dec(v_a_4754_);
lean_dec_ref(v_a_4753_);
lean_dec(v_a_4752_);
lean_dec_ref(v_a_4751_);
lean_dec(v_a_4750_);
lean_dec(v_a_4749_);
lean_dec(v_a_4748_);
return v_res_4760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object* v_a_4761_, lean_object* v_b_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_){
_start:
{
lean_object* v___x_4775_; 
v___x_4775_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4761_, v_a_4764_);
if (lean_obj_tag(v___x_4775_) == 0)
{
lean_object* v_a_4776_; uint8_t v___x_4777_; lean_object* v___x_4778_; 
v_a_4776_ = lean_ctor_get(v___x_4775_, 0);
lean_inc(v_a_4776_);
lean_dec_ref(v___x_4775_);
v___x_4777_ = 0;
lean_inc_ref(v_a_4761_);
v___x_4778_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_4761_, v___x_4777_, v_a_4776_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_);
if (lean_obj_tag(v___x_4778_) == 0)
{
lean_object* v_a_4779_; lean_object* v___x_4781_; uint8_t v_isShared_4782_; uint8_t v_isSharedCheck_4828_; 
v_a_4779_ = lean_ctor_get(v___x_4778_, 0);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4778_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4781_ = v___x_4778_;
v_isShared_4782_ = v_isSharedCheck_4828_;
goto v_resetjp_4780_;
}
else
{
lean_inc(v_a_4779_);
lean_dec(v___x_4778_);
v___x_4781_ = lean_box(0);
v_isShared_4782_ = v_isSharedCheck_4828_;
goto v_resetjp_4780_;
}
v_resetjp_4780_:
{
if (lean_obj_tag(v_a_4779_) == 1)
{
lean_object* v_val_4783_; lean_object* v___x_4784_; 
lean_del_object(v___x_4781_);
v_val_4783_ = lean_ctor_get(v_a_4779_, 0);
lean_inc(v_val_4783_);
lean_dec_ref(v_a_4779_);
v___x_4784_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4762_, v_a_4764_);
if (lean_obj_tag(v___x_4784_) == 0)
{
lean_object* v_a_4785_; lean_object* v___x_4786_; 
v_a_4785_ = lean_ctor_get(v___x_4784_, 0);
lean_inc(v_a_4785_);
lean_dec_ref(v___x_4784_);
lean_inc_ref(v_b_4762_);
v___x_4786_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_4762_, v___x_4777_, v_a_4785_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_);
if (lean_obj_tag(v___x_4786_) == 0)
{
lean_object* v_a_4787_; lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4807_; 
v_a_4787_ = lean_ctor_get(v___x_4786_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___x_4786_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4789_ = v___x_4786_;
v_isShared_4790_ = v_isSharedCheck_4807_;
goto v_resetjp_4788_;
}
else
{
lean_inc(v_a_4787_);
lean_dec(v___x_4786_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4807_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
if (lean_obj_tag(v_a_4787_) == 1)
{
lean_object* v_val_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; uint8_t v___x_4795_; 
v_val_4791_ = lean_ctor_get(v_a_4787_, 0);
lean_inc_n(v_val_4791_, 2);
lean_dec_ref(v_a_4787_);
lean_inc(v_val_4783_);
v___x_4792_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4792_, 0, v_val_4783_);
lean_ctor_set(v___x_4792_, 1, v_val_4791_);
v___x_4793_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4792_);
v___x_4794_ = lean_box(0);
v___x_4795_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4793_, v___x_4794_);
if (v___x_4795_ == 0)
{
lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; 
lean_del_object(v___x_4789_);
v___x_4796_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4796_, 0, v_a_4761_);
lean_ctor_set(v___x_4796_, 1, v_b_4762_);
lean_ctor_set(v___x_4796_, 2, v_val_4783_);
lean_ctor_set(v___x_4796_, 3, v_val_4791_);
v___x_4797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4797_, 0, v___x_4793_);
lean_ctor_set(v___x_4797_, 1, v___x_4796_);
v___x_4798_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_4797_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_);
return v___x_4798_;
}
else
{
lean_object* v___x_4799_; lean_object* v___x_4801_; 
lean_dec(v___x_4793_);
lean_dec(v_val_4791_);
lean_dec(v_val_4783_);
lean_dec_ref(v_b_4762_);
lean_dec_ref(v_a_4761_);
v___x_4799_ = lean_box(0);
if (v_isShared_4790_ == 0)
{
lean_ctor_set(v___x_4789_, 0, v___x_4799_);
v___x_4801_ = v___x_4789_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v___x_4799_);
v___x_4801_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
return v___x_4801_;
}
}
}
else
{
lean_object* v___x_4803_; lean_object* v___x_4805_; 
lean_dec(v_a_4787_);
lean_dec(v_val_4783_);
lean_dec_ref(v_b_4762_);
lean_dec_ref(v_a_4761_);
v___x_4803_ = lean_box(0);
if (v_isShared_4790_ == 0)
{
lean_ctor_set(v___x_4789_, 0, v___x_4803_);
v___x_4805_ = v___x_4789_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4803_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
}
}
else
{
lean_object* v_a_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4815_; 
lean_dec(v_val_4783_);
lean_dec_ref(v_b_4762_);
lean_dec_ref(v_a_4761_);
v_a_4808_ = lean_ctor_get(v___x_4786_, 0);
v_isSharedCheck_4815_ = !lean_is_exclusive(v___x_4786_);
if (v_isSharedCheck_4815_ == 0)
{
v___x_4810_ = v___x_4786_;
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_a_4808_);
lean_dec(v___x_4786_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
lean_object* v___x_4813_; 
if (v_isShared_4811_ == 0)
{
v___x_4813_ = v___x_4810_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_a_4808_);
v___x_4813_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
return v___x_4813_;
}
}
}
}
else
{
lean_object* v_a_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4823_; 
lean_dec(v_val_4783_);
lean_dec_ref(v_b_4762_);
lean_dec_ref(v_a_4761_);
v_a_4816_ = lean_ctor_get(v___x_4784_, 0);
v_isSharedCheck_4823_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4818_ = v___x_4784_;
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
else
{
lean_inc(v_a_4816_);
lean_dec(v___x_4784_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v___x_4821_; 
if (v_isShared_4819_ == 0)
{
v___x_4821_ = v___x_4818_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4816_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
}
}
else
{
lean_object* v___x_4824_; lean_object* v___x_4826_; 
lean_dec(v_a_4779_);
lean_dec_ref(v_b_4762_);
lean_dec_ref(v_a_4761_);
v___x_4824_ = lean_box(0);
if (v_isShared_4782_ == 0)
{
lean_ctor_set(v___x_4781_, 0, v___x_4824_);
v___x_4826_ = v___x_4781_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v___x_4824_);
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
lean_object* v_a_4829_; lean_object* v___x_4831_; uint8_t v_isShared_4832_; uint8_t v_isSharedCheck_4836_; 
lean_dec_ref(v_b_4762_);
lean_dec_ref(v_a_4761_);
v_a_4829_ = lean_ctor_get(v___x_4778_, 0);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4778_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4831_ = v___x_4778_;
v_isShared_4832_ = v_isSharedCheck_4836_;
goto v_resetjp_4830_;
}
else
{
lean_inc(v_a_4829_);
lean_dec(v___x_4778_);
v___x_4831_ = lean_box(0);
v_isShared_4832_ = v_isSharedCheck_4836_;
goto v_resetjp_4830_;
}
v_resetjp_4830_:
{
lean_object* v___x_4834_; 
if (v_isShared_4832_ == 0)
{
v___x_4834_ = v___x_4831_;
goto v_reusejp_4833_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_a_4829_);
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
lean_dec_ref(v_b_4762_);
lean_dec_ref(v_a_4761_);
v_a_4837_ = lean_ctor_get(v___x_4775_, 0);
v_isSharedCheck_4844_ = !lean_is_exclusive(v___x_4775_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4839_ = v___x_4775_;
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
else
{
lean_inc(v_a_4837_);
lean_dec(v___x_4775_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___boxed(lean_object* v_a_4845_, lean_object* v_b_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_4845_, v_b_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_);
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
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(lean_object* v_a_4860_, lean_object* v_b_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_){
_start:
{
lean_object* v___x_4874_; 
v___x_4874_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_);
if (lean_obj_tag(v___x_4874_) == 0)
{
lean_object* v_a_4875_; lean_object* v___x_4876_; 
v_a_4875_ = lean_ctor_get(v___x_4874_, 0);
lean_inc(v_a_4875_);
lean_dec_ref(v___x_4874_);
lean_inc_ref(v_a_4860_);
v___x_4876_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_4860_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_);
if (lean_obj_tag(v___x_4876_) == 0)
{
lean_object* v_a_4877_; lean_object* v_fst_4878_; lean_object* v___x_4879_; 
v_a_4877_ = lean_ctor_get(v___x_4876_, 0);
lean_inc(v_a_4877_);
lean_dec_ref(v___x_4876_);
v_fst_4878_ = lean_ctor_get(v_a_4877_, 0);
lean_inc(v_fst_4878_);
lean_dec(v_a_4877_);
lean_inc_ref(v_b_4861_);
v___x_4879_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_);
if (lean_obj_tag(v___x_4879_) == 0)
{
lean_object* v_a_4880_; lean_object* v_fst_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4964_; 
v_a_4880_ = lean_ctor_get(v___x_4879_, 0);
lean_inc(v_a_4880_);
lean_dec_ref(v___x_4879_);
v_fst_4881_ = lean_ctor_get(v_a_4880_, 0);
v_isSharedCheck_4964_ = !lean_is_exclusive(v_a_4880_);
if (v_isSharedCheck_4964_ == 0)
{
lean_object* v_unused_4965_; 
v_unused_4965_ = lean_ctor_get(v_a_4880_, 1);
lean_dec(v_unused_4965_);
v___x_4883_ = v_a_4880_;
v_isShared_4884_ = v_isSharedCheck_4964_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_fst_4881_);
lean_dec(v_a_4880_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4964_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v___x_4885_; 
v___x_4885_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4860_, v_a_4863_);
if (lean_obj_tag(v___x_4885_) == 0)
{
lean_object* v_a_4886_; lean_object* v_id_4887_; lean_object* v_structId_4888_; uint8_t v___x_4889_; lean_object* v___x_4890_; 
v_a_4886_ = lean_ctor_get(v___x_4885_, 0);
lean_inc(v_a_4886_);
lean_dec_ref(v___x_4885_);
v_id_4887_ = lean_ctor_get(v_a_4875_, 0);
lean_inc(v_id_4887_);
v_structId_4888_ = lean_ctor_get(v_a_4875_, 1);
lean_inc(v_structId_4888_);
lean_dec(v_a_4875_);
v___x_4889_ = 0;
v___x_4890_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4878_, v___x_4889_, v_a_4886_, v_structId_4888_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_);
if (lean_obj_tag(v___x_4890_) == 0)
{
lean_object* v_a_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4947_; 
v_a_4891_ = lean_ctor_get(v___x_4890_, 0);
v_isSharedCheck_4947_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4947_ == 0)
{
v___x_4893_ = v___x_4890_;
v_isShared_4894_ = v_isSharedCheck_4947_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_a_4891_);
lean_dec(v___x_4890_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4947_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
if (lean_obj_tag(v_a_4891_) == 1)
{
lean_object* v_val_4895_; lean_object* v___x_4896_; 
lean_del_object(v___x_4893_);
v_val_4895_ = lean_ctor_get(v_a_4891_, 0);
lean_inc(v_val_4895_);
lean_dec_ref(v_a_4891_);
v___x_4896_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4861_, v_a_4863_);
if (lean_obj_tag(v___x_4896_) == 0)
{
lean_object* v_a_4897_; lean_object* v___x_4898_; 
v_a_4897_ = lean_ctor_get(v___x_4896_, 0);
lean_inc(v_a_4897_);
lean_dec_ref(v___x_4896_);
v___x_4898_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4881_, v___x_4889_, v_a_4897_, v_structId_4888_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_);
if (lean_obj_tag(v___x_4898_) == 0)
{
lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4926_; 
v_a_4899_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4926_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4926_ == 0)
{
v___x_4901_ = v___x_4898_;
v_isShared_4902_ = v_isSharedCheck_4926_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___x_4898_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4926_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
if (lean_obj_tag(v_a_4899_) == 1)
{
lean_object* v_val_4903_; lean_object* v___x_4905_; 
v_val_4903_ = lean_ctor_get(v_a_4899_, 0);
lean_inc_n(v_val_4903_, 2);
lean_dec_ref(v_a_4899_);
lean_inc(v_val_4895_);
if (v_isShared_4884_ == 0)
{
lean_ctor_set_tag(v___x_4883_, 3);
lean_ctor_set(v___x_4883_, 1, v_val_4903_);
lean_ctor_set(v___x_4883_, 0, v_val_4895_);
v___x_4905_ = v___x_4883_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_val_4895_);
lean_ctor_set(v_reuseFailAlloc_4921_, 1, v_val_4903_);
v___x_4905_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
lean_object* v___x_4906_; lean_object* v___x_4907_; uint8_t v___x_4908_; 
v___x_4906_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4905_);
v___x_4907_ = lean_box(0);
v___x_4908_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4906_, v___x_4907_);
if (v___x_4908_ == 0)
{
lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; 
lean_del_object(v___x_4901_);
lean_inc(v_val_4903_);
lean_inc(v_val_4895_);
lean_inc(v_id_4887_);
lean_inc_ref(v_b_4861_);
lean_inc_ref(v_a_4860_);
v___x_4909_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4909_, 0, v_a_4860_);
lean_ctor_set(v___x_4909_, 1, v_b_4861_);
lean_ctor_set(v___x_4909_, 2, v_id_4887_);
lean_ctor_set(v___x_4909_, 3, v_val_4895_);
lean_ctor_set(v___x_4909_, 4, v_val_4903_);
lean_inc(v___x_4906_);
v___x_4910_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4910_, 0, v___x_4906_);
lean_ctor_set(v___x_4910_, 1, v___x_4909_);
lean_ctor_set_uint8(v___x_4910_, sizeof(void*)*2, v___x_4889_);
v___x_4911_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4910_, v_structId_4888_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_);
if (lean_obj_tag(v___x_4911_) == 0)
{
lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; 
lean_dec_ref(v___x_4911_);
v___x_4912_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4913_ = l_Lean_Grind_Linarith_Poly_mul(v___x_4906_, v___x_4912_);
v___x_4914_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4914_, 0, v_b_4861_);
lean_ctor_set(v___x_4914_, 1, v_a_4860_);
lean_ctor_set(v___x_4914_, 2, v_id_4887_);
lean_ctor_set(v___x_4914_, 3, v_val_4903_);
lean_ctor_set(v___x_4914_, 4, v_val_4895_);
v___x_4915_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4915_, 0, v___x_4913_);
lean_ctor_set(v___x_4915_, 1, v___x_4914_);
lean_ctor_set_uint8(v___x_4915_, sizeof(void*)*2, v___x_4889_);
v___x_4916_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4915_, v_structId_4888_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_);
lean_dec(v_structId_4888_);
return v___x_4916_;
}
else
{
lean_dec(v___x_4906_);
lean_dec(v_val_4903_);
lean_dec(v_val_4895_);
lean_dec(v_structId_4888_);
lean_dec(v_id_4887_);
lean_dec_ref(v_b_4861_);
lean_dec_ref(v_a_4860_);
return v___x_4911_;
}
}
else
{
lean_object* v___x_4917_; lean_object* v___x_4919_; 
lean_dec(v___x_4906_);
lean_dec(v_val_4903_);
lean_dec(v_val_4895_);
lean_dec(v_structId_4888_);
lean_dec(v_id_4887_);
lean_dec_ref(v_b_4861_);
lean_dec_ref(v_a_4860_);
v___x_4917_ = lean_box(0);
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 0, v___x_4917_);
v___x_4919_ = v___x_4901_;
goto v_reusejp_4918_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v___x_4917_);
v___x_4919_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4918_;
}
v_reusejp_4918_:
{
return v___x_4919_;
}
}
}
}
else
{
lean_object* v___x_4922_; lean_object* v___x_4924_; 
lean_dec(v_a_4899_);
lean_dec(v_val_4895_);
lean_dec(v_structId_4888_);
lean_dec(v_id_4887_);
lean_del_object(v___x_4883_);
lean_dec_ref(v_b_4861_);
lean_dec_ref(v_a_4860_);
v___x_4922_ = lean_box(0);
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 0, v___x_4922_);
v___x_4924_ = v___x_4901_;
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
lean_object* v_a_4927_; lean_object* v___x_4929_; uint8_t v_isShared_4930_; uint8_t v_isSharedCheck_4934_; 
lean_dec(v_val_4895_);
lean_dec(v_structId_4888_);
lean_dec(v_id_4887_);
lean_del_object(v___x_4883_);
lean_dec_ref(v_b_4861_);
lean_dec_ref(v_a_4860_);
v_a_4927_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4934_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4934_ == 0)
{
v___x_4929_ = v___x_4898_;
v_isShared_4930_ = v_isSharedCheck_4934_;
goto v_resetjp_4928_;
}
else
{
lean_inc(v_a_4927_);
lean_dec(v___x_4898_);
v___x_4929_ = lean_box(0);
v_isShared_4930_ = v_isSharedCheck_4934_;
goto v_resetjp_4928_;
}
v_resetjp_4928_:
{
lean_object* v___x_4932_; 
if (v_isShared_4930_ == 0)
{
v___x_4932_ = v___x_4929_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4933_; 
v_reuseFailAlloc_4933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4933_, 0, v_a_4927_);
v___x_4932_ = v_reuseFailAlloc_4933_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
return v___x_4932_;
}
}
}
}
else
{
lean_object* v_a_4935_; lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_4942_; 
lean_dec(v_val_4895_);
lean_dec(v_structId_4888_);
lean_dec(v_id_4887_);
lean_del_object(v___x_4883_);
lean_dec(v_fst_4881_);
lean_dec_ref(v_b_4861_);
lean_dec_ref(v_a_4860_);
v_a_4935_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4942_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4942_ == 0)
{
v___x_4937_ = v___x_4896_;
v_isShared_4938_ = v_isSharedCheck_4942_;
goto v_resetjp_4936_;
}
else
{
lean_inc(v_a_4935_);
lean_dec(v___x_4896_);
v___x_4937_ = lean_box(0);
v_isShared_4938_ = v_isSharedCheck_4942_;
goto v_resetjp_4936_;
}
v_resetjp_4936_:
{
lean_object* v___x_4940_; 
if (v_isShared_4938_ == 0)
{
v___x_4940_ = v___x_4937_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v_a_4935_);
v___x_4940_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
return v___x_4940_;
}
}
}
}
else
{
lean_object* v___x_4943_; lean_object* v___x_4945_; 
lean_dec(v_a_4891_);
lean_dec(v_structId_4888_);
lean_dec(v_id_4887_);
lean_del_object(v___x_4883_);
lean_dec(v_fst_4881_);
lean_dec_ref(v_b_4861_);
lean_dec_ref(v_a_4860_);
v___x_4943_ = lean_box(0);
if (v_isShared_4894_ == 0)
{
lean_ctor_set(v___x_4893_, 0, v___x_4943_);
v___x_4945_ = v___x_4893_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v___x_4943_);
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
lean_object* v_a_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_4955_; 
lean_dec(v_structId_4888_);
lean_dec(v_id_4887_);
lean_del_object(v___x_4883_);
lean_dec(v_fst_4881_);
lean_dec_ref(v_b_4861_);
lean_dec_ref(v_a_4860_);
v_a_4948_ = lean_ctor_get(v___x_4890_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4950_ = v___x_4890_;
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_a_4948_);
lean_dec(v___x_4890_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v___x_4953_; 
if (v_isShared_4951_ == 0)
{
v___x_4953_ = v___x_4950_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v_a_4948_);
v___x_4953_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
return v___x_4953_;
}
}
}
}
else
{
lean_object* v_a_4956_; lean_object* v___x_4958_; uint8_t v_isShared_4959_; uint8_t v_isSharedCheck_4963_; 
lean_del_object(v___x_4883_);
lean_dec(v_fst_4881_);
lean_dec(v_fst_4878_);
lean_dec(v_a_4875_);
lean_dec_ref(v_b_4861_);
lean_dec_ref(v_a_4860_);
v_a_4956_ = lean_ctor_get(v___x_4885_, 0);
v_isSharedCheck_4963_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4963_ == 0)
{
v___x_4958_ = v___x_4885_;
v_isShared_4959_ = v_isSharedCheck_4963_;
goto v_resetjp_4957_;
}
else
{
lean_inc(v_a_4956_);
lean_dec(v___x_4885_);
v___x_4958_ = lean_box(0);
v_isShared_4959_ = v_isSharedCheck_4963_;
goto v_resetjp_4957_;
}
v_resetjp_4957_:
{
lean_object* v___x_4961_; 
if (v_isShared_4959_ == 0)
{
v___x_4961_ = v___x_4958_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_a_4956_);
v___x_4961_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
return v___x_4961_;
}
}
}
}
}
else
{
lean_object* v_a_4966_; lean_object* v___x_4968_; uint8_t v_isShared_4969_; uint8_t v_isSharedCheck_4973_; 
lean_dec(v_fst_4878_);
lean_dec(v_a_4875_);
lean_dec_ref(v_b_4861_);
lean_dec_ref(v_a_4860_);
v_a_4966_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4973_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4973_ == 0)
{
v___x_4968_ = v___x_4879_;
v_isShared_4969_ = v_isSharedCheck_4973_;
goto v_resetjp_4967_;
}
else
{
lean_inc(v_a_4966_);
lean_dec(v___x_4879_);
v___x_4968_ = lean_box(0);
v_isShared_4969_ = v_isSharedCheck_4973_;
goto v_resetjp_4967_;
}
v_resetjp_4967_:
{
lean_object* v___x_4971_; 
if (v_isShared_4969_ == 0)
{
v___x_4971_ = v___x_4968_;
goto v_reusejp_4970_;
}
else
{
lean_object* v_reuseFailAlloc_4972_; 
v_reuseFailAlloc_4972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4972_, 0, v_a_4966_);
v___x_4971_ = v_reuseFailAlloc_4972_;
goto v_reusejp_4970_;
}
v_reusejp_4970_:
{
return v___x_4971_;
}
}
}
}
else
{
lean_object* v_a_4974_; lean_object* v___x_4976_; uint8_t v_isShared_4977_; uint8_t v_isSharedCheck_4981_; 
lean_dec(v_a_4875_);
lean_dec_ref(v_b_4861_);
lean_dec_ref(v_a_4860_);
v_a_4974_ = lean_ctor_get(v___x_4876_, 0);
v_isSharedCheck_4981_ = !lean_is_exclusive(v___x_4876_);
if (v_isSharedCheck_4981_ == 0)
{
v___x_4976_ = v___x_4876_;
v_isShared_4977_ = v_isSharedCheck_4981_;
goto v_resetjp_4975_;
}
else
{
lean_inc(v_a_4974_);
lean_dec(v___x_4876_);
v___x_4976_ = lean_box(0);
v_isShared_4977_ = v_isSharedCheck_4981_;
goto v_resetjp_4975_;
}
v_resetjp_4975_:
{
lean_object* v___x_4979_; 
if (v_isShared_4977_ == 0)
{
v___x_4979_ = v___x_4976_;
goto v_reusejp_4978_;
}
else
{
lean_object* v_reuseFailAlloc_4980_; 
v_reuseFailAlloc_4980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4980_, 0, v_a_4974_);
v___x_4979_ = v_reuseFailAlloc_4980_;
goto v_reusejp_4978_;
}
v_reusejp_4978_:
{
return v___x_4979_;
}
}
}
}
else
{
lean_object* v_a_4982_; lean_object* v___x_4984_; uint8_t v_isShared_4985_; uint8_t v_isSharedCheck_4989_; 
lean_dec_ref(v_b_4861_);
lean_dec_ref(v_a_4860_);
v_a_4982_ = lean_ctor_get(v___x_4874_, 0);
v_isSharedCheck_4989_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_4989_ == 0)
{
v___x_4984_ = v___x_4874_;
v_isShared_4985_ = v_isSharedCheck_4989_;
goto v_resetjp_4983_;
}
else
{
lean_inc(v_a_4982_);
lean_dec(v___x_4874_);
v___x_4984_ = lean_box(0);
v_isShared_4985_ = v_isSharedCheck_4989_;
goto v_resetjp_4983_;
}
v_resetjp_4983_:
{
lean_object* v___x_4987_; 
if (v_isShared_4985_ == 0)
{
v___x_4987_ = v___x_4984_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v_a_4982_);
v___x_4987_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
return v___x_4987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27___boxed(lean_object* v_a_4990_, lean_object* v_b_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_){
_start:
{
lean_object* v_res_5004_; 
v_res_5004_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_4990_, v_b_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_);
lean_dec(v_a_5002_);
lean_dec_ref(v_a_5001_);
lean_dec(v_a_5000_);
lean_dec_ref(v_a_4999_);
lean_dec(v_a_4998_);
lean_dec_ref(v_a_4997_);
lean_dec(v_a_4996_);
lean_dec_ref(v_a_4995_);
lean_dec(v_a_4994_);
lean_dec(v_a_4993_);
lean_dec(v_a_4992_);
return v_res_5004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(lean_object* v_a_5005_, lean_object* v_b_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_){
_start:
{
lean_object* v___x_5019_; 
v___x_5019_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_);
if (lean_obj_tag(v___x_5019_) == 0)
{
lean_object* v_a_5020_; lean_object* v___x_5021_; 
v_a_5020_ = lean_ctor_get(v___x_5019_, 0);
lean_inc(v_a_5020_);
lean_dec_ref(v___x_5019_);
lean_inc_ref(v_a_5005_);
v___x_5021_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5005_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_);
if (lean_obj_tag(v___x_5021_) == 0)
{
lean_object* v_a_5022_; lean_object* v_fst_5023_; lean_object* v___x_5025_; uint8_t v_isShared_5026_; uint8_t v_isSharedCheck_5119_; 
v_a_5022_ = lean_ctor_get(v___x_5021_, 0);
lean_inc(v_a_5022_);
lean_dec_ref(v___x_5021_);
v_fst_5023_ = lean_ctor_get(v_a_5022_, 0);
v_isSharedCheck_5119_ = !lean_is_exclusive(v_a_5022_);
if (v_isSharedCheck_5119_ == 0)
{
lean_object* v_unused_5120_; 
v_unused_5120_ = lean_ctor_get(v_a_5022_, 1);
lean_dec(v_unused_5120_);
v___x_5025_ = v_a_5022_;
v_isShared_5026_ = v_isSharedCheck_5119_;
goto v_resetjp_5024_;
}
else
{
lean_inc(v_fst_5023_);
lean_dec(v_a_5022_);
v___x_5025_ = lean_box(0);
v_isShared_5026_ = v_isSharedCheck_5119_;
goto v_resetjp_5024_;
}
v_resetjp_5024_:
{
lean_object* v___x_5027_; 
lean_inc_ref(v_b_5006_);
v___x_5027_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_);
if (lean_obj_tag(v___x_5027_) == 0)
{
lean_object* v_a_5028_; lean_object* v_fst_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5109_; 
v_a_5028_ = lean_ctor_get(v___x_5027_, 0);
lean_inc(v_a_5028_);
lean_dec_ref(v___x_5027_);
v_fst_5029_ = lean_ctor_get(v_a_5028_, 0);
v_isSharedCheck_5109_ = !lean_is_exclusive(v_a_5028_);
if (v_isSharedCheck_5109_ == 0)
{
lean_object* v_unused_5110_; 
v_unused_5110_ = lean_ctor_get(v_a_5028_, 1);
lean_dec(v_unused_5110_);
v___x_5031_ = v_a_5028_;
v_isShared_5032_ = v_isSharedCheck_5109_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_fst_5029_);
lean_dec(v_a_5028_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5109_;
goto v_resetjp_5030_;
}
v_resetjp_5030_:
{
lean_object* v___x_5033_; 
v___x_5033_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5005_, v_a_5008_);
if (lean_obj_tag(v___x_5033_) == 0)
{
lean_object* v_a_5034_; lean_object* v_id_5035_; lean_object* v_structId_5036_; uint8_t v___x_5037_; lean_object* v___x_5038_; 
v_a_5034_ = lean_ctor_get(v___x_5033_, 0);
lean_inc(v_a_5034_);
lean_dec_ref(v___x_5033_);
v_id_5035_ = lean_ctor_get(v_a_5020_, 0);
lean_inc(v_id_5035_);
v_structId_5036_ = lean_ctor_get(v_a_5020_, 1);
lean_inc(v_structId_5036_);
lean_dec(v_a_5020_);
v___x_5037_ = 0;
v___x_5038_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5023_, v___x_5037_, v_a_5034_, v_structId_5036_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_);
if (lean_obj_tag(v___x_5038_) == 0)
{
lean_object* v_a_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5092_; 
v_a_5039_ = lean_ctor_get(v___x_5038_, 0);
v_isSharedCheck_5092_ = !lean_is_exclusive(v___x_5038_);
if (v_isSharedCheck_5092_ == 0)
{
v___x_5041_ = v___x_5038_;
v_isShared_5042_ = v_isSharedCheck_5092_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_a_5039_);
lean_dec(v___x_5038_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5092_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
if (lean_obj_tag(v_a_5039_) == 1)
{
lean_object* v_val_5043_; lean_object* v___x_5044_; 
lean_del_object(v___x_5041_);
v_val_5043_ = lean_ctor_get(v_a_5039_, 0);
lean_inc(v_val_5043_);
lean_dec_ref(v_a_5039_);
v___x_5044_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5006_, v_a_5008_);
if (lean_obj_tag(v___x_5044_) == 0)
{
lean_object* v_a_5045_; lean_object* v___x_5046_; 
v_a_5045_ = lean_ctor_get(v___x_5044_, 0);
lean_inc(v_a_5045_);
lean_dec_ref(v___x_5044_);
v___x_5046_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5029_, v___x_5037_, v_a_5045_, v_structId_5036_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_);
if (lean_obj_tag(v___x_5046_) == 0)
{
lean_object* v_a_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5071_; 
v_a_5047_ = lean_ctor_get(v___x_5046_, 0);
v_isSharedCheck_5071_ = !lean_is_exclusive(v___x_5046_);
if (v_isSharedCheck_5071_ == 0)
{
v___x_5049_ = v___x_5046_;
v_isShared_5050_ = v_isSharedCheck_5071_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_a_5047_);
lean_dec(v___x_5046_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5071_;
goto v_resetjp_5048_;
}
v_resetjp_5048_:
{
if (lean_obj_tag(v_a_5047_) == 1)
{
lean_object* v_val_5051_; lean_object* v___x_5053_; 
v_val_5051_ = lean_ctor_get(v_a_5047_, 0);
lean_inc_n(v_val_5051_, 2);
lean_dec_ref(v_a_5047_);
lean_inc(v_val_5043_);
if (v_isShared_5032_ == 0)
{
lean_ctor_set_tag(v___x_5031_, 3);
lean_ctor_set(v___x_5031_, 1, v_val_5051_);
lean_ctor_set(v___x_5031_, 0, v_val_5043_);
v___x_5053_ = v___x_5031_;
goto v_reusejp_5052_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_val_5043_);
lean_ctor_set(v_reuseFailAlloc_5066_, 1, v_val_5051_);
v___x_5053_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5052_;
}
v_reusejp_5052_:
{
lean_object* v___x_5054_; lean_object* v___x_5055_; uint8_t v___x_5056_; 
v___x_5054_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5053_);
v___x_5055_ = lean_box(0);
v___x_5056_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_5054_, v___x_5055_);
if (v___x_5056_ == 0)
{
lean_object* v___x_5057_; lean_object* v___x_5059_; 
lean_del_object(v___x_5049_);
v___x_5057_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5057_, 0, v_a_5005_);
lean_ctor_set(v___x_5057_, 1, v_b_5006_);
lean_ctor_set(v___x_5057_, 2, v_id_5035_);
lean_ctor_set(v___x_5057_, 3, v_val_5043_);
lean_ctor_set(v___x_5057_, 4, v_val_5051_);
if (v_isShared_5026_ == 0)
{
lean_ctor_set(v___x_5025_, 1, v___x_5057_);
lean_ctor_set(v___x_5025_, 0, v___x_5054_);
v___x_5059_ = v___x_5025_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v___x_5054_);
lean_ctor_set(v_reuseFailAlloc_5061_, 1, v___x_5057_);
v___x_5059_ = v_reuseFailAlloc_5061_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
lean_object* v___x_5060_; 
v___x_5060_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_5059_, v_structId_5036_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_);
lean_dec(v_structId_5036_);
return v___x_5060_;
}
}
else
{
lean_object* v___x_5062_; lean_object* v___x_5064_; 
lean_dec(v___x_5054_);
lean_dec(v_val_5051_);
lean_dec(v_val_5043_);
lean_dec(v_structId_5036_);
lean_dec(v_id_5035_);
lean_del_object(v___x_5025_);
lean_dec_ref(v_b_5006_);
lean_dec_ref(v_a_5005_);
v___x_5062_ = lean_box(0);
if (v_isShared_5050_ == 0)
{
lean_ctor_set(v___x_5049_, 0, v___x_5062_);
v___x_5064_ = v___x_5049_;
goto v_reusejp_5063_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v___x_5062_);
v___x_5064_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5063_;
}
v_reusejp_5063_:
{
return v___x_5064_;
}
}
}
}
else
{
lean_object* v___x_5067_; lean_object* v___x_5069_; 
lean_dec(v_a_5047_);
lean_dec(v_val_5043_);
lean_dec(v_structId_5036_);
lean_dec(v_id_5035_);
lean_del_object(v___x_5031_);
lean_del_object(v___x_5025_);
lean_dec_ref(v_b_5006_);
lean_dec_ref(v_a_5005_);
v___x_5067_ = lean_box(0);
if (v_isShared_5050_ == 0)
{
lean_ctor_set(v___x_5049_, 0, v___x_5067_);
v___x_5069_ = v___x_5049_;
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
lean_object* v_a_5072_; lean_object* v___x_5074_; uint8_t v_isShared_5075_; uint8_t v_isSharedCheck_5079_; 
lean_dec(v_val_5043_);
lean_dec(v_structId_5036_);
lean_dec(v_id_5035_);
lean_del_object(v___x_5031_);
lean_del_object(v___x_5025_);
lean_dec_ref(v_b_5006_);
lean_dec_ref(v_a_5005_);
v_a_5072_ = lean_ctor_get(v___x_5046_, 0);
v_isSharedCheck_5079_ = !lean_is_exclusive(v___x_5046_);
if (v_isSharedCheck_5079_ == 0)
{
v___x_5074_ = v___x_5046_;
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
else
{
lean_inc(v_a_5072_);
lean_dec(v___x_5046_);
v___x_5074_ = lean_box(0);
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
v_resetjp_5073_:
{
lean_object* v___x_5077_; 
if (v_isShared_5075_ == 0)
{
v___x_5077_ = v___x_5074_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_a_5072_);
v___x_5077_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5076_;
}
v_reusejp_5076_:
{
return v___x_5077_;
}
}
}
}
else
{
lean_object* v_a_5080_; lean_object* v___x_5082_; uint8_t v_isShared_5083_; uint8_t v_isSharedCheck_5087_; 
lean_dec(v_val_5043_);
lean_dec(v_structId_5036_);
lean_dec(v_id_5035_);
lean_del_object(v___x_5031_);
lean_dec(v_fst_5029_);
lean_del_object(v___x_5025_);
lean_dec_ref(v_b_5006_);
lean_dec_ref(v_a_5005_);
v_a_5080_ = lean_ctor_get(v___x_5044_, 0);
v_isSharedCheck_5087_ = !lean_is_exclusive(v___x_5044_);
if (v_isSharedCheck_5087_ == 0)
{
v___x_5082_ = v___x_5044_;
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
else
{
lean_inc(v_a_5080_);
lean_dec(v___x_5044_);
v___x_5082_ = lean_box(0);
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
v_resetjp_5081_:
{
lean_object* v___x_5085_; 
if (v_isShared_5083_ == 0)
{
v___x_5085_ = v___x_5082_;
goto v_reusejp_5084_;
}
else
{
lean_object* v_reuseFailAlloc_5086_; 
v_reuseFailAlloc_5086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_a_5080_);
v___x_5085_ = v_reuseFailAlloc_5086_;
goto v_reusejp_5084_;
}
v_reusejp_5084_:
{
return v___x_5085_;
}
}
}
}
else
{
lean_object* v___x_5088_; lean_object* v___x_5090_; 
lean_dec(v_a_5039_);
lean_dec(v_structId_5036_);
lean_dec(v_id_5035_);
lean_del_object(v___x_5031_);
lean_dec(v_fst_5029_);
lean_del_object(v___x_5025_);
lean_dec_ref(v_b_5006_);
lean_dec_ref(v_a_5005_);
v___x_5088_ = lean_box(0);
if (v_isShared_5042_ == 0)
{
lean_ctor_set(v___x_5041_, 0, v___x_5088_);
v___x_5090_ = v___x_5041_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v___x_5088_);
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
lean_object* v_a_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5100_; 
lean_dec(v_structId_5036_);
lean_dec(v_id_5035_);
lean_del_object(v___x_5031_);
lean_dec(v_fst_5029_);
lean_del_object(v___x_5025_);
lean_dec_ref(v_b_5006_);
lean_dec_ref(v_a_5005_);
v_a_5093_ = lean_ctor_get(v___x_5038_, 0);
v_isSharedCheck_5100_ = !lean_is_exclusive(v___x_5038_);
if (v_isSharedCheck_5100_ == 0)
{
v___x_5095_ = v___x_5038_;
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_a_5093_);
lean_dec(v___x_5038_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v___x_5098_; 
if (v_isShared_5096_ == 0)
{
v___x_5098_ = v___x_5095_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v_a_5093_);
v___x_5098_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
return v___x_5098_;
}
}
}
}
else
{
lean_object* v_a_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5108_; 
lean_del_object(v___x_5031_);
lean_dec(v_fst_5029_);
lean_del_object(v___x_5025_);
lean_dec(v_fst_5023_);
lean_dec(v_a_5020_);
lean_dec_ref(v_b_5006_);
lean_dec_ref(v_a_5005_);
v_a_5101_ = lean_ctor_get(v___x_5033_, 0);
v_isSharedCheck_5108_ = !lean_is_exclusive(v___x_5033_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_5103_ = v___x_5033_;
v_isShared_5104_ = v_isSharedCheck_5108_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_a_5101_);
lean_dec(v___x_5033_);
v___x_5103_ = lean_box(0);
v_isShared_5104_ = v_isSharedCheck_5108_;
goto v_resetjp_5102_;
}
v_resetjp_5102_:
{
lean_object* v___x_5106_; 
if (v_isShared_5104_ == 0)
{
v___x_5106_ = v___x_5103_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5107_; 
v_reuseFailAlloc_5107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5107_, 0, v_a_5101_);
v___x_5106_ = v_reuseFailAlloc_5107_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
return v___x_5106_;
}
}
}
}
}
else
{
lean_object* v_a_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5118_; 
lean_del_object(v___x_5025_);
lean_dec(v_fst_5023_);
lean_dec(v_a_5020_);
lean_dec_ref(v_b_5006_);
lean_dec_ref(v_a_5005_);
v_a_5111_ = lean_ctor_get(v___x_5027_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v___x_5027_);
if (v_isSharedCheck_5118_ == 0)
{
v___x_5113_ = v___x_5027_;
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_a_5111_);
lean_dec(v___x_5027_);
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
lean_object* v_a_5121_; lean_object* v___x_5123_; uint8_t v_isShared_5124_; uint8_t v_isSharedCheck_5128_; 
lean_dec(v_a_5020_);
lean_dec_ref(v_b_5006_);
lean_dec_ref(v_a_5005_);
v_a_5121_ = lean_ctor_get(v___x_5021_, 0);
v_isSharedCheck_5128_ = !lean_is_exclusive(v___x_5021_);
if (v_isSharedCheck_5128_ == 0)
{
v___x_5123_ = v___x_5021_;
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
else
{
lean_inc(v_a_5121_);
lean_dec(v___x_5021_);
v___x_5123_ = lean_box(0);
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
v_resetjp_5122_:
{
lean_object* v___x_5126_; 
if (v_isShared_5124_ == 0)
{
v___x_5126_ = v___x_5123_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_a_5121_);
v___x_5126_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
return v___x_5126_;
}
}
}
}
else
{
lean_object* v_a_5129_; lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5136_; 
lean_dec_ref(v_b_5006_);
lean_dec_ref(v_a_5005_);
v_a_5129_ = lean_ctor_get(v___x_5019_, 0);
v_isSharedCheck_5136_ = !lean_is_exclusive(v___x_5019_);
if (v_isSharedCheck_5136_ == 0)
{
v___x_5131_ = v___x_5019_;
v_isShared_5132_ = v_isSharedCheck_5136_;
goto v_resetjp_5130_;
}
else
{
lean_inc(v_a_5129_);
lean_dec(v___x_5019_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5136_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
lean_object* v___x_5134_; 
if (v_isShared_5132_ == 0)
{
v___x_5134_ = v___x_5131_;
goto v_reusejp_5133_;
}
else
{
lean_object* v_reuseFailAlloc_5135_; 
v_reuseFailAlloc_5135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5135_, 0, v_a_5129_);
v___x_5134_ = v_reuseFailAlloc_5135_;
goto v_reusejp_5133_;
}
v_reusejp_5133_:
{
return v___x_5134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq___boxed(lean_object* v_a_5137_, lean_object* v_b_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_){
_start:
{
lean_object* v_res_5151_; 
v_res_5151_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5137_, v_b_5138_, v_a_5139_, v_a_5140_, v_a_5141_, v_a_5142_, v_a_5143_, v_a_5144_, v_a_5145_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_);
lean_dec(v_a_5149_);
lean_dec_ref(v_a_5148_);
lean_dec(v_a_5147_);
lean_dec_ref(v_a_5146_);
lean_dec(v_a_5145_);
lean_dec_ref(v_a_5144_);
lean_dec(v_a_5143_);
lean_dec_ref(v_a_5142_);
lean_dec(v_a_5141_);
lean_dec(v_a_5140_);
lean_dec(v_a_5139_);
return v_res_5151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq(lean_object* v_a_5152_, lean_object* v_b_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_){
_start:
{
uint8_t v___x_5165_; 
v___x_5165_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_5152_, v_b_5153_);
if (v___x_5165_ == 0)
{
lean_object* v___x_5166_; 
v___x_5166_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5152_, v_b_5153_, v_a_5154_, v_a_5162_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v_a_5167_; 
v_a_5167_ = lean_ctor_get(v___x_5166_, 0);
lean_inc(v_a_5167_);
lean_dec_ref(v___x_5166_);
if (lean_obj_tag(v_a_5167_) == 1)
{
lean_object* v_val_5168_; lean_object* v___x_5169_; 
v_val_5168_ = lean_ctor_get(v_a_5167_, 0);
lean_inc(v_val_5168_);
lean_dec_ref(v_a_5167_);
v___x_5169_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_val_5168_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_);
if (lean_obj_tag(v___x_5169_) == 0)
{
lean_object* v_a_5170_; uint8_t v___x_5171_; 
v_a_5170_ = lean_ctor_get(v___x_5169_, 0);
lean_inc(v_a_5170_);
lean_dec_ref(v___x_5169_);
v___x_5171_ = lean_unbox(v_a_5170_);
lean_dec(v_a_5170_);
if (v___x_5171_ == 0)
{
lean_object* v___x_5172_; 
v___x_5172_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5168_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_);
if (lean_obj_tag(v___x_5172_) == 0)
{
lean_object* v_a_5173_; uint8_t v___x_5174_; 
v_a_5173_ = lean_ctor_get(v___x_5172_, 0);
lean_inc(v_a_5173_);
lean_dec_ref(v___x_5172_);
v___x_5174_ = lean_unbox(v_a_5173_);
lean_dec(v_a_5173_);
if (v___x_5174_ == 0)
{
lean_object* v___x_5175_; 
v___x_5175_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_5152_, v_b_5153_, v_val_5168_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_);
lean_dec(v_val_5168_);
return v___x_5175_;
}
else
{
lean_object* v___x_5176_; 
lean_dec(v_val_5168_);
v___x_5176_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_5152_, v_b_5153_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_);
return v___x_5176_;
}
}
else
{
lean_object* v_a_5177_; lean_object* v___x_5179_; uint8_t v_isShared_5180_; uint8_t v_isSharedCheck_5184_; 
lean_dec(v_val_5168_);
lean_dec_ref(v_b_5153_);
lean_dec_ref(v_a_5152_);
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
v___x_5185_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5168_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_);
if (lean_obj_tag(v___x_5185_) == 0)
{
lean_object* v_a_5186_; uint8_t v___x_5187_; 
v_a_5186_ = lean_ctor_get(v___x_5185_, 0);
lean_inc(v_a_5186_);
lean_dec_ref(v___x_5185_);
v___x_5187_ = lean_unbox(v_a_5186_);
lean_dec(v_a_5186_);
if (v___x_5187_ == 0)
{
lean_object* v___x_5188_; 
v___x_5188_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_5152_, v_b_5153_, v_val_5168_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_);
lean_dec(v_val_5168_);
return v___x_5188_;
}
else
{
lean_object* v___x_5189_; 
v___x_5189_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_5152_, v_b_5153_, v_val_5168_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_);
lean_dec(v_val_5168_);
return v___x_5189_;
}
}
else
{
lean_object* v_a_5190_; lean_object* v___x_5192_; uint8_t v_isShared_5193_; uint8_t v_isSharedCheck_5197_; 
lean_dec(v_val_5168_);
lean_dec_ref(v_b_5153_);
lean_dec_ref(v_a_5152_);
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
lean_dec_ref(v_b_5153_);
lean_dec_ref(v_a_5152_);
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
v___x_5206_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5152_, v_b_5153_, v_a_5154_, v_a_5162_);
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
lean_dec_ref(v_a_5207_);
v___x_5212_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_5211_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_);
if (lean_obj_tag(v___x_5212_) == 0)
{
lean_object* v_a_5213_; lean_object* v_orderedAddInst_x3f_5214_; 
v_a_5213_ = lean_ctor_get(v___x_5212_, 0);
lean_inc(v_a_5213_);
lean_dec_ref(v___x_5212_);
v_orderedAddInst_x3f_5214_ = lean_ctor_get(v_a_5213_, 9);
lean_inc(v_orderedAddInst_x3f_5214_);
lean_dec(v_a_5213_);
if (lean_obj_tag(v_orderedAddInst_x3f_5214_) == 0)
{
lean_object* v___x_5215_; 
v___x_5215_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5152_, v_b_5153_, v_val_5211_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_);
lean_dec(v_val_5211_);
return v___x_5215_;
}
else
{
lean_object* v___x_5216_; 
lean_dec_ref(v_orderedAddInst_x3f_5214_);
v___x_5216_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5152_, v_b_5153_, v_val_5211_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_);
lean_dec(v_val_5211_);
return v___x_5216_;
}
}
else
{
lean_object* v_a_5217_; lean_object* v___x_5219_; uint8_t v_isShared_5220_; uint8_t v_isSharedCheck_5224_; 
lean_dec(v_val_5211_);
lean_dec_ref(v_b_5153_);
lean_dec_ref(v_a_5152_);
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
lean_dec_ref(v_b_5153_);
lean_dec_ref(v_a_5152_);
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
lean_dec_ref(v_b_5153_);
lean_dec_ref(v_a_5152_);
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
lean_dec_ref(v_b_5153_);
lean_dec_ref(v_a_5152_);
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
lean_dec_ref(v_b_5153_);
lean_dec_ref(v_a_5152_);
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
lean_dec_ref(v_a_5281_);
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
lean_dec_ref(v_a_5289_);
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
lean_object* v_a_5299_; lean_object* v___x_5300_; 
v_a_5299_ = lean_ctor_get(v___x_5298_, 0);
lean_inc(v_a_5299_);
lean_dec_ref(v___x_5298_);
v___x_5300_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5262_, v_a_5265_);
lean_dec_ref(v_a_5262_);
if (lean_obj_tag(v___x_5300_) == 0)
{
lean_object* v_a_5301_; lean_object* v___x_5302_; 
v_a_5301_ = lean_ctor_get(v___x_5300_, 0);
lean_inc(v_a_5301_);
lean_dec_ref(v___x_5300_);
v___x_5302_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5263_, v_a_5265_);
lean_dec_ref(v_b_5263_);
if (lean_obj_tag(v___x_5302_) == 0)
{
lean_object* v_a_5303_; lean_object* v_p_5304_; lean_object* v___y_5306_; uint8_t v___x_5340_; 
v_a_5303_ = lean_ctor_get(v___x_5302_, 0);
lean_inc(v_a_5303_);
lean_dec_ref(v___x_5302_);
v_p_5304_ = lean_ctor_get(v_a_5299_, 0);
v___x_5340_ = lean_nat_dec_le(v_a_5301_, v_a_5303_);
if (v___x_5340_ == 0)
{
lean_dec(v_a_5303_);
v___y_5306_ = v_a_5301_;
goto v___jp_5305_;
}
else
{
lean_dec(v_a_5301_);
v___y_5306_ = v_a_5303_;
goto v___jp_5305_;
}
v___jp_5305_:
{
lean_object* v___x_5307_; 
lean_inc(v___y_5306_);
lean_inc_ref(v_p_5304_);
v___x_5307_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_5304_, v___y_5306_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_);
if (lean_obj_tag(v___x_5307_) == 0)
{
lean_object* v_a_5308_; lean_object* v___x_5309_; 
v_a_5308_ = lean_ctor_get(v___x_5307_, 0);
lean_inc(v_a_5308_);
lean_dec_ref(v___x_5307_);
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
lean_dec_ref(v_a_5310_);
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
lean_dec(v_a_5301_);
lean_dec(v_a_5299_);
v_a_5341_ = lean_ctor_get(v___x_5302_, 0);
v_isSharedCheck_5348_ = !lean_is_exclusive(v___x_5302_);
if (v_isSharedCheck_5348_ == 0)
{
v___x_5343_ = v___x_5302_;
v_isShared_5344_ = v_isSharedCheck_5348_;
goto v_resetjp_5342_;
}
else
{
lean_inc(v_a_5341_);
lean_dec(v___x_5302_);
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
v_a_5349_ = lean_ctor_get(v___x_5300_, 0);
v_isSharedCheck_5356_ = !lean_is_exclusive(v___x_5300_);
if (v_isSharedCheck_5356_ == 0)
{
v___x_5351_ = v___x_5300_;
v_isShared_5352_ = v_isSharedCheck_5356_;
goto v_resetjp_5350_;
}
else
{
lean_inc(v_a_5349_);
lean_dec(v___x_5300_);
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
lean_dec_ref(v___x_5420_);
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
lean_dec_ref(v_a_5424_);
v___x_5429_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5407_, v_a_5409_);
if (lean_obj_tag(v___x_5429_) == 0)
{
lean_object* v_a_5430_; lean_object* v___x_5431_; 
v_a_5430_ = lean_ctor_get(v___x_5429_, 0);
lean_inc(v_a_5430_);
lean_dec_ref(v___x_5429_);
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
lean_dec_ref(v_a_5432_);
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
lean_dec_ref(v___x_5513_);
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
lean_dec_ref(v___x_5519_);
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
lean_dec_ref(v___x_5525_);
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
lean_dec_ref(v___x_5531_);
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
lean_dec_ref(v_a_5535_);
v___x_5540_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5500_, v_a_5502_);
if (lean_obj_tag(v___x_5540_) == 0)
{
lean_object* v_a_5541_; lean_object* v___x_5542_; 
v_a_5541_ = lean_ctor_get(v___x_5540_, 0);
lean_inc(v_a_5541_);
lean_dec_ref(v___x_5540_);
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
lean_dec_ref(v_a_5543_);
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
lean_dec_ref(v___x_5655_);
if (lean_obj_tag(v_a_5656_) == 1)
{
lean_object* v_val_5657_; lean_object* v___x_5658_; 
v_val_5657_ = lean_ctor_get(v_a_5656_, 0);
lean_inc(v_val_5657_);
lean_dec_ref(v_a_5656_);
v___x_5658_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5657_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_);
if (lean_obj_tag(v___x_5658_) == 0)
{
lean_object* v_a_5659_; uint8_t v___x_5660_; 
v_a_5659_ = lean_ctor_get(v___x_5658_, 0);
lean_inc(v_a_5659_);
lean_dec_ref(v___x_5658_);
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
lean_dec_ref(v_a_5672_);
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
