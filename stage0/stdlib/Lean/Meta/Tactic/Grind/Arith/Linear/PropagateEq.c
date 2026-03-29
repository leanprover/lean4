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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_fileName_1362_; lean_object* v_fileMap_1363_; lean_object* v_options_1364_; lean_object* v_currRecDepth_1365_; lean_object* v_maxRecDepth_1366_; lean_object* v_ref_1367_; lean_object* v_currNamespace_1368_; lean_object* v_openDecls_1369_; lean_object* v_initHeartbeats_1370_; lean_object* v_maxHeartbeats_1371_; lean_object* v_quotContext_1372_; lean_object* v_currMacroScope_1373_; uint8_t v_diag_1374_; lean_object* v_cancelTk_x3f_1375_; uint8_t v_suppressElabErrors_1376_; lean_object* v_inheritedTraceOptions_1377_; uint8_t v___x_1378_; 
v_fileName_1362_ = lean_ctor_get(v_a_1359_, 0);
lean_inc_ref(v_fileName_1362_);
v_fileMap_1363_ = lean_ctor_get(v_a_1359_, 1);
lean_inc_ref(v_fileMap_1363_);
v_options_1364_ = lean_ctor_get(v_a_1359_, 2);
lean_inc_ref(v_options_1364_);
v_currRecDepth_1365_ = lean_ctor_get(v_a_1359_, 3);
lean_inc(v_currRecDepth_1365_);
v_maxRecDepth_1366_ = lean_ctor_get(v_a_1359_, 4);
lean_inc(v_maxRecDepth_1366_);
v_ref_1367_ = lean_ctor_get(v_a_1359_, 5);
lean_inc(v_ref_1367_);
v_currNamespace_1368_ = lean_ctor_get(v_a_1359_, 6);
lean_inc(v_currNamespace_1368_);
v_openDecls_1369_ = lean_ctor_get(v_a_1359_, 7);
lean_inc(v_openDecls_1369_);
v_initHeartbeats_1370_ = lean_ctor_get(v_a_1359_, 8);
lean_inc(v_initHeartbeats_1370_);
v_maxHeartbeats_1371_ = lean_ctor_get(v_a_1359_, 9);
lean_inc(v_maxHeartbeats_1371_);
v_quotContext_1372_ = lean_ctor_get(v_a_1359_, 10);
lean_inc(v_quotContext_1372_);
v_currMacroScope_1373_ = lean_ctor_get(v_a_1359_, 11);
lean_inc(v_currMacroScope_1373_);
v_diag_1374_ = lean_ctor_get_uint8(v_a_1359_, sizeof(void*)*14);
v_cancelTk_x3f_1375_ = lean_ctor_get(v_a_1359_, 12);
lean_inc(v_cancelTk_x3f_1375_);
v_suppressElabErrors_1376_ = lean_ctor_get_uint8(v_a_1359_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1377_ = lean_ctor_get(v_a_1359_, 13);
lean_inc_ref(v_inheritedTraceOptions_1377_);
lean_dec_ref(v_a_1359_);
v___x_1378_ = lean_nat_dec_eq(v_currRecDepth_1365_, v_maxRecDepth_1366_);
if (v___x_1378_ == 0)
{
lean_object* v_p_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_p_1379_ = lean_ctor_get(v_c_1349_, 0);
v___x_1380_ = lean_unsigned_to_nat(1u);
v___x_1381_ = lean_nat_add(v_currRecDepth_1365_, v___x_1380_);
lean_dec(v_currRecDepth_1365_);
lean_inc_ref(v_inheritedTraceOptions_1377_);
lean_inc_ref(v_options_1364_);
v___x_1382_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1382_, 0, v_fileName_1362_);
lean_ctor_set(v___x_1382_, 1, v_fileMap_1363_);
lean_ctor_set(v___x_1382_, 2, v_options_1364_);
lean_ctor_set(v___x_1382_, 3, v___x_1381_);
lean_ctor_set(v___x_1382_, 4, v_maxRecDepth_1366_);
lean_ctor_set(v___x_1382_, 5, v_ref_1367_);
lean_ctor_set(v___x_1382_, 6, v_currNamespace_1368_);
lean_ctor_set(v___x_1382_, 7, v_openDecls_1369_);
lean_ctor_set(v___x_1382_, 8, v_initHeartbeats_1370_);
lean_ctor_set(v___x_1382_, 9, v_maxHeartbeats_1371_);
lean_ctor_set(v___x_1382_, 10, v_quotContext_1372_);
lean_ctor_set(v___x_1382_, 11, v_currMacroScope_1373_);
lean_ctor_set(v___x_1382_, 12, v_cancelTk_x3f_1375_);
lean_ctor_set(v___x_1382_, 13, v_inheritedTraceOptions_1377_);
lean_ctor_set_uint8(v___x_1382_, sizeof(void*)*14, v_diag_1374_);
lean_ctor_set_uint8(v___x_1382_, sizeof(void*)*14 + 1, v_suppressElabErrors_1376_);
lean_inc(v_p_1379_);
v___x_1383_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar(v_p_1379_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v___x_1382_, v_a_1360_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1474_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1386_ = v___x_1383_;
v_isShared_1387_ = v_isSharedCheck_1474_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1474_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
if (lean_obj_tag(v_a_1384_) == 1)
{
lean_object* v_val_1388_; lean_object* v_snd_1389_; lean_object* v_fst_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1470_; 
lean_del_object(v___x_1386_);
v_val_1388_ = lean_ctor_get(v_a_1384_, 0);
lean_inc(v_val_1388_);
lean_dec_ref(v_a_1384_);
v_snd_1389_ = lean_ctor_get(v_val_1388_, 1);
v_fst_1390_ = lean_ctor_get(v_val_1388_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_val_1388_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1392_ = v_val_1388_;
v_isShared_1393_ = v_isSharedCheck_1470_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_snd_1389_);
lean_inc(v_fst_1390_);
lean_dec(v_val_1388_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1470_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_fst_1394_; lean_object* v_snd_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1469_; 
v_fst_1394_ = lean_ctor_get(v_snd_1389_, 0);
v_snd_1395_ = lean_ctor_get(v_snd_1389_, 1);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_snd_1389_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1397_ = v_snd_1389_;
v_isShared_1398_ = v_isSharedCheck_1469_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_snd_1395_);
lean_inc(v_fst_1394_);
lean_dec(v_snd_1389_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1469_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; uint8_t v_hasTrace_1416_; 
v_hasTrace_1416_ = lean_ctor_get_uint8(v_options_1364_, sizeof(void*)*1);
if (v_hasTrace_1416_ == 0)
{
lean_del_object(v___x_1392_);
lean_dec_ref(v_inheritedTraceOptions_1377_);
lean_dec_ref(v_options_1364_);
v___y_1400_ = v_a_1350_;
v___y_1401_ = v_a_1351_;
v___y_1402_ = v_a_1352_;
v___y_1403_ = v_a_1353_;
v___y_1404_ = v_a_1354_;
v___y_1405_ = v_a_1355_;
v___y_1406_ = v_a_1356_;
v___y_1407_ = v_a_1357_;
v___y_1408_ = v_a_1358_;
v___y_1409_ = v___x_1382_;
v___y_1410_ = v_a_1360_;
goto v___jp_1399_;
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_1418_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_1419_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1377_, v_options_1364_, v___x_1418_);
lean_dec_ref(v_options_1364_);
lean_dec_ref(v_inheritedTraceOptions_1377_);
if (v___x_1419_ == 0)
{
lean_del_object(v___x_1392_);
v___y_1400_ = v_a_1350_;
v___y_1401_ = v_a_1351_;
v___y_1402_ = v_a_1352_;
v___y_1403_ = v_a_1353_;
v___y_1404_ = v_a_1354_;
v___y_1405_ = v_a_1355_;
v___y_1406_ = v_a_1356_;
v___y_1407_ = v_a_1357_;
v___y_1408_ = v_a_1358_;
v___y_1409_ = v___x_1382_;
v___y_1410_ = v_a_1360_;
goto v___jp_1399_;
}
else
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_1390_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v___x_1382_, v_a_1360_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref(v___x_1420_);
v___x_1422_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v___x_1382_, v_a_1360_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1424_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref(v___x_1422_);
v___x_1424_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_fst_1394_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v___x_1382_, v_a_1360_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref(v___x_1424_);
v___x_1426_ = l_Lean_MessageData_ofExpr(v_a_1421_);
v___x_1427_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_1393_ == 0)
{
lean_ctor_set_tag(v___x_1392_, 7);
lean_ctor_set(v___x_1392_, 1, v___x_1427_);
lean_ctor_set(v___x_1392_, 0, v___x_1426_);
v___x_1429_ = v___x_1392_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1430_ = l_Lean_MessageData_ofExpr(v_a_1423_);
v___x_1431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1429_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
lean_ctor_set(v___x_1432_, 1, v___x_1427_);
v___x_1433_ = l_Lean_MessageData_ofExpr(v_a_1425_);
v___x_1434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1432_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
v___x_1435_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_1417_, v___x_1434_, v_a_1357_, v_a_1358_, v___x_1382_, v_a_1360_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_dec_ref(v___x_1435_);
v___y_1400_ = v_a_1350_;
v___y_1401_ = v_a_1351_;
v___y_1402_ = v_a_1352_;
v___y_1403_ = v_a_1353_;
v___y_1404_ = v_a_1354_;
v___y_1405_ = v_a_1355_;
v___y_1406_ = v_a_1356_;
v___y_1407_ = v_a_1357_;
v___y_1408_ = v_a_1358_;
v___y_1409_ = v___x_1382_;
v___y_1410_ = v_a_1360_;
goto v___jp_1399_;
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_del_object(v___x_1397_);
lean_dec(v_snd_1395_);
lean_dec(v_fst_1394_);
lean_dec(v_fst_1390_);
lean_dec_ref(v___x_1382_);
lean_dec_ref(v_c_1349_);
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
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
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec(v_a_1423_);
lean_dec(v_a_1421_);
lean_del_object(v___x_1397_);
lean_dec(v_snd_1395_);
lean_dec(v_fst_1394_);
lean_del_object(v___x_1392_);
lean_dec(v_fst_1390_);
lean_dec_ref(v___x_1382_);
lean_dec_ref(v_c_1349_);
v_a_1445_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1424_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1424_);
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
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec(v_a_1421_);
lean_del_object(v___x_1397_);
lean_dec(v_snd_1395_);
lean_dec(v_fst_1394_);
lean_del_object(v___x_1392_);
lean_dec(v_fst_1390_);
lean_dec_ref(v___x_1382_);
lean_dec_ref(v_c_1349_);
v_a_1453_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1422_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1422_);
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
lean_del_object(v___x_1397_);
lean_dec(v_snd_1395_);
lean_dec(v_fst_1394_);
lean_del_object(v___x_1392_);
lean_dec(v_fst_1390_);
lean_dec_ref(v___x_1382_);
lean_dec_ref(v_c_1349_);
v_a_1461_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1420_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1420_);
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
}
v___jp_1399_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_1411_, 0, v_fst_1390_);
lean_ctor_set(v___x_1411_, 1, v_fst_1394_);
lean_ctor_set(v___x_1411_, 2, v_c_1349_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 1, v___x_1411_);
lean_ctor_set(v___x_1397_, 0, v_snd_1395_);
v___x_1413_ = v___x_1397_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_snd_1395_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
v_c_1349_ = v___x_1413_;
v_a_1350_ = v___y_1400_;
v_a_1351_ = v___y_1401_;
v_a_1352_ = v___y_1402_;
v_a_1353_ = v___y_1403_;
v_a_1354_ = v___y_1404_;
v_a_1355_ = v___y_1405_;
v_a_1356_ = v___y_1406_;
v_a_1357_ = v___y_1407_;
v_a_1358_ = v___y_1408_;
v_a_1359_ = v___y_1409_;
v_a_1360_ = v___y_1410_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_1472_; 
lean_dec(v_a_1384_);
lean_dec_ref(v___x_1382_);
lean_dec_ref(v_inheritedTraceOptions_1377_);
lean_dec_ref(v_options_1364_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v_c_1349_);
v___x_1472_ = v___x_1386_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_c_1349_);
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
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec_ref(v___x_1382_);
lean_dec_ref(v_inheritedTraceOptions_1377_);
lean_dec_ref(v_options_1364_);
lean_dec_ref(v_c_1349_);
v_a_1475_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1383_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1383_);
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
else
{
lean_object* v___x_1483_; 
lean_dec_ref(v_inheritedTraceOptions_1377_);
lean_dec(v_cancelTk_x3f_1375_);
lean_dec(v_currMacroScope_1373_);
lean_dec(v_quotContext_1372_);
lean_dec(v_maxHeartbeats_1371_);
lean_dec(v_initHeartbeats_1370_);
lean_dec(v_openDecls_1369_);
lean_dec(v_currNamespace_1368_);
lean_dec(v_maxRecDepth_1366_);
lean_dec(v_currRecDepth_1365_);
lean_dec_ref(v_options_1364_);
lean_dec_ref(v_fileMap_1363_);
lean_dec_ref(v_fileName_1362_);
lean_dec_ref(v_c_1349_);
v___x_1483_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_1367_);
return v___x_1483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts___boxed(lean_object* v_c_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
lean_dec(v_a_1495_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec(v_a_1487_);
lean_dec(v_a_1486_);
lean_dec(v_a_1485_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_ref_1504_; lean_object* v___x_1505_; lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1514_; 
v_ref_1504_ = lean_ctor_get(v___y_1501_, 5);
v___x_1505_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2_spec__5(v_msg_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1514_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1514_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1512_; 
lean_inc(v_ref_1504_);
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v_ref_1504_);
lean_ctor_set(v___x_1510_, 1, v_a_1506_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 1);
lean_ctor_set(v___x_1508_, 0, v___x_1510_);
v___x_1512_ = v___x_1508_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
return v_res_1521_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__0));
v___x_1524_ = l_Lean_stringToMessageData(v___x_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1549_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1549_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1549_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v_leFn_x3f_1542_; 
v_leFn_x3f_1542_ = lean_ctor_get(v_a_1538_, 20);
lean_inc(v_leFn_x3f_1542_);
lean_dec(v_a_1538_);
if (lean_obj_tag(v_leFn_x3f_1542_) == 1)
{
lean_object* v_val_1543_; lean_object* v___x_1545_; 
v_val_1543_ = lean_ctor_get(v_leFn_x3f_1542_, 0);
lean_inc(v_val_1543_);
lean_dec_ref(v_leFn_x3f_1542_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v_val_1543_);
v___x_1545_ = v___x_1540_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_val_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_dec(v_leFn_x3f_1542_);
lean_del_object(v___x_1540_);
v___x_1547_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___closed__1);
v___x_1548_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1547_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
return v___x_1548_;
}
}
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
v_a_1550_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1537_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1537_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1___boxed(lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec(v___y_1558_);
return v_res_1570_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__0));
v___x_1573_ = l_Lean_stringToMessageData(v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1598_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1589_ = v___x_1586_;
v_isShared_1590_ = v_isSharedCheck_1598_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1586_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1598_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v_ltFn_x3f_1591_; 
v_ltFn_x3f_1591_ = lean_ctor_get(v_a_1587_, 21);
lean_inc(v_ltFn_x3f_1591_);
lean_dec(v_a_1587_);
if (lean_obj_tag(v_ltFn_x3f_1591_) == 1)
{
lean_object* v_val_1592_; lean_object* v___x_1594_; 
v_val_1592_ = lean_ctor_get(v_ltFn_x3f_1591_, 0);
lean_inc(v_val_1592_);
lean_dec_ref(v_ltFn_x3f_1591_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v_val_1592_);
v___x_1594_ = v___x_1589_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_val_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_dec(v_ltFn_x3f_1591_);
lean_del_object(v___x_1589_);
v___x_1596_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___closed__1);
v___x_1597_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1596_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
return v___x_1597_;
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_a_1599_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1586_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1586_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2___boxed(lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec(v___y_1607_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(lean_object* v_p_1620_, uint8_t v_strict_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
if (v_strict_1621_ == 0)
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1(v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1636_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
lean_dec_ref(v___x_1634_);
v___x_1636_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1620_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref(v___x_1636_);
v___x_1638_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1648_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1648_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1648_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v_ofNatZero_1643_; lean_object* v___x_1644_; lean_object* v___x_1646_; 
v_ofNatZero_1643_ = lean_ctor_get(v_a_1639_, 18);
lean_inc_ref(v_ofNatZero_1643_);
lean_dec(v_a_1639_);
v___x_1644_ = l_Lean_mkAppB(v_a_1635_, v_a_1637_, v_ofNatZero_1643_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1644_);
v___x_1646_ = v___x_1641_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_a_1637_);
lean_dec(v_a_1635_);
v_a_1649_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1638_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1638_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
else
{
lean_dec(v_a_1635_);
return v___x_1636_;
}
}
else
{
return v___x_1634_;
}
}
else
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__2(v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1659_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref(v___x_1657_);
v___x_1659_ = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0(v_p_1620_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1661_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref(v___x_1659_);
v___x_1661_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1671_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1671_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1671_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v_ofNatZero_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
v_ofNatZero_1666_ = lean_ctor_get(v_a_1662_, 18);
lean_inc_ref(v_ofNatZero_1666_);
lean_dec(v_a_1662_);
v___x_1667_ = l_Lean_mkAppB(v_a_1658_, v_a_1660_, v_ofNatZero_1666_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1667_);
v___x_1669_ = v___x_1664_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec(v_a_1660_);
lean_dec(v_a_1658_);
v_a_1672_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1661_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1661_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
else
{
lean_dec(v_a_1658_);
return v___x_1659_;
}
}
else
{
return v___x_1657_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_p_1680_, lean_object* v_strict_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
uint8_t v_strict_boxed_1694_; lean_object* v_res_1695_; 
v_strict_boxed_1694_ = lean_unbox(v_strict_1681_);
v_res_1695_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1680_, v_strict_boxed_1694_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec(v_p_1680_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(lean_object* v_c_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v_p_1709_; uint8_t v_strict_1710_; lean_object* v___x_1711_; 
v_p_1709_ = lean_ctor_get(v_c_1696_, 0);
v_strict_1710_ = lean_ctor_get_uint8(v_c_1696_, sizeof(void*)*2);
v___x_1711_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0(v_p_1709_, v_strict_1710_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0___boxed(lean_object* v_c_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v_c_1712_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(lean_object* v_a_1726_, lean_object* v_x_1727_, lean_object* v_c_u2081_1728_, lean_object* v_b_1729_, lean_object* v_c_u2082_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v_options_1743_; lean_object* v_p_1744_; lean_object* v_p_1745_; uint8_t v_strict_1746_; lean_object* v_inheritedTraceOptions_1747_; uint8_t v_hasTrace_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v_p_1753_; 
v_options_1743_ = lean_ctor_get(v_a_1740_, 2);
v_p_1744_ = lean_ctor_get(v_c_u2081_1728_, 0);
v_p_1745_ = lean_ctor_get(v_c_u2082_1730_, 0);
v_strict_1746_ = lean_ctor_get_uint8(v_c_u2082_1730_, sizeof(void*)*2);
v_inheritedTraceOptions_1747_ = lean_ctor_get(v_a_1740_, 13);
v_hasTrace_1748_ = lean_ctor_get_uint8(v_options_1743_, sizeof(void*)*1);
v___x_1749_ = lean_nat_to_int(v_a_1726_);
lean_inc(v_p_1745_);
v___x_1750_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1745_, v___x_1749_);
lean_dec(v___x_1749_);
v___x_1751_ = lean_int_neg(v_b_1729_);
lean_inc(v_p_1744_);
v___x_1752_ = l_Lean_Grind_Linarith_Poly_mul(v_p_1744_, v___x_1751_);
lean_dec(v___x_1751_);
v_p_1753_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1750_, v___x_1752_);
if (v_hasTrace_1748_ == 0)
{
goto v___jp_1754_;
}
else
{
lean_object* v_cls_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v_cls_1758_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__1));
v___x_1759_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__2);
v___x_1760_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1747_, v_options_1743_, v___x_1759_);
if (v___x_1760_ == 0)
{
goto v___jp_1754_;
}
else
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1727_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref(v___x_1761_);
v___x_1763_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_u2081_1728_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1765_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref(v___x_1763_);
v___x_1765_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0(v_c_u2082_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref(v___x_1765_);
v___x_1767_ = l_Lean_MessageData_ofExpr(v_a_1762_);
v___x_1768_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_1769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
v___x_1770_ = l_Lean_MessageData_ofExpr(v_a_1764_);
v___x_1771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1769_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
lean_ctor_set(v___x_1772_, 1, v___x_1768_);
v___x_1773_ = l_Lean_MessageData_ofExpr(v_a_1766_);
v___x_1774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1772_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_1758_, v___x_1774_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_dec_ref(v___x_1775_);
goto v___jp_1754_;
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_dec(v_p_1753_);
lean_dec_ref(v_c_u2082_1730_);
lean_dec_ref(v_c_u2081_1728_);
lean_dec(v_x_1727_);
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
lean_dec(v_p_1753_);
lean_dec_ref(v_c_u2082_1730_);
lean_dec_ref(v_c_u2081_1728_);
lean_dec(v_x_1727_);
v_a_1784_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1765_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1765_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_dec(v_a_1762_);
lean_dec(v_p_1753_);
lean_dec_ref(v_c_u2082_1730_);
lean_dec_ref(v_c_u2081_1728_);
lean_dec(v_x_1727_);
v_a_1792_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1763_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1763_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec(v_p_1753_);
lean_dec_ref(v_c_u2082_1730_);
lean_dec_ref(v_c_u2081_1728_);
lean_dec(v_x_1727_);
v_a_1800_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1761_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1761_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
v___jp_1754_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = lean_alloc_ctor(13, 3, 0);
lean_ctor_set(v___x_1755_, 0, v_x_1727_);
lean_ctor_set(v___x_1755_, 1, v_c_u2081_1728_);
lean_ctor_set(v___x_1755_, 2, v_c_u2082_1730_);
v___x_1756_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1756_, 0, v_p_1753_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
lean_ctor_set_uint8(v___x_1756_, sizeof(void*)*2, v_strict_1746_);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
return v___x_1757_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq___boxed(lean_object** _args){
lean_object* v_a_1808_ = _args[0];
lean_object* v_x_1809_ = _args[1];
lean_object* v_c_u2081_1810_ = _args[2];
lean_object* v_b_1811_ = _args[3];
lean_object* v_c_u2082_1812_ = _args[4];
lean_object* v_a_1813_ = _args[5];
lean_object* v_a_1814_ = _args[6];
lean_object* v_a_1815_ = _args[7];
lean_object* v_a_1816_ = _args[8];
lean_object* v_a_1817_ = _args[9];
lean_object* v_a_1818_ = _args[10];
lean_object* v_a_1819_ = _args[11];
lean_object* v_a_1820_ = _args[12];
lean_object* v_a_1821_ = _args[13];
lean_object* v_a_1822_ = _args[14];
lean_object* v_a_1823_ = _args[15];
lean_object* v_a_1824_ = _args[16];
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1808_, v_x_1809_, v_c_u2081_1810_, v_b_1811_, v_c_u2082_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
lean_dec(v_a_1823_);
lean_dec_ref(v_a_1822_);
lean_dec(v_a_1821_);
lean_dec_ref(v_a_1820_);
lean_dec(v_a_1819_);
lean_dec_ref(v_a_1818_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
lean_dec(v_a_1815_);
lean_dec(v_a_1814_);
lean_dec(v_a_1813_);
lean_dec(v_b_1811_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1826_, lean_object* v_msg_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1827_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1841_, lean_object* v_msg_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1841_, v_msg_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec(v___y_1843_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(lean_object* v_a_1864_, lean_object* v_x_1865_, lean_object* v_c_u2081_1866_, lean_object* v_as_1867_, size_t v_sz_1868_, size_t v_i_1869_, lean_object* v_b_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
uint8_t v___x_1883_; 
v___x_1883_ = lean_usize_dec_lt(v_i_1869_, v_sz_1868_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; 
lean_dec_ref(v_c_u2081_1866_);
lean_dec(v_x_1865_);
lean_dec(v_a_1864_);
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v_b_1870_);
return v___x_1884_;
}
else
{
lean_object* v_a_1885_; lean_object* v_fst_1886_; lean_object* v_snd_1887_; lean_object* v___x_1888_; 
lean_dec_ref(v_b_1870_);
v_a_1885_ = lean_array_uget_borrowed(v_as_1867_, v_i_1869_);
v_fst_1886_ = lean_ctor_get(v_a_1885_, 0);
v_snd_1887_ = lean_ctor_get(v_a_1885_, 1);
lean_inc(v_snd_1887_);
lean_inc_ref(v_c_u2081_1866_);
lean_inc(v_x_1865_);
lean_inc(v_a_1864_);
v___x_1888_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_IneqCnstr_applyEq(v_a_1864_, v_x_1865_, v_c_u2081_1866_, v_fst_1886_, v_snd_1887_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1890_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref(v___x_1888_);
v___x_1890_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v_a_1889_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v___x_1891_; 
lean_dec_ref(v___x_1890_);
v___x_1891_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1905_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1894_ = v___x_1891_;
v_isShared_1895_ = v_isSharedCheck_1905_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1891_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1905_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
uint8_t v___x_1896_; 
v___x_1896_ = lean_unbox(v_a_1892_);
lean_dec(v_a_1892_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; size_t v___x_1898_; size_t v___x_1899_; 
lean_del_object(v___x_1894_);
v___x_1897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v___x_1898_ = ((size_t)1ULL);
v___x_1899_ = lean_usize_add(v_i_1869_, v___x_1898_);
v_i_1869_ = v___x_1899_;
v_b_1870_ = v___x_1897_;
goto _start;
}
else
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
lean_dec_ref(v_c_u2081_1866_);
lean_dec(v_x_1865_);
lean_dec(v_a_1864_);
v___x_1901_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v___x_1901_);
v___x_1903_ = v___x_1894_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec_ref(v_c_u2081_1866_);
lean_dec(v_x_1865_);
lean_dec(v_a_1864_);
v_a_1906_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1891_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1891_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec_ref(v_c_u2081_1866_);
lean_dec(v_x_1865_);
lean_dec(v_a_1864_);
v_a_1914_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1890_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1890_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec_ref(v_c_u2081_1866_);
lean_dec(v_x_1865_);
lean_dec(v_a_1864_);
v_a_1922_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1888_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1888_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___boxed(lean_object** _args){
lean_object* v_a_1930_ = _args[0];
lean_object* v_x_1931_ = _args[1];
lean_object* v_c_u2081_1932_ = _args[2];
lean_object* v_as_1933_ = _args[3];
lean_object* v_sz_1934_ = _args[4];
lean_object* v_i_1935_ = _args[5];
lean_object* v_b_1936_ = _args[6];
lean_object* v___y_1937_ = _args[7];
lean_object* v___y_1938_ = _args[8];
lean_object* v___y_1939_ = _args[9];
lean_object* v___y_1940_ = _args[10];
lean_object* v___y_1941_ = _args[11];
lean_object* v___y_1942_ = _args[12];
lean_object* v___y_1943_ = _args[13];
lean_object* v___y_1944_ = _args[14];
lean_object* v___y_1945_ = _args[15];
lean_object* v___y_1946_ = _args[16];
lean_object* v___y_1947_ = _args[17];
lean_object* v___y_1948_ = _args[18];
_start:
{
size_t v_sz_boxed_1949_; size_t v_i_boxed_1950_; lean_object* v_res_1951_; 
v_sz_boxed_1949_ = lean_unbox_usize(v_sz_1934_);
lean_dec(v_sz_1934_);
v_i_boxed_1950_ = lean_unbox_usize(v_i_1935_);
lean_dec(v_i_1935_);
v_res_1951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1930_, v_x_1931_, v_c_u2081_1932_, v_as_1933_, v_sz_boxed_1949_, v_i_boxed_1950_, v_b_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v_as_1933_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(lean_object* v_a_1952_, lean_object* v_x_1953_, lean_object* v_c_u2081_1954_, lean_object* v_todo_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; size_t v_sz_1970_; size_t v___x_1971_; lean_object* v___x_1972_; 
v___x_1968_ = lean_box(0);
v___x_1969_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_1970_ = lean_array_size(v_todo_1955_);
v___x_1971_ = ((size_t)0ULL);
v___x_1972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0(v_a_1952_, v_x_1953_, v_c_u2081_1954_, v_todo_1955_, v_sz_1970_, v___x_1971_, v___x_1969_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1985_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_1985_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1985_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v_fst_1977_; 
v_fst_1977_ = lean_ctor_get(v_a_1973_, 0);
lean_inc(v_fst_1977_);
lean_dec(v_a_1973_);
if (lean_obj_tag(v_fst_1977_) == 0)
{
lean_object* v___x_1979_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1968_);
v___x_1979_ = v___x_1975_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1968_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
else
{
lean_object* v_val_1981_; lean_object* v___x_1983_; 
v_val_1981_ = lean_ctor_get(v_fst_1977_, 0);
lean_inc(v_val_1981_);
lean_dec_ref(v_fst_1977_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v_val_1981_);
v___x_1983_ = v___x_1975_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_val_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
v_a_1986_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1972_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1972_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs___boxed(lean_object* v_a_1994_, lean_object* v_x_1995_, lean_object* v_c_u2081_1996_, lean_object* v_todo_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_1994_, v_x_1995_, v_c_u2081_1996_, v_todo_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
lean_dec(v_a_2006_);
lean_dec_ref(v_a_2005_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_todo_1997_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_2011_, lean_object* v_as_2012_, size_t v_sz_2013_, size_t v_i_2014_, lean_object* v_b_2015_){
_start:
{
uint8_t v___x_2016_; 
v___x_2016_ = lean_usize_dec_lt(v_i_2014_, v_sz_2013_);
if (v___x_2016_ == 0)
{
return v_b_2015_;
}
else
{
lean_object* v_snd_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2050_; 
v_snd_2017_ = lean_ctor_get(v_b_2015_, 1);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_b_2015_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; 
v_unused_2051_ = lean_ctor_get(v_b_2015_, 0);
lean_dec(v_unused_2051_);
v___x_2019_ = v_b_2015_;
v_isShared_2020_ = v_isSharedCheck_2050_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_snd_2017_);
lean_dec(v_b_2015_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2050_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v_fst_2021_; lean_object* v_snd_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2049_; 
v_fst_2021_ = lean_ctor_get(v_snd_2017_, 0);
v_snd_2022_ = lean_ctor_get(v_snd_2017_, 1);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_snd_2017_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2024_ = v_snd_2017_;
v_isShared_2025_ = v_isSharedCheck_2049_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_snd_2022_);
lean_inc(v_fst_2021_);
lean_dec(v_snd_2017_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2049_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v_a_2026_; lean_object* v_p_2027_; lean_object* v___x_2028_; lean_object* v_a_2030_; lean_object* v_b_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
v_a_2026_ = lean_array_uget_borrowed(v_as_2012_, v_i_2014_);
v_p_2027_ = lean_ctor_get(v_a_2026_, 0);
v___x_2028_ = lean_box(0);
v_b_2037_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2027_, v_x_2011_);
v___x_2038_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2039_ = lean_int_dec_eq(v_b_2037_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2041_; 
lean_inc(v_a_2026_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 1, v_a_2026_);
lean_ctor_set(v___x_2019_, 0, v_b_2037_);
v___x_2041_ = v___x_2019_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_b_2037_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_a_2026_);
v___x_2041_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v_todo_2042_; lean_object* v___x_2043_; 
v_todo_2042_ = lean_array_push(v_snd_2022_, v___x_2041_);
v___x_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2043_, 0, v_fst_2021_);
lean_ctor_set(v___x_2043_, 1, v_todo_2042_);
v_a_2030_ = v___x_2043_;
goto v___jp_2029_;
}
}
else
{
lean_object* v_cs_x27_2045_; lean_object* v___x_2047_; 
lean_dec(v_b_2037_);
lean_inc(v_a_2026_);
v_cs_x27_2045_ = l_Lean_PersistentArray_push___redArg(v_fst_2021_, v_a_2026_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 1, v_snd_2022_);
lean_ctor_set(v___x_2019_, 0, v_cs_x27_2045_);
v___x_2047_ = v___x_2019_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_cs_x27_2045_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_snd_2022_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
v_a_2030_ = v___x_2047_;
goto v___jp_2029_;
}
}
v___jp_2029_:
{
lean_object* v___x_2032_; 
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 1, v_a_2030_);
lean_ctor_set(v___x_2024_, 0, v___x_2028_);
v___x_2032_ = v___x_2024_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_a_2030_);
v___x_2032_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
size_t v___x_2033_; size_t v___x_2034_; 
v___x_2033_ = ((size_t)1ULL);
v___x_2034_ = lean_usize_add(v_i_2014_, v___x_2033_);
v_i_2014_ = v___x_2034_;
v_b_2015_ = v___x_2032_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_2052_, lean_object* v_as_2053_, lean_object* v_sz_2054_, lean_object* v_i_2055_, lean_object* v_b_2056_){
_start:
{
size_t v_sz_boxed_2057_; size_t v_i_boxed_2058_; lean_object* v_res_2059_; 
v_sz_boxed_2057_ = lean_unbox_usize(v_sz_2054_);
lean_dec(v_sz_2054_);
v_i_boxed_2058_ = lean_unbox_usize(v_i_2055_);
lean_dec(v_i_2055_);
v_res_2059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2052_, v_as_2053_, v_sz_boxed_2057_, v_i_boxed_2058_, v_b_2056_);
lean_dec_ref(v_as_2053_);
lean_dec(v_x_2052_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(lean_object* v_x_2060_, lean_object* v_as_2061_, size_t v_sz_2062_, size_t v_i_2063_, lean_object* v_b_2064_){
_start:
{
uint8_t v___x_2065_; 
v___x_2065_ = lean_usize_dec_lt(v_i_2063_, v_sz_2062_);
if (v___x_2065_ == 0)
{
return v_b_2064_;
}
else
{
lean_object* v_snd_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2099_; 
v_snd_2066_ = lean_ctor_get(v_b_2064_, 1);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_b_2064_);
if (v_isSharedCheck_2099_ == 0)
{
lean_object* v_unused_2100_; 
v_unused_2100_ = lean_ctor_get(v_b_2064_, 0);
lean_dec(v_unused_2100_);
v___x_2068_ = v_b_2064_;
v_isShared_2069_ = v_isSharedCheck_2099_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_snd_2066_);
lean_dec(v_b_2064_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2099_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v_fst_2070_; lean_object* v_snd_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2098_; 
v_fst_2070_ = lean_ctor_get(v_snd_2066_, 0);
v_snd_2071_ = lean_ctor_get(v_snd_2066_, 1);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_snd_2066_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2073_ = v_snd_2066_;
v_isShared_2074_ = v_isSharedCheck_2098_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_snd_2071_);
lean_inc(v_fst_2070_);
lean_dec(v_snd_2066_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2098_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v_a_2075_; lean_object* v_p_2076_; lean_object* v___x_2077_; lean_object* v_a_2079_; lean_object* v_b_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
v_a_2075_ = lean_array_uget_borrowed(v_as_2061_, v_i_2063_);
v_p_2076_ = lean_ctor_get(v_a_2075_, 0);
v___x_2077_ = lean_box(0);
v_b_2086_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2076_, v_x_2060_);
v___x_2087_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2088_ = lean_int_dec_eq(v_b_2086_, v___x_2087_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2090_; 
lean_inc(v_a_2075_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 1, v_a_2075_);
lean_ctor_set(v___x_2068_, 0, v_b_2086_);
v___x_2090_ = v___x_2068_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_b_2086_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_a_2075_);
v___x_2090_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v_todo_2091_; lean_object* v___x_2092_; 
v_todo_2091_ = lean_array_push(v_snd_2071_, v___x_2090_);
v___x_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2092_, 0, v_fst_2070_);
lean_ctor_set(v___x_2092_, 1, v_todo_2091_);
v_a_2079_ = v___x_2092_;
goto v___jp_2078_;
}
}
else
{
lean_object* v_cs_x27_2094_; lean_object* v___x_2096_; 
lean_dec(v_b_2086_);
lean_inc(v_a_2075_);
v_cs_x27_2094_ = l_Lean_PersistentArray_push___redArg(v_fst_2070_, v_a_2075_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 1, v_snd_2071_);
lean_ctor_set(v___x_2068_, 0, v_cs_x27_2094_);
v___x_2096_ = v___x_2068_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_cs_x27_2094_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_snd_2071_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
v_a_2079_ = v___x_2096_;
goto v___jp_2078_;
}
}
v___jp_2078_:
{
lean_object* v___x_2081_; 
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 1, v_a_2079_);
lean_ctor_set(v___x_2073_, 0, v___x_2077_);
v___x_2081_ = v___x_2073_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_a_2079_);
v___x_2081_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
size_t v___x_2082_; size_t v___x_2083_; lean_object* v___x_2084_; 
v___x_2082_ = ((size_t)1ULL);
v___x_2083_ = lean_usize_add(v_i_2063_, v___x_2082_);
v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2_spec__5(v_x_2060_, v_as_2061_, v_sz_2062_, v___x_2083_, v___x_2081_);
return v___x_2084_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2101_, lean_object* v_as_2102_, lean_object* v_sz_2103_, lean_object* v_i_2104_, lean_object* v_b_2105_){
_start:
{
size_t v_sz_boxed_2106_; size_t v_i_boxed_2107_; lean_object* v_res_2108_; 
v_sz_boxed_2106_ = lean_unbox_usize(v_sz_2103_);
lean_dec(v_sz_2103_);
v_i_boxed_2107_ = lean_unbox_usize(v_i_2104_);
lean_dec(v_i_2104_);
v_res_2108_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2101_, v_as_2102_, v_sz_boxed_2106_, v_i_boxed_2107_, v_b_2105_);
lean_dec_ref(v_as_2102_);
lean_dec(v_x_2101_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_2109_, lean_object* v_as_2110_, size_t v_sz_2111_, size_t v_i_2112_, lean_object* v_b_2113_){
_start:
{
uint8_t v___x_2114_; 
v___x_2114_ = lean_usize_dec_lt(v_i_2112_, v_sz_2111_);
if (v___x_2114_ == 0)
{
return v_b_2113_;
}
else
{
lean_object* v_snd_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2148_; 
v_snd_2115_ = lean_ctor_get(v_b_2113_, 1);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_b_2113_);
if (v_isSharedCheck_2148_ == 0)
{
lean_object* v_unused_2149_; 
v_unused_2149_ = lean_ctor_get(v_b_2113_, 0);
lean_dec(v_unused_2149_);
v___x_2117_ = v_b_2113_;
v_isShared_2118_ = v_isSharedCheck_2148_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_snd_2115_);
lean_dec(v_b_2113_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2148_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v_fst_2119_; lean_object* v_snd_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2147_; 
v_fst_2119_ = lean_ctor_get(v_snd_2115_, 0);
v_snd_2120_ = lean_ctor_get(v_snd_2115_, 1);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_snd_2115_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2122_ = v_snd_2115_;
v_isShared_2123_ = v_isSharedCheck_2147_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_snd_2120_);
lean_inc(v_fst_2119_);
lean_dec(v_snd_2115_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2147_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v_a_2124_; lean_object* v_p_2125_; lean_object* v___x_2126_; lean_object* v_a_2128_; lean_object* v_b_2135_; lean_object* v___x_2136_; uint8_t v___x_2137_; 
v_a_2124_ = lean_array_uget_borrowed(v_as_2110_, v_i_2112_);
v_p_2125_ = lean_ctor_get(v_a_2124_, 0);
v___x_2126_ = lean_box(0);
v_b_2135_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2125_, v_x_2109_);
v___x_2136_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2137_ = lean_int_dec_eq(v_b_2135_, v___x_2136_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2139_; 
lean_inc(v_a_2124_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 1, v_a_2124_);
lean_ctor_set(v___x_2117_, 0, v_b_2135_);
v___x_2139_ = v___x_2117_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_b_2135_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_a_2124_);
v___x_2139_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v_todo_2140_; lean_object* v___x_2141_; 
v_todo_2140_ = lean_array_push(v_snd_2120_, v___x_2139_);
v___x_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2141_, 0, v_fst_2119_);
lean_ctor_set(v___x_2141_, 1, v_todo_2140_);
v_a_2128_ = v___x_2141_;
goto v___jp_2127_;
}
}
else
{
lean_object* v_cs_x27_2143_; lean_object* v___x_2145_; 
lean_dec(v_b_2135_);
lean_inc(v_a_2124_);
v_cs_x27_2143_ = l_Lean_PersistentArray_push___redArg(v_fst_2119_, v_a_2124_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 1, v_snd_2120_);
lean_ctor_set(v___x_2117_, 0, v_cs_x27_2143_);
v___x_2145_ = v___x_2117_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_cs_x27_2143_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_snd_2120_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
v_a_2128_ = v___x_2145_;
goto v___jp_2127_;
}
}
v___jp_2127_:
{
lean_object* v___x_2130_; 
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 1, v_a_2128_);
lean_ctor_set(v___x_2122_, 0, v___x_2126_);
v___x_2130_ = v___x_2122_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_a_2128_);
v___x_2130_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
size_t v___x_2131_; size_t v___x_2132_; 
v___x_2131_ = ((size_t)1ULL);
v___x_2132_ = lean_usize_add(v_i_2112_, v___x_2131_);
v_i_2112_ = v___x_2132_;
v_b_2113_ = v___x_2130_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_2150_, lean_object* v_as_2151_, lean_object* v_sz_2152_, lean_object* v_i_2153_, lean_object* v_b_2154_){
_start:
{
size_t v_sz_boxed_2155_; size_t v_i_boxed_2156_; lean_object* v_res_2157_; 
v_sz_boxed_2155_ = lean_unbox_usize(v_sz_2152_);
lean_dec(v_sz_2152_);
v_i_boxed_2156_ = lean_unbox_usize(v_i_2153_);
lean_dec(v_i_2153_);
v_res_2157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2150_, v_as_2151_, v_sz_boxed_2155_, v_i_boxed_2156_, v_b_2154_);
lean_dec_ref(v_as_2151_);
lean_dec(v_x_2150_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2158_, lean_object* v_as_2159_, size_t v_sz_2160_, size_t v_i_2161_, lean_object* v_b_2162_){
_start:
{
uint8_t v___x_2163_; 
v___x_2163_ = lean_usize_dec_lt(v_i_2161_, v_sz_2160_);
if (v___x_2163_ == 0)
{
return v_b_2162_;
}
else
{
lean_object* v_snd_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2197_; 
v_snd_2164_ = lean_ctor_get(v_b_2162_, 1);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_b_2162_);
if (v_isSharedCheck_2197_ == 0)
{
lean_object* v_unused_2198_; 
v_unused_2198_ = lean_ctor_get(v_b_2162_, 0);
lean_dec(v_unused_2198_);
v___x_2166_ = v_b_2162_;
v_isShared_2167_ = v_isSharedCheck_2197_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_snd_2164_);
lean_dec(v_b_2162_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2197_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v_fst_2168_; lean_object* v_snd_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2196_; 
v_fst_2168_ = lean_ctor_get(v_snd_2164_, 0);
v_snd_2169_ = lean_ctor_get(v_snd_2164_, 1);
v_isSharedCheck_2196_ = !lean_is_exclusive(v_snd_2164_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2171_ = v_snd_2164_;
v_isShared_2172_ = v_isSharedCheck_2196_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_snd_2169_);
lean_inc(v_fst_2168_);
lean_dec(v_snd_2164_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2196_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v_a_2173_; lean_object* v_p_2174_; lean_object* v___x_2175_; lean_object* v_a_2177_; lean_object* v_b_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; 
v_a_2173_ = lean_array_uget_borrowed(v_as_2159_, v_i_2161_);
v_p_2174_ = lean_ctor_get(v_a_2173_, 0);
v___x_2175_ = lean_box(0);
v_b_2184_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2174_, v_x_2158_);
v___x_2185_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_2186_ = lean_int_dec_eq(v_b_2184_, v___x_2185_);
if (v___x_2186_ == 0)
{
lean_object* v___x_2188_; 
lean_inc(v_a_2173_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 1, v_a_2173_);
lean_ctor_set(v___x_2166_, 0, v_b_2184_);
v___x_2188_ = v___x_2166_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_b_2184_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_a_2173_);
v___x_2188_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
lean_object* v_todo_2189_; lean_object* v___x_2190_; 
v_todo_2189_ = lean_array_push(v_snd_2169_, v___x_2188_);
v___x_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2190_, 0, v_fst_2168_);
lean_ctor_set(v___x_2190_, 1, v_todo_2189_);
v_a_2177_ = v___x_2190_;
goto v___jp_2176_;
}
}
else
{
lean_object* v_cs_x27_2192_; lean_object* v___x_2194_; 
lean_dec(v_b_2184_);
lean_inc(v_a_2173_);
v_cs_x27_2192_ = l_Lean_PersistentArray_push___redArg(v_fst_2168_, v_a_2173_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 1, v_snd_2169_);
lean_ctor_set(v___x_2166_, 0, v_cs_x27_2192_);
v___x_2194_ = v___x_2166_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_cs_x27_2192_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_snd_2169_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
v_a_2177_ = v___x_2194_;
goto v___jp_2176_;
}
}
v___jp_2176_:
{
lean_object* v___x_2179_; 
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 1, v_a_2177_);
lean_ctor_set(v___x_2171_, 0, v___x_2175_);
v___x_2179_ = v___x_2171_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2175_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_a_2177_);
v___x_2179_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
size_t v___x_2180_; size_t v___x_2181_; lean_object* v___x_2182_; 
v___x_2180_ = ((size_t)1ULL);
v___x_2181_ = lean_usize_add(v_i_2161_, v___x_2180_);
v___x_2182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_2158_, v_as_2159_, v_sz_2160_, v___x_2181_, v___x_2179_);
return v___x_2182_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_2199_, lean_object* v_as_2200_, lean_object* v_sz_2201_, lean_object* v_i_2202_, lean_object* v_b_2203_){
_start:
{
size_t v_sz_boxed_2204_; size_t v_i_boxed_2205_; lean_object* v_res_2206_; 
v_sz_boxed_2204_ = lean_unbox_usize(v_sz_2201_);
lean_dec(v_sz_2201_);
v_i_boxed_2205_ = lean_unbox_usize(v_i_2202_);
lean_dec(v_i_2202_);
v_res_2206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2199_, v_as_2200_, v_sz_boxed_2204_, v_i_boxed_2205_, v_b_2203_);
lean_dec_ref(v_as_2200_);
lean_dec(v_x_2199_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(lean_object* v_init_2207_, lean_object* v_x_2208_, lean_object* v_n_2209_, lean_object* v_b_2210_){
_start:
{
if (lean_obj_tag(v_n_2209_) == 0)
{
lean_object* v_cs_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2226_; 
v_cs_2211_ = lean_ctor_get(v_n_2209_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_n_2209_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2213_ = v_n_2209_;
v_isShared_2214_ = v_isSharedCheck_2226_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_cs_2211_);
lean_dec(v_n_2209_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2226_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; size_t v_sz_2217_; size_t v___x_2218_; lean_object* v___x_2219_; lean_object* v_fst_2220_; 
v___x_2215_ = lean_box(0);
v___x_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
lean_ctor_set(v___x_2216_, 1, v_b_2210_);
v_sz_2217_ = lean_array_size(v_cs_2211_);
v___x_2218_ = ((size_t)0ULL);
v___x_2219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2207_, v_x_2208_, v_cs_2211_, v_sz_2217_, v___x_2218_, v___x_2216_);
lean_dec_ref(v_cs_2211_);
v_fst_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_fst_2220_);
if (lean_obj_tag(v_fst_2220_) == 0)
{
lean_object* v_snd_2221_; lean_object* v___x_2223_; 
v_snd_2221_ = lean_ctor_get(v___x_2219_, 1);
lean_inc(v_snd_2221_);
lean_dec_ref(v___x_2219_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set_tag(v___x_2213_, 1);
lean_ctor_set(v___x_2213_, 0, v_snd_2221_);
v___x_2223_ = v___x_2213_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_snd_2221_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
else
{
lean_object* v_val_2225_; 
lean_dec_ref(v___x_2219_);
lean_del_object(v___x_2213_);
v_val_2225_ = lean_ctor_get(v_fst_2220_, 0);
lean_inc(v_val_2225_);
lean_dec_ref(v_fst_2220_);
return v_val_2225_;
}
}
}
else
{
lean_object* v_vs_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2242_; 
v_vs_2227_ = lean_ctor_get(v_n_2209_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_n_2209_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2229_ = v_n_2209_;
v_isShared_2230_ = v_isSharedCheck_2242_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_vs_2227_);
lean_dec(v_n_2209_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2242_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; size_t v_sz_2233_; size_t v___x_2234_; lean_object* v___x_2235_; lean_object* v_fst_2236_; 
v___x_2231_ = lean_box(0);
v___x_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v_b_2210_);
v_sz_2233_ = lean_array_size(v_vs_2227_);
v___x_2234_ = ((size_t)0ULL);
v___x_2235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__3(v_x_2208_, v_vs_2227_, v_sz_2233_, v___x_2234_, v___x_2232_);
lean_dec_ref(v_vs_2227_);
v_fst_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_fst_2236_);
if (lean_obj_tag(v_fst_2236_) == 0)
{
lean_object* v_snd_2237_; lean_object* v___x_2239_; 
v_snd_2237_ = lean_ctor_get(v___x_2235_, 1);
lean_inc(v_snd_2237_);
lean_dec_ref(v___x_2235_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v_snd_2237_);
v___x_2239_ = v___x_2229_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_snd_2237_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
else
{
lean_object* v_val_2241_; 
lean_dec_ref(v___x_2235_);
lean_del_object(v___x_2229_);
v_val_2241_ = lean_ctor_get(v_fst_2236_, 0);
lean_inc(v_val_2241_);
lean_dec_ref(v_fst_2236_);
return v_val_2241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_2243_, lean_object* v_x_2244_, lean_object* v_as_2245_, size_t v_sz_2246_, size_t v_i_2247_, lean_object* v_b_2248_){
_start:
{
uint8_t v___x_2249_; 
v___x_2249_ = lean_usize_dec_lt(v_i_2247_, v_sz_2246_);
if (v___x_2249_ == 0)
{
return v_b_2248_;
}
else
{
lean_object* v_snd_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2268_; 
v_snd_2250_ = lean_ctor_get(v_b_2248_, 1);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_b_2248_);
if (v_isSharedCheck_2268_ == 0)
{
lean_object* v_unused_2269_; 
v_unused_2269_ = lean_ctor_get(v_b_2248_, 0);
lean_dec(v_unused_2269_);
v___x_2252_ = v_b_2248_;
v_isShared_2253_ = v_isSharedCheck_2268_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_snd_2250_);
lean_dec(v_b_2248_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2268_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v_a_2254_; lean_object* v___x_2255_; 
v_a_2254_ = lean_array_uget_borrowed(v_as_2245_, v_i_2247_);
lean_inc(v_snd_2250_);
lean_inc(v_a_2254_);
v___x_2255_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2243_, v_x_2244_, v_a_2254_, v_snd_2250_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v___x_2256_; lean_object* v___x_2258_; 
v___x_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v___x_2256_);
v___x_2258_ = v___x_2252_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v_snd_2250_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2261_; lean_object* v___x_2263_; 
lean_dec(v_snd_2250_);
v_a_2260_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_a_2260_);
lean_dec_ref(v___x_2255_);
v___x_2261_ = lean_box(0);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 1, v_a_2260_);
lean_ctor_set(v___x_2252_, 0, v___x_2261_);
v___x_2263_ = v___x_2252_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2261_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v_a_2260_);
v___x_2263_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
size_t v___x_2264_; size_t v___x_2265_; 
v___x_2264_ = ((size_t)1ULL);
v___x_2265_ = lean_usize_add(v_i_2247_, v___x_2264_);
v_i_2247_ = v___x_2265_;
v_b_2248_ = v___x_2263_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_2270_, lean_object* v_x_2271_, lean_object* v_as_2272_, lean_object* v_sz_2273_, lean_object* v_i_2274_, lean_object* v_b_2275_){
_start:
{
size_t v_sz_boxed_2276_; size_t v_i_boxed_2277_; lean_object* v_res_2278_; 
v_sz_boxed_2276_ = lean_unbox_usize(v_sz_2273_);
lean_dec(v_sz_2273_);
v_i_boxed_2277_ = lean_unbox_usize(v_i_2274_);
lean_dec(v_i_2274_);
v_res_2278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1_spec__2(v_init_2270_, v_x_2271_, v_as_2272_, v_sz_boxed_2276_, v_i_boxed_2277_, v_b_2275_);
lean_dec_ref(v_as_2272_);
lean_dec(v_x_2271_);
lean_dec_ref(v_init_2270_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_2279_, lean_object* v_x_2280_, lean_object* v_n_2281_, lean_object* v_b_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2279_, v_x_2280_, v_n_2281_, v_b_2282_);
lean_dec(v_x_2280_);
lean_dec_ref(v_init_2279_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(lean_object* v_x_2284_, lean_object* v_t_2285_, lean_object* v_init_2286_){
_start:
{
lean_object* v_root_2287_; lean_object* v_tail_2288_; lean_object* v___x_2289_; 
v_root_2287_ = lean_ctor_get(v_t_2285_, 0);
lean_inc_ref(v_root_2287_);
v_tail_2288_ = lean_ctor_get(v_t_2285_, 1);
lean_inc_ref(v_tail_2288_);
lean_dec_ref(v_t_2285_);
lean_inc_ref(v_init_2286_);
v___x_2289_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__1(v_init_2286_, v_x_2284_, v_root_2287_, v_init_2286_);
lean_dec_ref(v_init_2286_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; 
lean_dec_ref(v_tail_2288_);
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref(v___x_2289_);
return v_a_2290_;
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; size_t v_sz_2294_; size_t v___x_2295_; lean_object* v___x_2296_; lean_object* v_fst_2297_; 
v_a_2291_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2291_);
lean_dec_ref(v___x_2289_);
v___x_2292_ = lean_box(0);
v___x_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
lean_ctor_set(v___x_2293_, 1, v_a_2291_);
v_sz_2294_ = lean_array_size(v_tail_2288_);
v___x_2295_ = ((size_t)0ULL);
v___x_2296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0_spec__2(v_x_2284_, v_tail_2288_, v_sz_2294_, v___x_2295_, v___x_2293_);
lean_dec_ref(v_tail_2288_);
v_fst_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_fst_2297_);
if (lean_obj_tag(v_fst_2297_) == 0)
{
lean_object* v_snd_2298_; 
v_snd_2298_ = lean_ctor_get(v___x_2296_, 1);
lean_inc(v_snd_2298_);
lean_dec_ref(v___x_2296_);
return v_snd_2298_;
}
else
{
lean_object* v_val_2299_; 
lean_dec_ref(v___x_2296_);
v_val_2299_ = lean_ctor_get(v_fst_2297_, 0);
lean_inc(v_val_2299_);
lean_dec_ref(v_fst_2297_);
return v_val_2299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0___boxed(lean_object* v_x_2300_, lean_object* v_t_2301_, lean_object* v_init_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2300_, v_t_2301_, v_init_2302_);
lean_dec(v_x_2300_);
return v_res_2303_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2304_ = lean_unsigned_to_nat(32u);
v___x_2305_ = lean_mk_empty_array_with_capacity(v___x_2304_);
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
return v___x_2306_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1(void){
_start:
{
size_t v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v_cs_x27_2312_; 
v___x_2307_ = ((size_t)5ULL);
v___x_2308_ = lean_unsigned_to_nat(0u);
v___x_2309_ = lean_unsigned_to_nat(32u);
v___x_2310_ = lean_mk_empty_array_with_capacity(v___x_2309_);
v___x_2311_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__0);
v_cs_x27_2312_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_2312_, 0, v___x_2311_);
lean_ctor_set(v_cs_x27_2312_, 1, v___x_2310_);
lean_ctor_set(v_cs_x27_2312_, 2, v___x_2308_);
lean_ctor_set(v_cs_x27_2312_, 3, v___x_2308_);
lean_ctor_set_usize(v_cs_x27_2312_, 4, v___x_2307_);
return v_cs_x27_2312_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_2315_; lean_object* v_cs_x27_2316_; lean_object* v___x_2317_; 
v_todo_2315_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__2));
v_cs_x27_2316_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__1);
v___x_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2317_, 0, v_cs_x27_2316_);
lean_ctor_set(v___x_2317_, 1, v_todo_2315_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(lean_object* v_x_2318_, lean_object* v_cs_2319_){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v_fst_2322_; lean_object* v_snd_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
v___x_2320_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___closed__3);
v___x_2321_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0_spec__0(v_x_2318_, v_cs_2319_, v___x_2320_);
v_fst_2322_ = lean_ctor_get(v___x_2321_, 0);
v_snd_2323_ = lean_ctor_get(v___x_2321_, 1);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2321_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_snd_2323_);
lean_inc(v_fst_2322_);
lean_dec(v___x_2321_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_fst_2322_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v_snd_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0___boxed(lean_object* v_x_2331_, lean_object* v_cs_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2331_, v_cs_2332_);
lean_dec(v_x_2331_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(lean_object* v_x_2334_, lean_object* v_cs_2335_){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2334_, v_cs_2335_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs___boxed(lean_object* v_x_2337_, lean_object* v_cs_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs(v_x_2337_, v_cs_2338_);
lean_dec(v_x_2337_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(lean_object* v_a_2340_, lean_object* v_y_2341_, lean_object* v_fst_2342_, lean_object* v_s_2343_){
_start:
{
lean_object* v_structs_2344_; lean_object* v_typeIdOf_2345_; lean_object* v_exprToStructId_2346_; lean_object* v_exprToStructIdEntries_2347_; lean_object* v_forbiddenNatModules_2348_; lean_object* v_natStructs_2349_; lean_object* v_natTypeIdOf_2350_; lean_object* v_exprToNatStructId_2351_; lean_object* v___x_2352_; uint8_t v___x_2353_; 
v_structs_2344_ = lean_ctor_get(v_s_2343_, 0);
v_typeIdOf_2345_ = lean_ctor_get(v_s_2343_, 1);
v_exprToStructId_2346_ = lean_ctor_get(v_s_2343_, 2);
v_exprToStructIdEntries_2347_ = lean_ctor_get(v_s_2343_, 3);
v_forbiddenNatModules_2348_ = lean_ctor_get(v_s_2343_, 4);
v_natStructs_2349_ = lean_ctor_get(v_s_2343_, 5);
v_natTypeIdOf_2350_ = lean_ctor_get(v_s_2343_, 6);
v_exprToNatStructId_2351_ = lean_ctor_get(v_s_2343_, 7);
v___x_2352_ = lean_array_get_size(v_structs_2344_);
v___x_2353_ = lean_nat_dec_lt(v_a_2340_, v___x_2352_);
if (v___x_2353_ == 0)
{
lean_dec_ref(v_fst_2342_);
return v_s_2343_;
}
else
{
lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2415_; 
lean_inc_ref(v_exprToNatStructId_2351_);
lean_inc_ref(v_natTypeIdOf_2350_);
lean_inc_ref(v_natStructs_2349_);
lean_inc_ref(v_forbiddenNatModules_2348_);
lean_inc_ref(v_exprToStructIdEntries_2347_);
lean_inc_ref(v_exprToStructId_2346_);
lean_inc_ref(v_typeIdOf_2345_);
lean_inc_ref(v_structs_2344_);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_s_2343_);
if (v_isSharedCheck_2415_ == 0)
{
lean_object* v_unused_2416_; lean_object* v_unused_2417_; lean_object* v_unused_2418_; lean_object* v_unused_2419_; lean_object* v_unused_2420_; lean_object* v_unused_2421_; lean_object* v_unused_2422_; lean_object* v_unused_2423_; 
v_unused_2416_ = lean_ctor_get(v_s_2343_, 7);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v_s_2343_, 6);
lean_dec(v_unused_2417_);
v_unused_2418_ = lean_ctor_get(v_s_2343_, 5);
lean_dec(v_unused_2418_);
v_unused_2419_ = lean_ctor_get(v_s_2343_, 4);
lean_dec(v_unused_2419_);
v_unused_2420_ = lean_ctor_get(v_s_2343_, 3);
lean_dec(v_unused_2420_);
v_unused_2421_ = lean_ctor_get(v_s_2343_, 2);
lean_dec(v_unused_2421_);
v_unused_2422_ = lean_ctor_get(v_s_2343_, 1);
lean_dec(v_unused_2422_);
v_unused_2423_ = lean_ctor_get(v_s_2343_, 0);
lean_dec(v_unused_2423_);
v___x_2355_ = v_s_2343_;
v_isShared_2356_ = v_isSharedCheck_2415_;
goto v_resetjp_2354_;
}
else
{
lean_dec(v_s_2343_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2415_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v_v_2357_; lean_object* v_id_2358_; lean_object* v_ringId_x3f_2359_; lean_object* v_type_2360_; lean_object* v_u_2361_; lean_object* v_intModuleInst_2362_; lean_object* v_leInst_x3f_2363_; lean_object* v_ltInst_x3f_2364_; lean_object* v_lawfulOrderLTInst_x3f_2365_; lean_object* v_isPreorderInst_x3f_2366_; lean_object* v_orderedAddInst_x3f_2367_; lean_object* v_isLinearInst_x3f_2368_; lean_object* v_noNatDivInst_x3f_2369_; lean_object* v_ringInst_x3f_2370_; lean_object* v_commRingInst_x3f_2371_; lean_object* v_orderedRingInst_x3f_2372_; lean_object* v_fieldInst_x3f_2373_; lean_object* v_charInst_x3f_2374_; lean_object* v_zero_2375_; lean_object* v_ofNatZero_2376_; lean_object* v_one_x3f_2377_; lean_object* v_leFn_x3f_2378_; lean_object* v_ltFn_x3f_2379_; lean_object* v_addFn_2380_; lean_object* v_zsmulFn_2381_; lean_object* v_nsmulFn_2382_; lean_object* v_zsmulFn_x3f_2383_; lean_object* v_nsmulFn_x3f_2384_; lean_object* v_homomulFn_x3f_2385_; lean_object* v_subFn_2386_; lean_object* v_negFn_2387_; lean_object* v_vars_2388_; lean_object* v_varMap_2389_; lean_object* v_lowers_2390_; lean_object* v_uppers_2391_; lean_object* v_diseqs_2392_; lean_object* v_assignment_2393_; uint8_t v_caseSplits_2394_; lean_object* v_conflict_x3f_2395_; lean_object* v_diseqSplits_2396_; lean_object* v_elimEqs_2397_; lean_object* v_elimStack_2398_; lean_object* v_occurs_2399_; lean_object* v_ignored_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2414_; 
v_v_2357_ = lean_array_fget(v_structs_2344_, v_a_2340_);
v_id_2358_ = lean_ctor_get(v_v_2357_, 0);
v_ringId_x3f_2359_ = lean_ctor_get(v_v_2357_, 1);
v_type_2360_ = lean_ctor_get(v_v_2357_, 2);
v_u_2361_ = lean_ctor_get(v_v_2357_, 3);
v_intModuleInst_2362_ = lean_ctor_get(v_v_2357_, 4);
v_leInst_x3f_2363_ = lean_ctor_get(v_v_2357_, 5);
v_ltInst_x3f_2364_ = lean_ctor_get(v_v_2357_, 6);
v_lawfulOrderLTInst_x3f_2365_ = lean_ctor_get(v_v_2357_, 7);
v_isPreorderInst_x3f_2366_ = lean_ctor_get(v_v_2357_, 8);
v_orderedAddInst_x3f_2367_ = lean_ctor_get(v_v_2357_, 9);
v_isLinearInst_x3f_2368_ = lean_ctor_get(v_v_2357_, 10);
v_noNatDivInst_x3f_2369_ = lean_ctor_get(v_v_2357_, 11);
v_ringInst_x3f_2370_ = lean_ctor_get(v_v_2357_, 12);
v_commRingInst_x3f_2371_ = lean_ctor_get(v_v_2357_, 13);
v_orderedRingInst_x3f_2372_ = lean_ctor_get(v_v_2357_, 14);
v_fieldInst_x3f_2373_ = lean_ctor_get(v_v_2357_, 15);
v_charInst_x3f_2374_ = lean_ctor_get(v_v_2357_, 16);
v_zero_2375_ = lean_ctor_get(v_v_2357_, 17);
v_ofNatZero_2376_ = lean_ctor_get(v_v_2357_, 18);
v_one_x3f_2377_ = lean_ctor_get(v_v_2357_, 19);
v_leFn_x3f_2378_ = lean_ctor_get(v_v_2357_, 20);
v_ltFn_x3f_2379_ = lean_ctor_get(v_v_2357_, 21);
v_addFn_2380_ = lean_ctor_get(v_v_2357_, 22);
v_zsmulFn_2381_ = lean_ctor_get(v_v_2357_, 23);
v_nsmulFn_2382_ = lean_ctor_get(v_v_2357_, 24);
v_zsmulFn_x3f_2383_ = lean_ctor_get(v_v_2357_, 25);
v_nsmulFn_x3f_2384_ = lean_ctor_get(v_v_2357_, 26);
v_homomulFn_x3f_2385_ = lean_ctor_get(v_v_2357_, 27);
v_subFn_2386_ = lean_ctor_get(v_v_2357_, 28);
v_negFn_2387_ = lean_ctor_get(v_v_2357_, 29);
v_vars_2388_ = lean_ctor_get(v_v_2357_, 30);
v_varMap_2389_ = lean_ctor_get(v_v_2357_, 31);
v_lowers_2390_ = lean_ctor_get(v_v_2357_, 32);
v_uppers_2391_ = lean_ctor_get(v_v_2357_, 33);
v_diseqs_2392_ = lean_ctor_get(v_v_2357_, 34);
v_assignment_2393_ = lean_ctor_get(v_v_2357_, 35);
v_caseSplits_2394_ = lean_ctor_get_uint8(v_v_2357_, sizeof(void*)*42);
v_conflict_x3f_2395_ = lean_ctor_get(v_v_2357_, 36);
v_diseqSplits_2396_ = lean_ctor_get(v_v_2357_, 37);
v_elimEqs_2397_ = lean_ctor_get(v_v_2357_, 38);
v_elimStack_2398_ = lean_ctor_get(v_v_2357_, 39);
v_occurs_2399_ = lean_ctor_get(v_v_2357_, 40);
v_ignored_2400_ = lean_ctor_get(v_v_2357_, 41);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_v_2357_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2402_ = v_v_2357_;
v_isShared_2403_ = v_isSharedCheck_2414_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_ignored_2400_);
lean_inc(v_occurs_2399_);
lean_inc(v_elimStack_2398_);
lean_inc(v_elimEqs_2397_);
lean_inc(v_diseqSplits_2396_);
lean_inc(v_conflict_x3f_2395_);
lean_inc(v_assignment_2393_);
lean_inc(v_diseqs_2392_);
lean_inc(v_uppers_2391_);
lean_inc(v_lowers_2390_);
lean_inc(v_varMap_2389_);
lean_inc(v_vars_2388_);
lean_inc(v_negFn_2387_);
lean_inc(v_subFn_2386_);
lean_inc(v_homomulFn_x3f_2385_);
lean_inc(v_nsmulFn_x3f_2384_);
lean_inc(v_zsmulFn_x3f_2383_);
lean_inc(v_nsmulFn_2382_);
lean_inc(v_zsmulFn_2381_);
lean_inc(v_addFn_2380_);
lean_inc(v_ltFn_x3f_2379_);
lean_inc(v_leFn_x3f_2378_);
lean_inc(v_one_x3f_2377_);
lean_inc(v_ofNatZero_2376_);
lean_inc(v_zero_2375_);
lean_inc(v_charInst_x3f_2374_);
lean_inc(v_fieldInst_x3f_2373_);
lean_inc(v_orderedRingInst_x3f_2372_);
lean_inc(v_commRingInst_x3f_2371_);
lean_inc(v_ringInst_x3f_2370_);
lean_inc(v_noNatDivInst_x3f_2369_);
lean_inc(v_isLinearInst_x3f_2368_);
lean_inc(v_orderedAddInst_x3f_2367_);
lean_inc(v_isPreorderInst_x3f_2366_);
lean_inc(v_lawfulOrderLTInst_x3f_2365_);
lean_inc(v_ltInst_x3f_2364_);
lean_inc(v_leInst_x3f_2363_);
lean_inc(v_intModuleInst_2362_);
lean_inc(v_u_2361_);
lean_inc(v_type_2360_);
lean_inc(v_ringId_x3f_2359_);
lean_inc(v_id_2358_);
lean_dec(v_v_2357_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2414_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; lean_object* v_xs_x27_2405_; lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2404_ = lean_box(0);
v_xs_x27_2405_ = lean_array_fset(v_structs_2344_, v_a_2340_, v___x_2404_);
v___x_2406_ = l_Lean_PersistentArray_set___redArg(v_lowers_2390_, v_y_2341_, v_fst_2342_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 32, v___x_2406_);
v___x_2408_ = v___x_2402_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_id_2358_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v_ringId_x3f_2359_);
lean_ctor_set(v_reuseFailAlloc_2413_, 2, v_type_2360_);
lean_ctor_set(v_reuseFailAlloc_2413_, 3, v_u_2361_);
lean_ctor_set(v_reuseFailAlloc_2413_, 4, v_intModuleInst_2362_);
lean_ctor_set(v_reuseFailAlloc_2413_, 5, v_leInst_x3f_2363_);
lean_ctor_set(v_reuseFailAlloc_2413_, 6, v_ltInst_x3f_2364_);
lean_ctor_set(v_reuseFailAlloc_2413_, 7, v_lawfulOrderLTInst_x3f_2365_);
lean_ctor_set(v_reuseFailAlloc_2413_, 8, v_isPreorderInst_x3f_2366_);
lean_ctor_set(v_reuseFailAlloc_2413_, 9, v_orderedAddInst_x3f_2367_);
lean_ctor_set(v_reuseFailAlloc_2413_, 10, v_isLinearInst_x3f_2368_);
lean_ctor_set(v_reuseFailAlloc_2413_, 11, v_noNatDivInst_x3f_2369_);
lean_ctor_set(v_reuseFailAlloc_2413_, 12, v_ringInst_x3f_2370_);
lean_ctor_set(v_reuseFailAlloc_2413_, 13, v_commRingInst_x3f_2371_);
lean_ctor_set(v_reuseFailAlloc_2413_, 14, v_orderedRingInst_x3f_2372_);
lean_ctor_set(v_reuseFailAlloc_2413_, 15, v_fieldInst_x3f_2373_);
lean_ctor_set(v_reuseFailAlloc_2413_, 16, v_charInst_x3f_2374_);
lean_ctor_set(v_reuseFailAlloc_2413_, 17, v_zero_2375_);
lean_ctor_set(v_reuseFailAlloc_2413_, 18, v_ofNatZero_2376_);
lean_ctor_set(v_reuseFailAlloc_2413_, 19, v_one_x3f_2377_);
lean_ctor_set(v_reuseFailAlloc_2413_, 20, v_leFn_x3f_2378_);
lean_ctor_set(v_reuseFailAlloc_2413_, 21, v_ltFn_x3f_2379_);
lean_ctor_set(v_reuseFailAlloc_2413_, 22, v_addFn_2380_);
lean_ctor_set(v_reuseFailAlloc_2413_, 23, v_zsmulFn_2381_);
lean_ctor_set(v_reuseFailAlloc_2413_, 24, v_nsmulFn_2382_);
lean_ctor_set(v_reuseFailAlloc_2413_, 25, v_zsmulFn_x3f_2383_);
lean_ctor_set(v_reuseFailAlloc_2413_, 26, v_nsmulFn_x3f_2384_);
lean_ctor_set(v_reuseFailAlloc_2413_, 27, v_homomulFn_x3f_2385_);
lean_ctor_set(v_reuseFailAlloc_2413_, 28, v_subFn_2386_);
lean_ctor_set(v_reuseFailAlloc_2413_, 29, v_negFn_2387_);
lean_ctor_set(v_reuseFailAlloc_2413_, 30, v_vars_2388_);
lean_ctor_set(v_reuseFailAlloc_2413_, 31, v_varMap_2389_);
lean_ctor_set(v_reuseFailAlloc_2413_, 32, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2413_, 33, v_uppers_2391_);
lean_ctor_set(v_reuseFailAlloc_2413_, 34, v_diseqs_2392_);
lean_ctor_set(v_reuseFailAlloc_2413_, 35, v_assignment_2393_);
lean_ctor_set(v_reuseFailAlloc_2413_, 36, v_conflict_x3f_2395_);
lean_ctor_set(v_reuseFailAlloc_2413_, 37, v_diseqSplits_2396_);
lean_ctor_set(v_reuseFailAlloc_2413_, 38, v_elimEqs_2397_);
lean_ctor_set(v_reuseFailAlloc_2413_, 39, v_elimStack_2398_);
lean_ctor_set(v_reuseFailAlloc_2413_, 40, v_occurs_2399_);
lean_ctor_set(v_reuseFailAlloc_2413_, 41, v_ignored_2400_);
lean_ctor_set_uint8(v_reuseFailAlloc_2413_, sizeof(void*)*42, v_caseSplits_2394_);
v___x_2408_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2409_; lean_object* v___x_2411_; 
v___x_2409_ = lean_array_fset(v_xs_x27_2405_, v_a_2340_, v___x_2408_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2409_);
v___x_2411_ = v___x_2355_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v_typeIdOf_2345_);
lean_ctor_set(v_reuseFailAlloc_2412_, 2, v_exprToStructId_2346_);
lean_ctor_set(v_reuseFailAlloc_2412_, 3, v_exprToStructIdEntries_2347_);
lean_ctor_set(v_reuseFailAlloc_2412_, 4, v_forbiddenNatModules_2348_);
lean_ctor_set(v_reuseFailAlloc_2412_, 5, v_natStructs_2349_);
lean_ctor_set(v_reuseFailAlloc_2412_, 6, v_natTypeIdOf_2350_);
lean_ctor_set(v_reuseFailAlloc_2412_, 7, v_exprToNatStructId_2351_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed(lean_object* v_a_2424_, lean_object* v_y_2425_, lean_object* v_fst_2426_, lean_object* v_s_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0(v_a_2424_, v_y_2425_, v_fst_2426_, v_s_2427_);
lean_dec(v_y_2425_);
lean_dec(v_a_2424_);
return v_res_2428_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0(void){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(lean_object* v_a_2430_, lean_object* v_x_2431_, lean_object* v_c_2432_, lean_object* v_y_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2481_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2449_ = v___x_2446_;
v_isShared_2450_ = v_isSharedCheck_2481_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2446_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2481_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
uint8_t v___x_2451_; 
v___x_2451_ = lean_unbox(v_a_2447_);
lean_dec(v_a_2447_);
if (v___x_2451_ == 0)
{
lean_object* v___x_2452_; 
lean_del_object(v___x_2449_);
v___x_2452_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___y_2455_; lean_object* v_lowers_2463_; lean_object* v_size_2464_; lean_object* v___x_2465_; uint8_t v___x_2466_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
lean_dec_ref(v___x_2452_);
v_lowers_2463_ = lean_ctor_get(v_a_2453_, 32);
lean_inc_ref(v_lowers_2463_);
lean_dec(v_a_2453_);
v_size_2464_ = lean_ctor_get(v_lowers_2463_, 2);
v___x_2465_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2466_ = lean_nat_dec_lt(v_y_2433_, v_size_2464_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; 
lean_dec_ref(v_lowers_2463_);
v___x_2467_ = l_outOfBounds___redArg(v___x_2465_);
v___y_2455_ = v___x_2467_;
goto v___jp_2454_;
}
else
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2465_, v_lowers_2463_, v_y_2433_);
lean_dec_ref(v_lowers_2463_);
v___y_2455_ = v___x_2468_;
goto v___jp_2454_;
}
v___jp_2454_:
{
lean_object* v___x_2456_; lean_object* v_fst_2457_; lean_object* v_snd_2458_; lean_object* v___f_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2456_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2431_, v___y_2455_);
v_fst_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_fst_2457_);
v_snd_2458_ = lean_ctor_get(v___x_2456_, 1);
lean_inc(v_snd_2458_);
lean_dec_ref(v___x_2456_);
lean_inc(v_a_2434_);
v___f_2459_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2459_, 0, v_a_2434_);
lean_closure_set(v___f_2459_, 1, v_y_2433_);
lean_closure_set(v___f_2459_, 2, v_fst_2457_);
v___x_2460_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2461_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2460_, v___f_2459_, v_a_2435_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v___x_2462_; 
lean_dec_ref(v___x_2461_);
v___x_2462_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2430_, v_x_2431_, v_c_2432_, v_snd_2458_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
lean_dec(v_snd_2458_);
return v___x_2462_;
}
else
{
lean_dec(v_snd_2458_);
lean_dec_ref(v_c_2432_);
lean_dec(v_x_2431_);
lean_dec(v_a_2430_);
return v___x_2461_;
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec(v_y_2433_);
lean_dec_ref(v_c_2432_);
lean_dec(v_x_2431_);
lean_dec(v_a_2430_);
v_a_2469_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2452_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2452_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
else
{
lean_object* v___x_2477_; lean_object* v___x_2479_; 
lean_dec(v_y_2433_);
lean_dec_ref(v_c_2432_);
lean_dec(v_x_2431_);
lean_dec(v_a_2430_);
v___x_2477_ = lean_box(0);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v___x_2477_);
v___x_2479_ = v___x_2449_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2477_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_dec(v_y_2433_);
lean_dec_ref(v_c_2432_);
lean_dec(v_x_2431_);
lean_dec(v_a_2430_);
v_a_2482_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2446_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2446_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___boxed(lean_object* v_a_2490_, lean_object* v_x_2491_, lean_object* v_c_2492_, lean_object* v_y_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_2490_, v_x_2491_, v_c_2492_, v_y_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
lean_dec(v_a_2500_);
lean_dec_ref(v_a_2499_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec(v_a_2494_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(lean_object* v_a_2507_, lean_object* v_y_2508_, lean_object* v_fst_2509_, lean_object* v_s_2510_){
_start:
{
lean_object* v_structs_2511_; lean_object* v_typeIdOf_2512_; lean_object* v_exprToStructId_2513_; lean_object* v_exprToStructIdEntries_2514_; lean_object* v_forbiddenNatModules_2515_; lean_object* v_natStructs_2516_; lean_object* v_natTypeIdOf_2517_; lean_object* v_exprToNatStructId_2518_; lean_object* v___x_2519_; uint8_t v___x_2520_; 
v_structs_2511_ = lean_ctor_get(v_s_2510_, 0);
v_typeIdOf_2512_ = lean_ctor_get(v_s_2510_, 1);
v_exprToStructId_2513_ = lean_ctor_get(v_s_2510_, 2);
v_exprToStructIdEntries_2514_ = lean_ctor_get(v_s_2510_, 3);
v_forbiddenNatModules_2515_ = lean_ctor_get(v_s_2510_, 4);
v_natStructs_2516_ = lean_ctor_get(v_s_2510_, 5);
v_natTypeIdOf_2517_ = lean_ctor_get(v_s_2510_, 6);
v_exprToNatStructId_2518_ = lean_ctor_get(v_s_2510_, 7);
v___x_2519_ = lean_array_get_size(v_structs_2511_);
v___x_2520_ = lean_nat_dec_lt(v_a_2507_, v___x_2519_);
if (v___x_2520_ == 0)
{
lean_dec_ref(v_fst_2509_);
return v_s_2510_;
}
else
{
lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2582_; 
lean_inc_ref(v_exprToNatStructId_2518_);
lean_inc_ref(v_natTypeIdOf_2517_);
lean_inc_ref(v_natStructs_2516_);
lean_inc_ref(v_forbiddenNatModules_2515_);
lean_inc_ref(v_exprToStructIdEntries_2514_);
lean_inc_ref(v_exprToStructId_2513_);
lean_inc_ref(v_typeIdOf_2512_);
lean_inc_ref(v_structs_2511_);
v_isSharedCheck_2582_ = !lean_is_exclusive(v_s_2510_);
if (v_isSharedCheck_2582_ == 0)
{
lean_object* v_unused_2583_; lean_object* v_unused_2584_; lean_object* v_unused_2585_; lean_object* v_unused_2586_; lean_object* v_unused_2587_; lean_object* v_unused_2588_; lean_object* v_unused_2589_; lean_object* v_unused_2590_; 
v_unused_2583_ = lean_ctor_get(v_s_2510_, 7);
lean_dec(v_unused_2583_);
v_unused_2584_ = lean_ctor_get(v_s_2510_, 6);
lean_dec(v_unused_2584_);
v_unused_2585_ = lean_ctor_get(v_s_2510_, 5);
lean_dec(v_unused_2585_);
v_unused_2586_ = lean_ctor_get(v_s_2510_, 4);
lean_dec(v_unused_2586_);
v_unused_2587_ = lean_ctor_get(v_s_2510_, 3);
lean_dec(v_unused_2587_);
v_unused_2588_ = lean_ctor_get(v_s_2510_, 2);
lean_dec(v_unused_2588_);
v_unused_2589_ = lean_ctor_get(v_s_2510_, 1);
lean_dec(v_unused_2589_);
v_unused_2590_ = lean_ctor_get(v_s_2510_, 0);
lean_dec(v_unused_2590_);
v___x_2522_ = v_s_2510_;
v_isShared_2523_ = v_isSharedCheck_2582_;
goto v_resetjp_2521_;
}
else
{
lean_dec(v_s_2510_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2582_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v_v_2524_; lean_object* v_id_2525_; lean_object* v_ringId_x3f_2526_; lean_object* v_type_2527_; lean_object* v_u_2528_; lean_object* v_intModuleInst_2529_; lean_object* v_leInst_x3f_2530_; lean_object* v_ltInst_x3f_2531_; lean_object* v_lawfulOrderLTInst_x3f_2532_; lean_object* v_isPreorderInst_x3f_2533_; lean_object* v_orderedAddInst_x3f_2534_; lean_object* v_isLinearInst_x3f_2535_; lean_object* v_noNatDivInst_x3f_2536_; lean_object* v_ringInst_x3f_2537_; lean_object* v_commRingInst_x3f_2538_; lean_object* v_orderedRingInst_x3f_2539_; lean_object* v_fieldInst_x3f_2540_; lean_object* v_charInst_x3f_2541_; lean_object* v_zero_2542_; lean_object* v_ofNatZero_2543_; lean_object* v_one_x3f_2544_; lean_object* v_leFn_x3f_2545_; lean_object* v_ltFn_x3f_2546_; lean_object* v_addFn_2547_; lean_object* v_zsmulFn_2548_; lean_object* v_nsmulFn_2549_; lean_object* v_zsmulFn_x3f_2550_; lean_object* v_nsmulFn_x3f_2551_; lean_object* v_homomulFn_x3f_2552_; lean_object* v_subFn_2553_; lean_object* v_negFn_2554_; lean_object* v_vars_2555_; lean_object* v_varMap_2556_; lean_object* v_lowers_2557_; lean_object* v_uppers_2558_; lean_object* v_diseqs_2559_; lean_object* v_assignment_2560_; uint8_t v_caseSplits_2561_; lean_object* v_conflict_x3f_2562_; lean_object* v_diseqSplits_2563_; lean_object* v_elimEqs_2564_; lean_object* v_elimStack_2565_; lean_object* v_occurs_2566_; lean_object* v_ignored_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2581_; 
v_v_2524_ = lean_array_fget(v_structs_2511_, v_a_2507_);
v_id_2525_ = lean_ctor_get(v_v_2524_, 0);
v_ringId_x3f_2526_ = lean_ctor_get(v_v_2524_, 1);
v_type_2527_ = lean_ctor_get(v_v_2524_, 2);
v_u_2528_ = lean_ctor_get(v_v_2524_, 3);
v_intModuleInst_2529_ = lean_ctor_get(v_v_2524_, 4);
v_leInst_x3f_2530_ = lean_ctor_get(v_v_2524_, 5);
v_ltInst_x3f_2531_ = lean_ctor_get(v_v_2524_, 6);
v_lawfulOrderLTInst_x3f_2532_ = lean_ctor_get(v_v_2524_, 7);
v_isPreorderInst_x3f_2533_ = lean_ctor_get(v_v_2524_, 8);
v_orderedAddInst_x3f_2534_ = lean_ctor_get(v_v_2524_, 9);
v_isLinearInst_x3f_2535_ = lean_ctor_get(v_v_2524_, 10);
v_noNatDivInst_x3f_2536_ = lean_ctor_get(v_v_2524_, 11);
v_ringInst_x3f_2537_ = lean_ctor_get(v_v_2524_, 12);
v_commRingInst_x3f_2538_ = lean_ctor_get(v_v_2524_, 13);
v_orderedRingInst_x3f_2539_ = lean_ctor_get(v_v_2524_, 14);
v_fieldInst_x3f_2540_ = lean_ctor_get(v_v_2524_, 15);
v_charInst_x3f_2541_ = lean_ctor_get(v_v_2524_, 16);
v_zero_2542_ = lean_ctor_get(v_v_2524_, 17);
v_ofNatZero_2543_ = lean_ctor_get(v_v_2524_, 18);
v_one_x3f_2544_ = lean_ctor_get(v_v_2524_, 19);
v_leFn_x3f_2545_ = lean_ctor_get(v_v_2524_, 20);
v_ltFn_x3f_2546_ = lean_ctor_get(v_v_2524_, 21);
v_addFn_2547_ = lean_ctor_get(v_v_2524_, 22);
v_zsmulFn_2548_ = lean_ctor_get(v_v_2524_, 23);
v_nsmulFn_2549_ = lean_ctor_get(v_v_2524_, 24);
v_zsmulFn_x3f_2550_ = lean_ctor_get(v_v_2524_, 25);
v_nsmulFn_x3f_2551_ = lean_ctor_get(v_v_2524_, 26);
v_homomulFn_x3f_2552_ = lean_ctor_get(v_v_2524_, 27);
v_subFn_2553_ = lean_ctor_get(v_v_2524_, 28);
v_negFn_2554_ = lean_ctor_get(v_v_2524_, 29);
v_vars_2555_ = lean_ctor_get(v_v_2524_, 30);
v_varMap_2556_ = lean_ctor_get(v_v_2524_, 31);
v_lowers_2557_ = lean_ctor_get(v_v_2524_, 32);
v_uppers_2558_ = lean_ctor_get(v_v_2524_, 33);
v_diseqs_2559_ = lean_ctor_get(v_v_2524_, 34);
v_assignment_2560_ = lean_ctor_get(v_v_2524_, 35);
v_caseSplits_2561_ = lean_ctor_get_uint8(v_v_2524_, sizeof(void*)*42);
v_conflict_x3f_2562_ = lean_ctor_get(v_v_2524_, 36);
v_diseqSplits_2563_ = lean_ctor_get(v_v_2524_, 37);
v_elimEqs_2564_ = lean_ctor_get(v_v_2524_, 38);
v_elimStack_2565_ = lean_ctor_get(v_v_2524_, 39);
v_occurs_2566_ = lean_ctor_get(v_v_2524_, 40);
v_ignored_2567_ = lean_ctor_get(v_v_2524_, 41);
v_isSharedCheck_2581_ = !lean_is_exclusive(v_v_2524_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2569_ = v_v_2524_;
v_isShared_2570_ = v_isSharedCheck_2581_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_ignored_2567_);
lean_inc(v_occurs_2566_);
lean_inc(v_elimStack_2565_);
lean_inc(v_elimEqs_2564_);
lean_inc(v_diseqSplits_2563_);
lean_inc(v_conflict_x3f_2562_);
lean_inc(v_assignment_2560_);
lean_inc(v_diseqs_2559_);
lean_inc(v_uppers_2558_);
lean_inc(v_lowers_2557_);
lean_inc(v_varMap_2556_);
lean_inc(v_vars_2555_);
lean_inc(v_negFn_2554_);
lean_inc(v_subFn_2553_);
lean_inc(v_homomulFn_x3f_2552_);
lean_inc(v_nsmulFn_x3f_2551_);
lean_inc(v_zsmulFn_x3f_2550_);
lean_inc(v_nsmulFn_2549_);
lean_inc(v_zsmulFn_2548_);
lean_inc(v_addFn_2547_);
lean_inc(v_ltFn_x3f_2546_);
lean_inc(v_leFn_x3f_2545_);
lean_inc(v_one_x3f_2544_);
lean_inc(v_ofNatZero_2543_);
lean_inc(v_zero_2542_);
lean_inc(v_charInst_x3f_2541_);
lean_inc(v_fieldInst_x3f_2540_);
lean_inc(v_orderedRingInst_x3f_2539_);
lean_inc(v_commRingInst_x3f_2538_);
lean_inc(v_ringInst_x3f_2537_);
lean_inc(v_noNatDivInst_x3f_2536_);
lean_inc(v_isLinearInst_x3f_2535_);
lean_inc(v_orderedAddInst_x3f_2534_);
lean_inc(v_isPreorderInst_x3f_2533_);
lean_inc(v_lawfulOrderLTInst_x3f_2532_);
lean_inc(v_ltInst_x3f_2531_);
lean_inc(v_leInst_x3f_2530_);
lean_inc(v_intModuleInst_2529_);
lean_inc(v_u_2528_);
lean_inc(v_type_2527_);
lean_inc(v_ringId_x3f_2526_);
lean_inc(v_id_2525_);
lean_dec(v_v_2524_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2581_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; lean_object* v_xs_x27_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2571_ = lean_box(0);
v_xs_x27_2572_ = lean_array_fset(v_structs_2511_, v_a_2507_, v___x_2571_);
v___x_2573_ = l_Lean_PersistentArray_set___redArg(v_uppers_2558_, v_y_2508_, v_fst_2509_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 33, v___x_2573_);
v___x_2575_ = v___x_2569_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_id_2525_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_ringId_x3f_2526_);
lean_ctor_set(v_reuseFailAlloc_2580_, 2, v_type_2527_);
lean_ctor_set(v_reuseFailAlloc_2580_, 3, v_u_2528_);
lean_ctor_set(v_reuseFailAlloc_2580_, 4, v_intModuleInst_2529_);
lean_ctor_set(v_reuseFailAlloc_2580_, 5, v_leInst_x3f_2530_);
lean_ctor_set(v_reuseFailAlloc_2580_, 6, v_ltInst_x3f_2531_);
lean_ctor_set(v_reuseFailAlloc_2580_, 7, v_lawfulOrderLTInst_x3f_2532_);
lean_ctor_set(v_reuseFailAlloc_2580_, 8, v_isPreorderInst_x3f_2533_);
lean_ctor_set(v_reuseFailAlloc_2580_, 9, v_orderedAddInst_x3f_2534_);
lean_ctor_set(v_reuseFailAlloc_2580_, 10, v_isLinearInst_x3f_2535_);
lean_ctor_set(v_reuseFailAlloc_2580_, 11, v_noNatDivInst_x3f_2536_);
lean_ctor_set(v_reuseFailAlloc_2580_, 12, v_ringInst_x3f_2537_);
lean_ctor_set(v_reuseFailAlloc_2580_, 13, v_commRingInst_x3f_2538_);
lean_ctor_set(v_reuseFailAlloc_2580_, 14, v_orderedRingInst_x3f_2539_);
lean_ctor_set(v_reuseFailAlloc_2580_, 15, v_fieldInst_x3f_2540_);
lean_ctor_set(v_reuseFailAlloc_2580_, 16, v_charInst_x3f_2541_);
lean_ctor_set(v_reuseFailAlloc_2580_, 17, v_zero_2542_);
lean_ctor_set(v_reuseFailAlloc_2580_, 18, v_ofNatZero_2543_);
lean_ctor_set(v_reuseFailAlloc_2580_, 19, v_one_x3f_2544_);
lean_ctor_set(v_reuseFailAlloc_2580_, 20, v_leFn_x3f_2545_);
lean_ctor_set(v_reuseFailAlloc_2580_, 21, v_ltFn_x3f_2546_);
lean_ctor_set(v_reuseFailAlloc_2580_, 22, v_addFn_2547_);
lean_ctor_set(v_reuseFailAlloc_2580_, 23, v_zsmulFn_2548_);
lean_ctor_set(v_reuseFailAlloc_2580_, 24, v_nsmulFn_2549_);
lean_ctor_set(v_reuseFailAlloc_2580_, 25, v_zsmulFn_x3f_2550_);
lean_ctor_set(v_reuseFailAlloc_2580_, 26, v_nsmulFn_x3f_2551_);
lean_ctor_set(v_reuseFailAlloc_2580_, 27, v_homomulFn_x3f_2552_);
lean_ctor_set(v_reuseFailAlloc_2580_, 28, v_subFn_2553_);
lean_ctor_set(v_reuseFailAlloc_2580_, 29, v_negFn_2554_);
lean_ctor_set(v_reuseFailAlloc_2580_, 30, v_vars_2555_);
lean_ctor_set(v_reuseFailAlloc_2580_, 31, v_varMap_2556_);
lean_ctor_set(v_reuseFailAlloc_2580_, 32, v_lowers_2557_);
lean_ctor_set(v_reuseFailAlloc_2580_, 33, v___x_2573_);
lean_ctor_set(v_reuseFailAlloc_2580_, 34, v_diseqs_2559_);
lean_ctor_set(v_reuseFailAlloc_2580_, 35, v_assignment_2560_);
lean_ctor_set(v_reuseFailAlloc_2580_, 36, v_conflict_x3f_2562_);
lean_ctor_set(v_reuseFailAlloc_2580_, 37, v_diseqSplits_2563_);
lean_ctor_set(v_reuseFailAlloc_2580_, 38, v_elimEqs_2564_);
lean_ctor_set(v_reuseFailAlloc_2580_, 39, v_elimStack_2565_);
lean_ctor_set(v_reuseFailAlloc_2580_, 40, v_occurs_2566_);
lean_ctor_set(v_reuseFailAlloc_2580_, 41, v_ignored_2567_);
lean_ctor_set_uint8(v_reuseFailAlloc_2580_, sizeof(void*)*42, v_caseSplits_2561_);
v___x_2575_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2576_ = lean_array_fset(v_xs_x27_2572_, v_a_2507_, v___x_2575_);
if (v_isShared_2523_ == 0)
{
lean_ctor_set(v___x_2522_, 0, v___x_2576_);
v___x_2578_ = v___x_2522_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v_typeIdOf_2512_);
lean_ctor_set(v_reuseFailAlloc_2579_, 2, v_exprToStructId_2513_);
lean_ctor_set(v_reuseFailAlloc_2579_, 3, v_exprToStructIdEntries_2514_);
lean_ctor_set(v_reuseFailAlloc_2579_, 4, v_forbiddenNatModules_2515_);
lean_ctor_set(v_reuseFailAlloc_2579_, 5, v_natStructs_2516_);
lean_ctor_set(v_reuseFailAlloc_2579_, 6, v_natTypeIdOf_2517_);
lean_ctor_set(v_reuseFailAlloc_2579_, 7, v_exprToNatStructId_2518_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed(lean_object* v_a_2591_, lean_object* v_y_2592_, lean_object* v_fst_2593_, lean_object* v_s_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0(v_a_2591_, v_y_2592_, v_fst_2593_, v_s_2594_);
lean_dec(v_y_2592_);
lean_dec(v_a_2591_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(lean_object* v_a_2596_, lean_object* v_x_2597_, lean_object* v_c_2598_, lean_object* v_y_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2647_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2647_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2647_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
uint8_t v___x_2617_; 
v___x_2617_ = lean_unbox(v_a_2613_);
lean_dec(v_a_2613_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2618_; 
lean_del_object(v___x_2615_);
v___x_2618_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___y_2621_; lean_object* v_uppers_2629_; lean_object* v_size_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref(v___x_2618_);
v_uppers_2629_ = lean_ctor_get(v_a_2619_, 33);
lean_inc_ref(v_uppers_2629_);
lean_dec(v_a_2619_);
v_size_2630_ = lean_ctor_get(v_uppers_2629_, 2);
v___x_2631_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_2632_ = lean_nat_dec_lt(v_y_2599_, v_size_2630_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; 
lean_dec_ref(v_uppers_2629_);
v___x_2633_ = l_outOfBounds___redArg(v___x_2631_);
v___y_2621_ = v___x_2633_;
goto v___jp_2620_;
}
else
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2631_, v_uppers_2629_, v_y_2599_);
lean_dec_ref(v_uppers_2629_);
v___y_2621_ = v___x_2634_;
goto v___jp_2620_;
}
v___jp_2620_:
{
lean_object* v___x_2622_; lean_object* v_fst_2623_; lean_object* v_snd_2624_; lean_object* v___f_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2622_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitIneqCnstrs_spec__0(v_x_2597_, v___y_2621_);
v_fst_2623_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_fst_2623_);
v_snd_2624_ = lean_ctor_get(v___x_2622_, 1);
lean_inc(v_snd_2624_);
lean_dec_ref(v___x_2622_);
lean_inc(v_a_2600_);
v___f_2625_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2625_, 0, v_a_2600_);
lean_closure_set(v___f_2625_, 1, v_y_2599_);
lean_closure_set(v___f_2625_, 2, v_fst_2623_);
v___x_2626_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2627_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2626_, v___f_2625_, v_a_2601_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v___x_2628_; 
lean_dec_ref(v___x_2627_);
v___x_2628_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs(v_a_2596_, v_x_2597_, v_c_2598_, v_snd_2624_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
lean_dec(v_snd_2624_);
return v___x_2628_;
}
else
{
lean_dec(v_snd_2624_);
lean_dec_ref(v_c_2598_);
lean_dec(v_x_2597_);
lean_dec(v_a_2596_);
return v___x_2627_;
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
lean_dec(v_y_2599_);
lean_dec_ref(v_c_2598_);
lean_dec(v_x_2597_);
lean_dec(v_a_2596_);
v_a_2635_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2618_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2618_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
else
{
lean_object* v___x_2643_; lean_object* v___x_2645_; 
lean_dec(v_y_2599_);
lean_dec_ref(v_c_2598_);
lean_dec(v_x_2597_);
lean_dec(v_a_2596_);
v___x_2643_ = lean_box(0);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___x_2643_);
v___x_2645_ = v___x_2615_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
lean_dec(v_y_2599_);
lean_dec_ref(v_c_2598_);
lean_dec(v_x_2597_);
lean_dec(v_a_2596_);
v_a_2648_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2612_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2612_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2648_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers___boxed(lean_object* v_a_2656_, lean_object* v_x_2657_, lean_object* v_c_2658_, lean_object* v_y_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_2656_, v_x_2657_, v_c_2658_, v_y_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec(v_a_2660_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(lean_object* v___y_2673_, lean_object* v_a_2674_, lean_object* v_s_2675_){
_start:
{
lean_object* v_structs_2676_; lean_object* v_typeIdOf_2677_; lean_object* v_exprToStructId_2678_; lean_object* v_exprToStructIdEntries_2679_; lean_object* v_forbiddenNatModules_2680_; lean_object* v_natStructs_2681_; lean_object* v_natTypeIdOf_2682_; lean_object* v_exprToNatStructId_2683_; lean_object* v___x_2684_; uint8_t v___x_2685_; 
v_structs_2676_ = lean_ctor_get(v_s_2675_, 0);
v_typeIdOf_2677_ = lean_ctor_get(v_s_2675_, 1);
v_exprToStructId_2678_ = lean_ctor_get(v_s_2675_, 2);
v_exprToStructIdEntries_2679_ = lean_ctor_get(v_s_2675_, 3);
v_forbiddenNatModules_2680_ = lean_ctor_get(v_s_2675_, 4);
v_natStructs_2681_ = lean_ctor_get(v_s_2675_, 5);
v_natTypeIdOf_2682_ = lean_ctor_get(v_s_2675_, 6);
v_exprToNatStructId_2683_ = lean_ctor_get(v_s_2675_, 7);
v___x_2684_ = lean_array_get_size(v_structs_2676_);
v___x_2685_ = lean_nat_dec_lt(v___y_2673_, v___x_2684_);
if (v___x_2685_ == 0)
{
lean_dec_ref(v_a_2674_);
return v_s_2675_;
}
else
{
lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2747_; 
lean_inc_ref(v_exprToNatStructId_2683_);
lean_inc_ref(v_natTypeIdOf_2682_);
lean_inc_ref(v_natStructs_2681_);
lean_inc_ref(v_forbiddenNatModules_2680_);
lean_inc_ref(v_exprToStructIdEntries_2679_);
lean_inc_ref(v_exprToStructId_2678_);
lean_inc_ref(v_typeIdOf_2677_);
lean_inc_ref(v_structs_2676_);
v_isSharedCheck_2747_ = !lean_is_exclusive(v_s_2675_);
if (v_isSharedCheck_2747_ == 0)
{
lean_object* v_unused_2748_; lean_object* v_unused_2749_; lean_object* v_unused_2750_; lean_object* v_unused_2751_; lean_object* v_unused_2752_; lean_object* v_unused_2753_; lean_object* v_unused_2754_; lean_object* v_unused_2755_; 
v_unused_2748_ = lean_ctor_get(v_s_2675_, 7);
lean_dec(v_unused_2748_);
v_unused_2749_ = lean_ctor_get(v_s_2675_, 6);
lean_dec(v_unused_2749_);
v_unused_2750_ = lean_ctor_get(v_s_2675_, 5);
lean_dec(v_unused_2750_);
v_unused_2751_ = lean_ctor_get(v_s_2675_, 4);
lean_dec(v_unused_2751_);
v_unused_2752_ = lean_ctor_get(v_s_2675_, 3);
lean_dec(v_unused_2752_);
v_unused_2753_ = lean_ctor_get(v_s_2675_, 2);
lean_dec(v_unused_2753_);
v_unused_2754_ = lean_ctor_get(v_s_2675_, 1);
lean_dec(v_unused_2754_);
v_unused_2755_ = lean_ctor_get(v_s_2675_, 0);
lean_dec(v_unused_2755_);
v___x_2687_ = v_s_2675_;
v_isShared_2688_ = v_isSharedCheck_2747_;
goto v_resetjp_2686_;
}
else
{
lean_dec(v_s_2675_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2747_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v_v_2689_; lean_object* v_id_2690_; lean_object* v_ringId_x3f_2691_; lean_object* v_type_2692_; lean_object* v_u_2693_; lean_object* v_intModuleInst_2694_; lean_object* v_leInst_x3f_2695_; lean_object* v_ltInst_x3f_2696_; lean_object* v_lawfulOrderLTInst_x3f_2697_; lean_object* v_isPreorderInst_x3f_2698_; lean_object* v_orderedAddInst_x3f_2699_; lean_object* v_isLinearInst_x3f_2700_; lean_object* v_noNatDivInst_x3f_2701_; lean_object* v_ringInst_x3f_2702_; lean_object* v_commRingInst_x3f_2703_; lean_object* v_orderedRingInst_x3f_2704_; lean_object* v_fieldInst_x3f_2705_; lean_object* v_charInst_x3f_2706_; lean_object* v_zero_2707_; lean_object* v_ofNatZero_2708_; lean_object* v_one_x3f_2709_; lean_object* v_leFn_x3f_2710_; lean_object* v_ltFn_x3f_2711_; lean_object* v_addFn_2712_; lean_object* v_zsmulFn_2713_; lean_object* v_nsmulFn_2714_; lean_object* v_zsmulFn_x3f_2715_; lean_object* v_nsmulFn_x3f_2716_; lean_object* v_homomulFn_x3f_2717_; lean_object* v_subFn_2718_; lean_object* v_negFn_2719_; lean_object* v_vars_2720_; lean_object* v_varMap_2721_; lean_object* v_lowers_2722_; lean_object* v_uppers_2723_; lean_object* v_diseqs_2724_; lean_object* v_assignment_2725_; uint8_t v_caseSplits_2726_; lean_object* v_conflict_x3f_2727_; lean_object* v_diseqSplits_2728_; lean_object* v_elimEqs_2729_; lean_object* v_elimStack_2730_; lean_object* v_occurs_2731_; lean_object* v_ignored_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2746_; 
v_v_2689_ = lean_array_fget(v_structs_2676_, v___y_2673_);
v_id_2690_ = lean_ctor_get(v_v_2689_, 0);
v_ringId_x3f_2691_ = lean_ctor_get(v_v_2689_, 1);
v_type_2692_ = lean_ctor_get(v_v_2689_, 2);
v_u_2693_ = lean_ctor_get(v_v_2689_, 3);
v_intModuleInst_2694_ = lean_ctor_get(v_v_2689_, 4);
v_leInst_x3f_2695_ = lean_ctor_get(v_v_2689_, 5);
v_ltInst_x3f_2696_ = lean_ctor_get(v_v_2689_, 6);
v_lawfulOrderLTInst_x3f_2697_ = lean_ctor_get(v_v_2689_, 7);
v_isPreorderInst_x3f_2698_ = lean_ctor_get(v_v_2689_, 8);
v_orderedAddInst_x3f_2699_ = lean_ctor_get(v_v_2689_, 9);
v_isLinearInst_x3f_2700_ = lean_ctor_get(v_v_2689_, 10);
v_noNatDivInst_x3f_2701_ = lean_ctor_get(v_v_2689_, 11);
v_ringInst_x3f_2702_ = lean_ctor_get(v_v_2689_, 12);
v_commRingInst_x3f_2703_ = lean_ctor_get(v_v_2689_, 13);
v_orderedRingInst_x3f_2704_ = lean_ctor_get(v_v_2689_, 14);
v_fieldInst_x3f_2705_ = lean_ctor_get(v_v_2689_, 15);
v_charInst_x3f_2706_ = lean_ctor_get(v_v_2689_, 16);
v_zero_2707_ = lean_ctor_get(v_v_2689_, 17);
v_ofNatZero_2708_ = lean_ctor_get(v_v_2689_, 18);
v_one_x3f_2709_ = lean_ctor_get(v_v_2689_, 19);
v_leFn_x3f_2710_ = lean_ctor_get(v_v_2689_, 20);
v_ltFn_x3f_2711_ = lean_ctor_get(v_v_2689_, 21);
v_addFn_2712_ = lean_ctor_get(v_v_2689_, 22);
v_zsmulFn_2713_ = lean_ctor_get(v_v_2689_, 23);
v_nsmulFn_2714_ = lean_ctor_get(v_v_2689_, 24);
v_zsmulFn_x3f_2715_ = lean_ctor_get(v_v_2689_, 25);
v_nsmulFn_x3f_2716_ = lean_ctor_get(v_v_2689_, 26);
v_homomulFn_x3f_2717_ = lean_ctor_get(v_v_2689_, 27);
v_subFn_2718_ = lean_ctor_get(v_v_2689_, 28);
v_negFn_2719_ = lean_ctor_get(v_v_2689_, 29);
v_vars_2720_ = lean_ctor_get(v_v_2689_, 30);
v_varMap_2721_ = lean_ctor_get(v_v_2689_, 31);
v_lowers_2722_ = lean_ctor_get(v_v_2689_, 32);
v_uppers_2723_ = lean_ctor_get(v_v_2689_, 33);
v_diseqs_2724_ = lean_ctor_get(v_v_2689_, 34);
v_assignment_2725_ = lean_ctor_get(v_v_2689_, 35);
v_caseSplits_2726_ = lean_ctor_get_uint8(v_v_2689_, sizeof(void*)*42);
v_conflict_x3f_2727_ = lean_ctor_get(v_v_2689_, 36);
v_diseqSplits_2728_ = lean_ctor_get(v_v_2689_, 37);
v_elimEqs_2729_ = lean_ctor_get(v_v_2689_, 38);
v_elimStack_2730_ = lean_ctor_get(v_v_2689_, 39);
v_occurs_2731_ = lean_ctor_get(v_v_2689_, 40);
v_ignored_2732_ = lean_ctor_get(v_v_2689_, 41);
v_isSharedCheck_2746_ = !lean_is_exclusive(v_v_2689_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2734_ = v_v_2689_;
v_isShared_2735_ = v_isSharedCheck_2746_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_ignored_2732_);
lean_inc(v_occurs_2731_);
lean_inc(v_elimStack_2730_);
lean_inc(v_elimEqs_2729_);
lean_inc(v_diseqSplits_2728_);
lean_inc(v_conflict_x3f_2727_);
lean_inc(v_assignment_2725_);
lean_inc(v_diseqs_2724_);
lean_inc(v_uppers_2723_);
lean_inc(v_lowers_2722_);
lean_inc(v_varMap_2721_);
lean_inc(v_vars_2720_);
lean_inc(v_negFn_2719_);
lean_inc(v_subFn_2718_);
lean_inc(v_homomulFn_x3f_2717_);
lean_inc(v_nsmulFn_x3f_2716_);
lean_inc(v_zsmulFn_x3f_2715_);
lean_inc(v_nsmulFn_2714_);
lean_inc(v_zsmulFn_2713_);
lean_inc(v_addFn_2712_);
lean_inc(v_ltFn_x3f_2711_);
lean_inc(v_leFn_x3f_2710_);
lean_inc(v_one_x3f_2709_);
lean_inc(v_ofNatZero_2708_);
lean_inc(v_zero_2707_);
lean_inc(v_charInst_x3f_2706_);
lean_inc(v_fieldInst_x3f_2705_);
lean_inc(v_orderedRingInst_x3f_2704_);
lean_inc(v_commRingInst_x3f_2703_);
lean_inc(v_ringInst_x3f_2702_);
lean_inc(v_noNatDivInst_x3f_2701_);
lean_inc(v_isLinearInst_x3f_2700_);
lean_inc(v_orderedAddInst_x3f_2699_);
lean_inc(v_isPreorderInst_x3f_2698_);
lean_inc(v_lawfulOrderLTInst_x3f_2697_);
lean_inc(v_ltInst_x3f_2696_);
lean_inc(v_leInst_x3f_2695_);
lean_inc(v_intModuleInst_2694_);
lean_inc(v_u_2693_);
lean_inc(v_type_2692_);
lean_inc(v_ringId_x3f_2691_);
lean_inc(v_id_2690_);
lean_dec(v_v_2689_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2746_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2736_; lean_object* v_xs_x27_2737_; lean_object* v___x_2738_; lean_object* v___x_2740_; 
v___x_2736_ = lean_box(0);
v_xs_x27_2737_ = lean_array_fset(v_structs_2676_, v___y_2673_, v___x_2736_);
v___x_2738_ = l_Lean_PersistentArray_push___redArg(v_ignored_2732_, v_a_2674_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 41, v___x_2738_);
v___x_2740_ = v___x_2734_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_id_2690_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v_ringId_x3f_2691_);
lean_ctor_set(v_reuseFailAlloc_2745_, 2, v_type_2692_);
lean_ctor_set(v_reuseFailAlloc_2745_, 3, v_u_2693_);
lean_ctor_set(v_reuseFailAlloc_2745_, 4, v_intModuleInst_2694_);
lean_ctor_set(v_reuseFailAlloc_2745_, 5, v_leInst_x3f_2695_);
lean_ctor_set(v_reuseFailAlloc_2745_, 6, v_ltInst_x3f_2696_);
lean_ctor_set(v_reuseFailAlloc_2745_, 7, v_lawfulOrderLTInst_x3f_2697_);
lean_ctor_set(v_reuseFailAlloc_2745_, 8, v_isPreorderInst_x3f_2698_);
lean_ctor_set(v_reuseFailAlloc_2745_, 9, v_orderedAddInst_x3f_2699_);
lean_ctor_set(v_reuseFailAlloc_2745_, 10, v_isLinearInst_x3f_2700_);
lean_ctor_set(v_reuseFailAlloc_2745_, 11, v_noNatDivInst_x3f_2701_);
lean_ctor_set(v_reuseFailAlloc_2745_, 12, v_ringInst_x3f_2702_);
lean_ctor_set(v_reuseFailAlloc_2745_, 13, v_commRingInst_x3f_2703_);
lean_ctor_set(v_reuseFailAlloc_2745_, 14, v_orderedRingInst_x3f_2704_);
lean_ctor_set(v_reuseFailAlloc_2745_, 15, v_fieldInst_x3f_2705_);
lean_ctor_set(v_reuseFailAlloc_2745_, 16, v_charInst_x3f_2706_);
lean_ctor_set(v_reuseFailAlloc_2745_, 17, v_zero_2707_);
lean_ctor_set(v_reuseFailAlloc_2745_, 18, v_ofNatZero_2708_);
lean_ctor_set(v_reuseFailAlloc_2745_, 19, v_one_x3f_2709_);
lean_ctor_set(v_reuseFailAlloc_2745_, 20, v_leFn_x3f_2710_);
lean_ctor_set(v_reuseFailAlloc_2745_, 21, v_ltFn_x3f_2711_);
lean_ctor_set(v_reuseFailAlloc_2745_, 22, v_addFn_2712_);
lean_ctor_set(v_reuseFailAlloc_2745_, 23, v_zsmulFn_2713_);
lean_ctor_set(v_reuseFailAlloc_2745_, 24, v_nsmulFn_2714_);
lean_ctor_set(v_reuseFailAlloc_2745_, 25, v_zsmulFn_x3f_2715_);
lean_ctor_set(v_reuseFailAlloc_2745_, 26, v_nsmulFn_x3f_2716_);
lean_ctor_set(v_reuseFailAlloc_2745_, 27, v_homomulFn_x3f_2717_);
lean_ctor_set(v_reuseFailAlloc_2745_, 28, v_subFn_2718_);
lean_ctor_set(v_reuseFailAlloc_2745_, 29, v_negFn_2719_);
lean_ctor_set(v_reuseFailAlloc_2745_, 30, v_vars_2720_);
lean_ctor_set(v_reuseFailAlloc_2745_, 31, v_varMap_2721_);
lean_ctor_set(v_reuseFailAlloc_2745_, 32, v_lowers_2722_);
lean_ctor_set(v_reuseFailAlloc_2745_, 33, v_uppers_2723_);
lean_ctor_set(v_reuseFailAlloc_2745_, 34, v_diseqs_2724_);
lean_ctor_set(v_reuseFailAlloc_2745_, 35, v_assignment_2725_);
lean_ctor_set(v_reuseFailAlloc_2745_, 36, v_conflict_x3f_2727_);
lean_ctor_set(v_reuseFailAlloc_2745_, 37, v_diseqSplits_2728_);
lean_ctor_set(v_reuseFailAlloc_2745_, 38, v_elimEqs_2729_);
lean_ctor_set(v_reuseFailAlloc_2745_, 39, v_elimStack_2730_);
lean_ctor_set(v_reuseFailAlloc_2745_, 40, v_occurs_2731_);
lean_ctor_set(v_reuseFailAlloc_2745_, 41, v___x_2738_);
lean_ctor_set_uint8(v_reuseFailAlloc_2745_, sizeof(void*)*42, v_caseSplits_2726_);
v___x_2740_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2741_ = lean_array_fset(v_xs_x27_2737_, v___y_2673_, v___x_2740_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2741_);
v___x_2743_ = v___x_2687_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_typeIdOf_2677_);
lean_ctor_set(v_reuseFailAlloc_2744_, 2, v_exprToStructId_2678_);
lean_ctor_set(v_reuseFailAlloc_2744_, 3, v_exprToStructIdEntries_2679_);
lean_ctor_set(v_reuseFailAlloc_2744_, 4, v_forbiddenNatModules_2680_);
lean_ctor_set(v_reuseFailAlloc_2744_, 5, v_natStructs_2681_);
lean_ctor_set(v_reuseFailAlloc_2744_, 6, v_natTypeIdOf_2682_);
lean_ctor_set(v_reuseFailAlloc_2744_, 7, v_exprToNatStructId_2683_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed(lean_object* v___y_2756_, lean_object* v_a_2757_, lean_object* v_s_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0(v___y_2756_, v_a_2757_, v_s_2758_);
lean_dec(v___y_2756_);
return v_res_2759_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3(void){
_start:
{
lean_object* v_cls_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v_cls_2767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_2769_ = l_Lean_Name_append(v___x_2768_, v_cls_2767_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(lean_object* v_c_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_){
_start:
{
lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v_options_2808_; uint8_t v_hasTrace_2809_; 
v_options_2808_ = lean_ctor_get(v_a_2780_, 2);
v_hasTrace_2809_ = lean_ctor_get_uint8(v_options_2808_, sizeof(void*)*1);
if (v_hasTrace_2809_ == 0)
{
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
v___y_2794_ = v_a_2781_;
goto v___jp_2783_;
}
else
{
lean_object* v_inheritedTraceOptions_2810_; lean_object* v_cls_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; 
v_inheritedTraceOptions_2810_ = lean_ctor_get(v_a_2780_, 13);
v_cls_2811_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__2));
v___x_2812_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___closed__3);
v___x_2813_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2810_, v_options_2808_, v___x_2812_);
if (v___x_2813_ == 0)
{
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
v___y_2794_ = v_a_2781_;
goto v___jp_2783_;
}
else
{
lean_object* v___x_2814_; 
v___x_2814_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref(v___x_2814_);
v___x_2816_ = l_Lean_MessageData_ofExpr(v_a_2815_);
v___x_2817_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_2811_, v___x_2816_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_dec_ref(v___x_2817_);
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
v___y_2794_ = v_a_2781_;
goto v___jp_2783_;
}
else
{
return v___x_2817_;
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
v_a_2818_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2814_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2814_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
}
v___jp_2783_:
{
lean_object* v___x_2795_; 
v___x_2795_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_2770_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v___f_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2796_);
lean_dec_ref(v___x_2795_);
lean_inc(v___y_2784_);
v___f_2797_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2797_, 0, v___y_2784_);
lean_closure_set(v___f_2797_, 1, v_a_2796_);
v___x_2798_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2799_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2798_, v___f_2797_, v___y_2785_);
return v___x_2799_;
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
v_a_2800_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2795_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2795_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore___boxed(lean_object* v_c_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
lean_dec(v_a_2829_);
lean_dec(v_a_2828_);
lean_dec(v_a_2827_);
lean_dec_ref(v_c_2826_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(lean_object* v_c_u2082_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v_fileName_2853_; lean_object* v_fileMap_2854_; lean_object* v_options_2855_; lean_object* v_currRecDepth_2856_; lean_object* v_maxRecDepth_2857_; lean_object* v_ref_2858_; lean_object* v_currNamespace_2859_; lean_object* v_openDecls_2860_; lean_object* v_initHeartbeats_2861_; lean_object* v_maxHeartbeats_2862_; lean_object* v_quotContext_2863_; lean_object* v_currMacroScope_2864_; uint8_t v_diag_2865_; lean_object* v_cancelTk_x3f_2866_; uint8_t v_suppressElabErrors_2867_; lean_object* v_inheritedTraceOptions_2868_; uint8_t v___x_2869_; 
v_fileName_2853_ = lean_ctor_get(v_a_2850_, 0);
lean_inc_ref(v_fileName_2853_);
v_fileMap_2854_ = lean_ctor_get(v_a_2850_, 1);
lean_inc_ref(v_fileMap_2854_);
v_options_2855_ = lean_ctor_get(v_a_2850_, 2);
lean_inc_ref(v_options_2855_);
v_currRecDepth_2856_ = lean_ctor_get(v_a_2850_, 3);
lean_inc(v_currRecDepth_2856_);
v_maxRecDepth_2857_ = lean_ctor_get(v_a_2850_, 4);
lean_inc(v_maxRecDepth_2857_);
v_ref_2858_ = lean_ctor_get(v_a_2850_, 5);
lean_inc(v_ref_2858_);
v_currNamespace_2859_ = lean_ctor_get(v_a_2850_, 6);
lean_inc(v_currNamespace_2859_);
v_openDecls_2860_ = lean_ctor_get(v_a_2850_, 7);
lean_inc(v_openDecls_2860_);
v_initHeartbeats_2861_ = lean_ctor_get(v_a_2850_, 8);
lean_inc(v_initHeartbeats_2861_);
v_maxHeartbeats_2862_ = lean_ctor_get(v_a_2850_, 9);
lean_inc(v_maxHeartbeats_2862_);
v_quotContext_2863_ = lean_ctor_get(v_a_2850_, 10);
lean_inc(v_quotContext_2863_);
v_currMacroScope_2864_ = lean_ctor_get(v_a_2850_, 11);
lean_inc(v_currMacroScope_2864_);
v_diag_2865_ = lean_ctor_get_uint8(v_a_2850_, sizeof(void*)*14);
v_cancelTk_x3f_2866_ = lean_ctor_get(v_a_2850_, 12);
lean_inc(v_cancelTk_x3f_2866_);
v_suppressElabErrors_2867_ = lean_ctor_get_uint8(v_a_2850_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2868_ = lean_ctor_get(v_a_2850_, 13);
lean_inc_ref(v_inheritedTraceOptions_2868_);
lean_dec_ref(v_a_2850_);
v___x_2869_ = lean_nat_dec_eq(v_currRecDepth_2856_, v_maxRecDepth_2857_);
if (v___x_2869_ == 0)
{
lean_object* v_p_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v_p_2870_ = lean_ctor_get(v_c_u2082_2840_, 0);
v___x_2871_ = lean_unsigned_to_nat(1u);
v___x_2872_ = lean_nat_add(v_currRecDepth_2856_, v___x_2871_);
lean_dec(v_currRecDepth_2856_);
v___x_2873_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2873_, 0, v_fileName_2853_);
lean_ctor_set(v___x_2873_, 1, v_fileMap_2854_);
lean_ctor_set(v___x_2873_, 2, v_options_2855_);
lean_ctor_set(v___x_2873_, 3, v___x_2872_);
lean_ctor_set(v___x_2873_, 4, v_maxRecDepth_2857_);
lean_ctor_set(v___x_2873_, 5, v_ref_2858_);
lean_ctor_set(v___x_2873_, 6, v_currNamespace_2859_);
lean_ctor_set(v___x_2873_, 7, v_openDecls_2860_);
lean_ctor_set(v___x_2873_, 8, v_initHeartbeats_2861_);
lean_ctor_set(v___x_2873_, 9, v_maxHeartbeats_2862_);
lean_ctor_set(v___x_2873_, 10, v_quotContext_2863_);
lean_ctor_set(v___x_2873_, 11, v_currMacroScope_2864_);
lean_ctor_set(v___x_2873_, 12, v_cancelTk_x3f_2866_);
lean_ctor_set(v___x_2873_, 13, v_inheritedTraceOptions_2868_);
lean_ctor_set_uint8(v___x_2873_, sizeof(void*)*14, v_diag_2865_);
lean_ctor_set_uint8(v___x_2873_, sizeof(void*)*14 + 1, v_suppressElabErrors_2867_);
v___x_2874_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2870_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v___x_2873_, v_a_2851_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2912_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2877_ = v___x_2874_;
v_isShared_2878_ = v_isSharedCheck_2912_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2874_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2912_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
if (lean_obj_tag(v_a_2875_) == 1)
{
lean_object* v_val_2879_; lean_object* v_snd_2880_; lean_object* v_snd_2881_; lean_object* v_fst_2882_; lean_object* v_fst_2883_; lean_object* v_p_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_del_object(v___x_2877_);
v_val_2879_ = lean_ctor_get(v_a_2875_, 0);
lean_inc(v_val_2879_);
lean_dec_ref(v_a_2875_);
v_snd_2880_ = lean_ctor_get(v_val_2879_, 1);
lean_inc(v_snd_2880_);
v_snd_2881_ = lean_ctor_get(v_snd_2880_, 1);
lean_inc(v_snd_2881_);
v_fst_2882_ = lean_ctor_get(v_val_2879_, 0);
lean_inc(v_fst_2882_);
lean_dec(v_val_2879_);
v_fst_2883_ = lean_ctor_get(v_snd_2880_, 0);
lean_inc(v_fst_2883_);
lean_dec(v_snd_2880_);
v_p_2884_ = lean_ctor_get(v_snd_2881_, 0);
v___x_2885_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_2884_, v_fst_2883_);
lean_inc_ref(v_c_u2082_2840_);
v___x_2886_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v___x_2885_, v_fst_2883_, v_snd_2881_, v_fst_2882_, v_c_u2082_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v___x_2873_, v_a_2851_);
lean_dec(v_fst_2883_);
lean_dec(v___x_2885_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_a_2887_; 
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2887_);
lean_dec_ref(v___x_2886_);
if (lean_obj_tag(v_a_2887_) == 1)
{
lean_object* v_val_2888_; 
lean_dec_ref(v_c_u2082_2840_);
v_val_2888_ = lean_ctor_get(v_a_2887_, 0);
lean_inc(v_val_2888_);
lean_dec_ref(v_a_2887_);
v_c_u2082_2840_ = v_val_2888_;
v_a_2850_ = v___x_2873_;
goto _start;
}
else
{
lean_object* v___x_2890_; 
lean_dec(v_a_2887_);
v___x_2890_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_c_u2082_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v___x_2873_, v_a_2851_);
lean_dec_ref(v___x_2873_);
lean_dec_ref(v_c_u2082_2840_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2898_; 
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2898_ == 0)
{
lean_object* v_unused_2899_; 
v_unused_2899_ = lean_ctor_get(v___x_2890_, 0);
lean_dec(v_unused_2899_);
v___x_2892_ = v___x_2890_;
v_isShared_2893_ = v_isSharedCheck_2898_;
goto v_resetjp_2891_;
}
else
{
lean_dec(v___x_2890_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2898_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2894_ = lean_box(0);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v___x_2894_);
v___x_2896_ = v___x_2892_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
v_a_2900_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2890_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2890_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2873_);
lean_dec_ref(v_c_u2082_2840_);
return v___x_2886_;
}
}
else
{
lean_object* v___x_2908_; lean_object* v___x_2910_; 
lean_dec(v_a_2875_);
lean_dec_ref(v___x_2873_);
v___x_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2908_, 0, v_c_u2082_2840_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 0, v___x_2908_);
v___x_2910_ = v___x_2877_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2908_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec_ref(v___x_2873_);
lean_dec_ref(v_c_u2082_2840_);
v_a_2913_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2874_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2874_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
else
{
lean_object* v___x_2921_; 
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
lean_dec_ref(v_c_u2082_2840_);
v___x_2921_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts_spec__0___redArg(v_ref_2858_);
return v___x_2921_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f___boxed(lean_object* v_c_u2082_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_u2082_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_);
lean_dec(v_a_2933_);
lean_dec(v_a_2931_);
lean_dec_ref(v_a_2930_);
lean_dec(v_a_2929_);
lean_dec_ref(v_a_2928_);
lean_dec(v_a_2927_);
lean_dec_ref(v_a_2926_);
lean_dec(v_a_2925_);
lean_dec(v_a_2924_);
lean_dec(v_a_2923_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(lean_object* v_val_2936_, lean_object* v_x_2937_, size_t v_x_2938_, size_t v_x_2939_){
_start:
{
if (lean_obj_tag(v_x_2937_) == 0)
{
lean_object* v_cs_2940_; size_t v_j_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; uint8_t v___x_2944_; 
v_cs_2940_ = lean_ctor_get(v_x_2937_, 0);
v_j_2941_ = lean_usize_shift_right(v_x_2938_, v_x_2939_);
v___x_2942_ = lean_usize_to_nat(v_j_2941_);
v___x_2943_ = lean_array_get_size(v_cs_2940_);
v___x_2944_ = lean_nat_dec_lt(v___x_2942_, v___x_2943_);
if (v___x_2944_ == 0)
{
lean_dec(v___x_2942_);
lean_dec_ref(v_val_2936_);
return v_x_2937_;
}
else
{
lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2962_; 
lean_inc_ref(v_cs_2940_);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_x_2937_);
if (v_isSharedCheck_2962_ == 0)
{
lean_object* v_unused_2963_; 
v_unused_2963_ = lean_ctor_get(v_x_2937_, 0);
lean_dec(v_unused_2963_);
v___x_2946_ = v_x_2937_;
v_isShared_2947_ = v_isSharedCheck_2962_;
goto v_resetjp_2945_;
}
else
{
lean_dec(v_x_2937_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2962_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
size_t v___x_2948_; size_t v___x_2949_; size_t v___x_2950_; size_t v_i_2951_; size_t v___x_2952_; size_t v_shift_2953_; lean_object* v_v_2954_; lean_object* v___x_2955_; lean_object* v_xs_x27_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2960_; 
v___x_2948_ = ((size_t)1ULL);
v___x_2949_ = lean_usize_shift_left(v___x_2948_, v_x_2939_);
v___x_2950_ = lean_usize_sub(v___x_2949_, v___x_2948_);
v_i_2951_ = lean_usize_land(v_x_2938_, v___x_2950_);
v___x_2952_ = ((size_t)5ULL);
v_shift_2953_ = lean_usize_sub(v_x_2939_, v___x_2952_);
v_v_2954_ = lean_array_fget(v_cs_2940_, v___x_2942_);
v___x_2955_ = lean_box(0);
v_xs_x27_2956_ = lean_array_fset(v_cs_2940_, v___x_2942_, v___x_2955_);
v___x_2957_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2936_, v_v_2954_, v_i_2951_, v_shift_2953_);
v___x_2958_ = lean_array_fset(v_xs_x27_2956_, v___x_2942_, v___x_2957_);
lean_dec(v___x_2942_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 0, v___x_2958_);
v___x_2960_ = v___x_2946_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2958_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
else
{
lean_object* v_vs_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; uint8_t v___x_2967_; 
v_vs_2964_ = lean_ctor_get(v_x_2937_, 0);
v___x_2965_ = lean_usize_to_nat(v_x_2938_);
v___x_2966_ = lean_array_get_size(v_vs_2964_);
v___x_2967_ = lean_nat_dec_lt(v___x_2965_, v___x_2966_);
if (v___x_2967_ == 0)
{
lean_dec(v___x_2965_);
lean_dec_ref(v_val_2936_);
return v_x_2937_;
}
else
{
lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2979_; 
lean_inc_ref(v_vs_2964_);
v_isSharedCheck_2979_ = !lean_is_exclusive(v_x_2937_);
if (v_isSharedCheck_2979_ == 0)
{
lean_object* v_unused_2980_; 
v_unused_2980_ = lean_ctor_get(v_x_2937_, 0);
lean_dec(v_unused_2980_);
v___x_2969_ = v_x_2937_;
v_isShared_2970_ = v_isSharedCheck_2979_;
goto v_resetjp_2968_;
}
else
{
lean_dec(v_x_2937_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2979_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v_v_2971_; lean_object* v___x_2972_; lean_object* v_xs_x27_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2977_; 
v_v_2971_ = lean_array_fget(v_vs_2964_, v___x_2965_);
v___x_2972_ = lean_box(0);
v_xs_x27_2973_ = lean_array_fset(v_vs_2964_, v___x_2965_, v___x_2972_);
v___x_2974_ = l_Lean_PersistentArray_push___redArg(v_v_2971_, v_val_2936_);
v___x_2975_ = lean_array_fset(v_xs_x27_2973_, v___x_2965_, v___x_2974_);
lean_dec(v___x_2965_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 0, v___x_2975_);
v___x_2977_ = v___x_2969_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2975_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0___boxed(lean_object* v_val_2981_, lean_object* v_x_2982_, lean_object* v_x_2983_, lean_object* v_x_2984_){
_start:
{
size_t v_x_53643__boxed_2985_; size_t v_x_53644__boxed_2986_; lean_object* v_res_2987_; 
v_x_53643__boxed_2985_ = lean_unbox_usize(v_x_2983_);
lean_dec(v_x_2983_);
v_x_53644__boxed_2986_ = lean_unbox_usize(v_x_2984_);
lean_dec(v_x_2984_);
v_res_2987_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2981_, v_x_2982_, v_x_53643__boxed_2985_, v_x_53644__boxed_2986_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(lean_object* v_val_2988_, lean_object* v_t_2989_, lean_object* v_i_2990_){
_start:
{
lean_object* v_root_2991_; lean_object* v_tail_2992_; lean_object* v_size_2993_; size_t v_shift_2994_; lean_object* v_tailOff_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3019_; 
v_root_2991_ = lean_ctor_get(v_t_2989_, 0);
v_tail_2992_ = lean_ctor_get(v_t_2989_, 1);
v_size_2993_ = lean_ctor_get(v_t_2989_, 2);
v_shift_2994_ = lean_ctor_get_usize(v_t_2989_, 4);
v_tailOff_2995_ = lean_ctor_get(v_t_2989_, 3);
v_isSharedCheck_3019_ = !lean_is_exclusive(v_t_2989_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_2997_ = v_t_2989_;
v_isShared_2998_ = v_isSharedCheck_3019_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_tailOff_2995_);
lean_inc(v_size_2993_);
lean_inc(v_tail_2992_);
lean_inc(v_root_2991_);
lean_dec(v_t_2989_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3019_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
uint8_t v___x_2999_; 
v___x_2999_ = lean_nat_dec_le(v_tailOff_2995_, v_i_2990_);
if (v___x_2999_ == 0)
{
size_t v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3003_; 
v___x_3000_ = lean_usize_of_nat(v_i_2990_);
v___x_3001_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0_spec__0(v_val_2988_, v_root_2991_, v___x_3000_, v_shift_2994_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 0, v___x_3001_);
v___x_3003_ = v___x_2997_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_3001_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_tail_2992_);
lean_ctor_set(v_reuseFailAlloc_3004_, 2, v_size_2993_);
lean_ctor_set(v_reuseFailAlloc_3004_, 3, v_tailOff_2995_);
lean_ctor_set_usize(v_reuseFailAlloc_3004_, 4, v_shift_2994_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
else
{
lean_object* v___x_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; 
v___x_3005_ = lean_nat_sub(v_i_2990_, v_tailOff_2995_);
v___x_3006_ = lean_array_get_size(v_tail_2992_);
v___x_3007_ = lean_nat_dec_lt(v___x_3005_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3009_; 
lean_dec(v___x_3005_);
lean_dec_ref(v_val_2988_);
if (v_isShared_2998_ == 0)
{
v___x_3009_ = v___x_2997_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_root_2991_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v_tail_2992_);
lean_ctor_set(v_reuseFailAlloc_3010_, 2, v_size_2993_);
lean_ctor_set(v_reuseFailAlloc_3010_, 3, v_tailOff_2995_);
lean_ctor_set_usize(v_reuseFailAlloc_3010_, 4, v_shift_2994_);
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
lean_object* v_v_3011_; lean_object* v___x_3012_; lean_object* v_xs_x27_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3017_; 
v_v_3011_ = lean_array_fget(v_tail_2992_, v___x_3005_);
v___x_3012_ = lean_box(0);
v_xs_x27_3013_ = lean_array_fset(v_tail_2992_, v___x_3005_, v___x_3012_);
v___x_3014_ = l_Lean_PersistentArray_push___redArg(v_v_3011_, v_val_2988_);
v___x_3015_ = lean_array_fset(v_xs_x27_3013_, v___x_3005_, v___x_3014_);
lean_dec(v___x_3005_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 1, v___x_3015_);
v___x_3017_ = v___x_2997_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_root_2991_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v___x_3015_);
lean_ctor_set(v_reuseFailAlloc_3018_, 2, v_size_2993_);
lean_ctor_set(v_reuseFailAlloc_3018_, 3, v_tailOff_2995_);
lean_ctor_set_usize(v_reuseFailAlloc_3018_, 4, v_shift_2994_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0___boxed(lean_object* v_val_3020_, lean_object* v_t_3021_, lean_object* v_i_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3020_, v_t_3021_, v_i_3022_);
lean_dec(v_i_3022_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(lean_object* v___y_3024_, lean_object* v_val_3025_, lean_object* v_v_3026_, lean_object* v_s_3027_){
_start:
{
lean_object* v_structs_3028_; lean_object* v_typeIdOf_3029_; lean_object* v_exprToStructId_3030_; lean_object* v_exprToStructIdEntries_3031_; lean_object* v_forbiddenNatModules_3032_; lean_object* v_natStructs_3033_; lean_object* v_natTypeIdOf_3034_; lean_object* v_exprToNatStructId_3035_; lean_object* v___x_3036_; uint8_t v___x_3037_; 
v_structs_3028_ = lean_ctor_get(v_s_3027_, 0);
v_typeIdOf_3029_ = lean_ctor_get(v_s_3027_, 1);
v_exprToStructId_3030_ = lean_ctor_get(v_s_3027_, 2);
v_exprToStructIdEntries_3031_ = lean_ctor_get(v_s_3027_, 3);
v_forbiddenNatModules_3032_ = lean_ctor_get(v_s_3027_, 4);
v_natStructs_3033_ = lean_ctor_get(v_s_3027_, 5);
v_natTypeIdOf_3034_ = lean_ctor_get(v_s_3027_, 6);
v_exprToNatStructId_3035_ = lean_ctor_get(v_s_3027_, 7);
v___x_3036_ = lean_array_get_size(v_structs_3028_);
v___x_3037_ = lean_nat_dec_lt(v___y_3024_, v___x_3036_);
if (v___x_3037_ == 0)
{
lean_dec_ref(v_val_3025_);
return v_s_3027_;
}
else
{
lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3099_; 
lean_inc_ref(v_exprToNatStructId_3035_);
lean_inc_ref(v_natTypeIdOf_3034_);
lean_inc_ref(v_natStructs_3033_);
lean_inc_ref(v_forbiddenNatModules_3032_);
lean_inc_ref(v_exprToStructIdEntries_3031_);
lean_inc_ref(v_exprToStructId_3030_);
lean_inc_ref(v_typeIdOf_3029_);
lean_inc_ref(v_structs_3028_);
v_isSharedCheck_3099_ = !lean_is_exclusive(v_s_3027_);
if (v_isSharedCheck_3099_ == 0)
{
lean_object* v_unused_3100_; lean_object* v_unused_3101_; lean_object* v_unused_3102_; lean_object* v_unused_3103_; lean_object* v_unused_3104_; lean_object* v_unused_3105_; lean_object* v_unused_3106_; lean_object* v_unused_3107_; 
v_unused_3100_ = lean_ctor_get(v_s_3027_, 7);
lean_dec(v_unused_3100_);
v_unused_3101_ = lean_ctor_get(v_s_3027_, 6);
lean_dec(v_unused_3101_);
v_unused_3102_ = lean_ctor_get(v_s_3027_, 5);
lean_dec(v_unused_3102_);
v_unused_3103_ = lean_ctor_get(v_s_3027_, 4);
lean_dec(v_unused_3103_);
v_unused_3104_ = lean_ctor_get(v_s_3027_, 3);
lean_dec(v_unused_3104_);
v_unused_3105_ = lean_ctor_get(v_s_3027_, 2);
lean_dec(v_unused_3105_);
v_unused_3106_ = lean_ctor_get(v_s_3027_, 1);
lean_dec(v_unused_3106_);
v_unused_3107_ = lean_ctor_get(v_s_3027_, 0);
lean_dec(v_unused_3107_);
v___x_3039_ = v_s_3027_;
v_isShared_3040_ = v_isSharedCheck_3099_;
goto v_resetjp_3038_;
}
else
{
lean_dec(v_s_3027_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3099_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v_v_3041_; lean_object* v_id_3042_; lean_object* v_ringId_x3f_3043_; lean_object* v_type_3044_; lean_object* v_u_3045_; lean_object* v_intModuleInst_3046_; lean_object* v_leInst_x3f_3047_; lean_object* v_ltInst_x3f_3048_; lean_object* v_lawfulOrderLTInst_x3f_3049_; lean_object* v_isPreorderInst_x3f_3050_; lean_object* v_orderedAddInst_x3f_3051_; lean_object* v_isLinearInst_x3f_3052_; lean_object* v_noNatDivInst_x3f_3053_; lean_object* v_ringInst_x3f_3054_; lean_object* v_commRingInst_x3f_3055_; lean_object* v_orderedRingInst_x3f_3056_; lean_object* v_fieldInst_x3f_3057_; lean_object* v_charInst_x3f_3058_; lean_object* v_zero_3059_; lean_object* v_ofNatZero_3060_; lean_object* v_one_x3f_3061_; lean_object* v_leFn_x3f_3062_; lean_object* v_ltFn_x3f_3063_; lean_object* v_addFn_3064_; lean_object* v_zsmulFn_3065_; lean_object* v_nsmulFn_3066_; lean_object* v_zsmulFn_x3f_3067_; lean_object* v_nsmulFn_x3f_3068_; lean_object* v_homomulFn_x3f_3069_; lean_object* v_subFn_3070_; lean_object* v_negFn_3071_; lean_object* v_vars_3072_; lean_object* v_varMap_3073_; lean_object* v_lowers_3074_; lean_object* v_uppers_3075_; lean_object* v_diseqs_3076_; lean_object* v_assignment_3077_; uint8_t v_caseSplits_3078_; lean_object* v_conflict_x3f_3079_; lean_object* v_diseqSplits_3080_; lean_object* v_elimEqs_3081_; lean_object* v_elimStack_3082_; lean_object* v_occurs_3083_; lean_object* v_ignored_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3098_; 
v_v_3041_ = lean_array_fget(v_structs_3028_, v___y_3024_);
v_id_3042_ = lean_ctor_get(v_v_3041_, 0);
v_ringId_x3f_3043_ = lean_ctor_get(v_v_3041_, 1);
v_type_3044_ = lean_ctor_get(v_v_3041_, 2);
v_u_3045_ = lean_ctor_get(v_v_3041_, 3);
v_intModuleInst_3046_ = lean_ctor_get(v_v_3041_, 4);
v_leInst_x3f_3047_ = lean_ctor_get(v_v_3041_, 5);
v_ltInst_x3f_3048_ = lean_ctor_get(v_v_3041_, 6);
v_lawfulOrderLTInst_x3f_3049_ = lean_ctor_get(v_v_3041_, 7);
v_isPreorderInst_x3f_3050_ = lean_ctor_get(v_v_3041_, 8);
v_orderedAddInst_x3f_3051_ = lean_ctor_get(v_v_3041_, 9);
v_isLinearInst_x3f_3052_ = lean_ctor_get(v_v_3041_, 10);
v_noNatDivInst_x3f_3053_ = lean_ctor_get(v_v_3041_, 11);
v_ringInst_x3f_3054_ = lean_ctor_get(v_v_3041_, 12);
v_commRingInst_x3f_3055_ = lean_ctor_get(v_v_3041_, 13);
v_orderedRingInst_x3f_3056_ = lean_ctor_get(v_v_3041_, 14);
v_fieldInst_x3f_3057_ = lean_ctor_get(v_v_3041_, 15);
v_charInst_x3f_3058_ = lean_ctor_get(v_v_3041_, 16);
v_zero_3059_ = lean_ctor_get(v_v_3041_, 17);
v_ofNatZero_3060_ = lean_ctor_get(v_v_3041_, 18);
v_one_x3f_3061_ = lean_ctor_get(v_v_3041_, 19);
v_leFn_x3f_3062_ = lean_ctor_get(v_v_3041_, 20);
v_ltFn_x3f_3063_ = lean_ctor_get(v_v_3041_, 21);
v_addFn_3064_ = lean_ctor_get(v_v_3041_, 22);
v_zsmulFn_3065_ = lean_ctor_get(v_v_3041_, 23);
v_nsmulFn_3066_ = lean_ctor_get(v_v_3041_, 24);
v_zsmulFn_x3f_3067_ = lean_ctor_get(v_v_3041_, 25);
v_nsmulFn_x3f_3068_ = lean_ctor_get(v_v_3041_, 26);
v_homomulFn_x3f_3069_ = lean_ctor_get(v_v_3041_, 27);
v_subFn_3070_ = lean_ctor_get(v_v_3041_, 28);
v_negFn_3071_ = lean_ctor_get(v_v_3041_, 29);
v_vars_3072_ = lean_ctor_get(v_v_3041_, 30);
v_varMap_3073_ = lean_ctor_get(v_v_3041_, 31);
v_lowers_3074_ = lean_ctor_get(v_v_3041_, 32);
v_uppers_3075_ = lean_ctor_get(v_v_3041_, 33);
v_diseqs_3076_ = lean_ctor_get(v_v_3041_, 34);
v_assignment_3077_ = lean_ctor_get(v_v_3041_, 35);
v_caseSplits_3078_ = lean_ctor_get_uint8(v_v_3041_, sizeof(void*)*42);
v_conflict_x3f_3079_ = lean_ctor_get(v_v_3041_, 36);
v_diseqSplits_3080_ = lean_ctor_get(v_v_3041_, 37);
v_elimEqs_3081_ = lean_ctor_get(v_v_3041_, 38);
v_elimStack_3082_ = lean_ctor_get(v_v_3041_, 39);
v_occurs_3083_ = lean_ctor_get(v_v_3041_, 40);
v_ignored_3084_ = lean_ctor_get(v_v_3041_, 41);
v_isSharedCheck_3098_ = !lean_is_exclusive(v_v_3041_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3086_ = v_v_3041_;
v_isShared_3087_ = v_isSharedCheck_3098_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_ignored_3084_);
lean_inc(v_occurs_3083_);
lean_inc(v_elimStack_3082_);
lean_inc(v_elimEqs_3081_);
lean_inc(v_diseqSplits_3080_);
lean_inc(v_conflict_x3f_3079_);
lean_inc(v_assignment_3077_);
lean_inc(v_diseqs_3076_);
lean_inc(v_uppers_3075_);
lean_inc(v_lowers_3074_);
lean_inc(v_varMap_3073_);
lean_inc(v_vars_3072_);
lean_inc(v_negFn_3071_);
lean_inc(v_subFn_3070_);
lean_inc(v_homomulFn_x3f_3069_);
lean_inc(v_nsmulFn_x3f_3068_);
lean_inc(v_zsmulFn_x3f_3067_);
lean_inc(v_nsmulFn_3066_);
lean_inc(v_zsmulFn_3065_);
lean_inc(v_addFn_3064_);
lean_inc(v_ltFn_x3f_3063_);
lean_inc(v_leFn_x3f_3062_);
lean_inc(v_one_x3f_3061_);
lean_inc(v_ofNatZero_3060_);
lean_inc(v_zero_3059_);
lean_inc(v_charInst_x3f_3058_);
lean_inc(v_fieldInst_x3f_3057_);
lean_inc(v_orderedRingInst_x3f_3056_);
lean_inc(v_commRingInst_x3f_3055_);
lean_inc(v_ringInst_x3f_3054_);
lean_inc(v_noNatDivInst_x3f_3053_);
lean_inc(v_isLinearInst_x3f_3052_);
lean_inc(v_orderedAddInst_x3f_3051_);
lean_inc(v_isPreorderInst_x3f_3050_);
lean_inc(v_lawfulOrderLTInst_x3f_3049_);
lean_inc(v_ltInst_x3f_3048_);
lean_inc(v_leInst_x3f_3047_);
lean_inc(v_intModuleInst_3046_);
lean_inc(v_u_3045_);
lean_inc(v_type_3044_);
lean_inc(v_ringId_x3f_3043_);
lean_inc(v_id_3042_);
lean_dec(v_v_3041_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3098_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3088_; lean_object* v_xs_x27_3089_; lean_object* v___x_3090_; lean_object* v___x_3092_; 
v___x_3088_ = lean_box(0);
v_xs_x27_3089_ = lean_array_fset(v_structs_3028_, v___y_3024_, v___x_3088_);
v___x_3090_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert_spec__0(v_val_3025_, v_diseqs_3076_, v_v_3026_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 34, v___x_3090_);
v___x_3092_ = v___x_3086_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_id_3042_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v_ringId_x3f_3043_);
lean_ctor_set(v_reuseFailAlloc_3097_, 2, v_type_3044_);
lean_ctor_set(v_reuseFailAlloc_3097_, 3, v_u_3045_);
lean_ctor_set(v_reuseFailAlloc_3097_, 4, v_intModuleInst_3046_);
lean_ctor_set(v_reuseFailAlloc_3097_, 5, v_leInst_x3f_3047_);
lean_ctor_set(v_reuseFailAlloc_3097_, 6, v_ltInst_x3f_3048_);
lean_ctor_set(v_reuseFailAlloc_3097_, 7, v_lawfulOrderLTInst_x3f_3049_);
lean_ctor_set(v_reuseFailAlloc_3097_, 8, v_isPreorderInst_x3f_3050_);
lean_ctor_set(v_reuseFailAlloc_3097_, 9, v_orderedAddInst_x3f_3051_);
lean_ctor_set(v_reuseFailAlloc_3097_, 10, v_isLinearInst_x3f_3052_);
lean_ctor_set(v_reuseFailAlloc_3097_, 11, v_noNatDivInst_x3f_3053_);
lean_ctor_set(v_reuseFailAlloc_3097_, 12, v_ringInst_x3f_3054_);
lean_ctor_set(v_reuseFailAlloc_3097_, 13, v_commRingInst_x3f_3055_);
lean_ctor_set(v_reuseFailAlloc_3097_, 14, v_orderedRingInst_x3f_3056_);
lean_ctor_set(v_reuseFailAlloc_3097_, 15, v_fieldInst_x3f_3057_);
lean_ctor_set(v_reuseFailAlloc_3097_, 16, v_charInst_x3f_3058_);
lean_ctor_set(v_reuseFailAlloc_3097_, 17, v_zero_3059_);
lean_ctor_set(v_reuseFailAlloc_3097_, 18, v_ofNatZero_3060_);
lean_ctor_set(v_reuseFailAlloc_3097_, 19, v_one_x3f_3061_);
lean_ctor_set(v_reuseFailAlloc_3097_, 20, v_leFn_x3f_3062_);
lean_ctor_set(v_reuseFailAlloc_3097_, 21, v_ltFn_x3f_3063_);
lean_ctor_set(v_reuseFailAlloc_3097_, 22, v_addFn_3064_);
lean_ctor_set(v_reuseFailAlloc_3097_, 23, v_zsmulFn_3065_);
lean_ctor_set(v_reuseFailAlloc_3097_, 24, v_nsmulFn_3066_);
lean_ctor_set(v_reuseFailAlloc_3097_, 25, v_zsmulFn_x3f_3067_);
lean_ctor_set(v_reuseFailAlloc_3097_, 26, v_nsmulFn_x3f_3068_);
lean_ctor_set(v_reuseFailAlloc_3097_, 27, v_homomulFn_x3f_3069_);
lean_ctor_set(v_reuseFailAlloc_3097_, 28, v_subFn_3070_);
lean_ctor_set(v_reuseFailAlloc_3097_, 29, v_negFn_3071_);
lean_ctor_set(v_reuseFailAlloc_3097_, 30, v_vars_3072_);
lean_ctor_set(v_reuseFailAlloc_3097_, 31, v_varMap_3073_);
lean_ctor_set(v_reuseFailAlloc_3097_, 32, v_lowers_3074_);
lean_ctor_set(v_reuseFailAlloc_3097_, 33, v_uppers_3075_);
lean_ctor_set(v_reuseFailAlloc_3097_, 34, v___x_3090_);
lean_ctor_set(v_reuseFailAlloc_3097_, 35, v_assignment_3077_);
lean_ctor_set(v_reuseFailAlloc_3097_, 36, v_conflict_x3f_3079_);
lean_ctor_set(v_reuseFailAlloc_3097_, 37, v_diseqSplits_3080_);
lean_ctor_set(v_reuseFailAlloc_3097_, 38, v_elimEqs_3081_);
lean_ctor_set(v_reuseFailAlloc_3097_, 39, v_elimStack_3082_);
lean_ctor_set(v_reuseFailAlloc_3097_, 40, v_occurs_3083_);
lean_ctor_set(v_reuseFailAlloc_3097_, 41, v_ignored_3084_);
lean_ctor_set_uint8(v_reuseFailAlloc_3097_, sizeof(void*)*42, v_caseSplits_3078_);
v___x_3092_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
lean_object* v___x_3093_; lean_object* v___x_3095_; 
v___x_3093_ = lean_array_fset(v_xs_x27_3089_, v___y_3024_, v___x_3092_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 0, v___x_3093_);
v___x_3095_ = v___x_3039_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3093_);
lean_ctor_set(v_reuseFailAlloc_3096_, 1, v_typeIdOf_3029_);
lean_ctor_set(v_reuseFailAlloc_3096_, 2, v_exprToStructId_3030_);
lean_ctor_set(v_reuseFailAlloc_3096_, 3, v_exprToStructIdEntries_3031_);
lean_ctor_set(v_reuseFailAlloc_3096_, 4, v_forbiddenNatModules_3032_);
lean_ctor_set(v_reuseFailAlloc_3096_, 5, v_natStructs_3033_);
lean_ctor_set(v_reuseFailAlloc_3096_, 6, v_natTypeIdOf_3034_);
lean_ctor_set(v_reuseFailAlloc_3096_, 7, v_exprToNatStructId_3035_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed(lean_object* v___y_3108_, lean_object* v_val_3109_, lean_object* v_v_3110_, lean_object* v_s_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0(v___y_3108_, v_val_3109_, v_v_3110_, v_s_3111_);
lean_dec(v_v_3110_);
lean_dec(v___y_3108_);
return v_res_3112_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2(void){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3120_ = l_Lean_Name_append(v___x_3119_, v___x_3118_);
return v___x_3120_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3127_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3129_ = l_Lean_Name_append(v___x_3128_, v___x_3127_);
return v___x_3129_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7(void){
_start:
{
lean_object* v_cls_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v_cls_3134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_3136_ = l_Lean_Name_append(v___x_3135_, v_cls_3134_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(lean_object* v_c_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_){
_start:
{
lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v_options_3208_; lean_object* v_inheritedTraceOptions_3209_; uint8_t v_hasTrace_3210_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; 
v_options_3208_ = lean_ctor_get(v_a_3147_, 2);
v_inheritedTraceOptions_3209_ = lean_ctor_get(v_a_3147_, 13);
v_hasTrace_3210_ = lean_ctor_get_uint8(v_options_3208_, sizeof(void*)*1);
if (v_hasTrace_3210_ == 0)
{
v___y_3212_ = v_a_3138_;
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
goto v___jp_3211_;
}
else
{
lean_object* v_cls_3281_; lean_object* v___x_3282_; uint8_t v___x_3283_; 
v_cls_3281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_3282_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_3283_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3209_, v_options_3208_, v___x_3282_);
if (v___x_3283_ == 0)
{
v___y_3212_ = v_a_3138_;
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
goto v___jp_3211_;
}
else
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_c_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
lean_dec_ref(v___x_3284_);
v___x_3286_ = l_Lean_MessageData_ofExpr(v_a_3285_);
v___x_3287_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_3281_, v___x_3286_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_dec_ref(v___x_3287_);
v___y_3212_ = v_a_3138_;
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
goto v___jp_3211_;
}
else
{
lean_dec_ref(v_c_3137_);
return v___x_3287_;
}
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
lean_dec_ref(v_c_3137_);
v_a_3288_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3284_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3284_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
}
v___jp_3150_:
{
lean_object* v___x_3167_; 
v___x_3167_ = l_Lean_Grind_Linarith_Poly_updateOccs(v___y_3154_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v___f_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
lean_dec_ref(v___x_3167_);
lean_inc(v___y_3156_);
v___f_3168_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3168_, 0, v___y_3156_);
lean_closure_set(v___f_3168_, 1, v___y_3152_);
lean_closure_set(v___f_3168_, 2, v___y_3151_);
v___x_3169_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3170_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3169_, v___f_3168_, v___y_3157_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v___x_3171_; 
lean_dec_ref(v___x_3170_);
v___x_3171_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3184_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3174_ = v___x_3171_;
v_isShared_3175_ = v_isSharedCheck_3184_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3171_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3184_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
uint8_t v___x_3176_; uint8_t v___x_3177_; uint8_t v___x_3178_; 
v___x_3176_ = 0;
v___x_3177_ = lean_unbox(v_a_3172_);
lean_dec(v_a_3172_);
v___x_3178_ = l_Lean_instBEqLBool_beq(v___x_3177_, v___x_3176_);
if (v___x_3178_ == 0)
{
lean_object* v___x_3179_; lean_object* v___x_3181_; 
lean_dec(v___y_3153_);
v___x_3179_ = lean_box(0);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v___x_3179_);
v___x_3181_ = v___x_3174_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3179_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
else
{
lean_object* v___x_3183_; 
lean_del_object(v___x_3174_);
v___x_3183_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v___y_3153_, v___y_3156_, v___y_3157_);
return v___x_3183_;
}
}
}
else
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3192_; 
lean_dec(v___y_3153_);
v_a_3185_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3187_ = v___x_3171_;
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3171_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3190_; 
if (v_isShared_3188_ == 0)
{
v___x_3190_ = v___x_3187_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3185_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
else
{
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3153_);
return v___x_3170_;
}
}
else
{
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
return v___x_3167_;
}
}
v___jp_3193_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3206_, 0, v___y_3194_);
v___x_3207_ = l_Lean_Meta_Grind_Arith_Linear_setInconsistent(v___x_3206_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
return v___x_3207_;
}
v___jp_3211_:
{
lean_object* v___x_3223_; 
lean_inc_ref(v___y_3221_);
v___x_3223_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applySubsts_x3f(v_c_3137_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3272_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3226_ = v___x_3223_;
v_isShared_3227_ = v_isSharedCheck_3272_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3223_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3272_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
if (lean_obj_tag(v_a_3224_) == 1)
{
lean_object* v_val_3228_; lean_object* v_p_3229_; 
lean_del_object(v___x_3226_);
v_val_3228_ = lean_ctor_get(v_a_3224_, 0);
lean_inc(v_val_3228_);
lean_dec_ref(v_a_3224_);
v_p_3229_ = lean_ctor_get(v_val_3228_, 0);
if (lean_obj_tag(v_p_3229_) == 0)
{
lean_object* v_options_3230_; uint8_t v_hasTrace_3231_; 
v_options_3230_ = lean_ctor_get(v___y_3221_, 2);
v_hasTrace_3231_ = lean_ctor_get_uint8(v_options_3230_, sizeof(void*)*1);
if (v_hasTrace_3231_ == 0)
{
v___y_3194_ = v_val_3228_;
v___y_3195_ = v___y_3212_;
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
goto v___jp_3193_;
}
else
{
lean_object* v_inheritedTraceOptions_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; uint8_t v___x_3235_; 
v_inheritedTraceOptions_3232_ = lean_ctor_get(v___y_3221_, 13);
v___x_3233_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__1));
v___x_3234_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__2);
v___x_3235_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3232_, v_options_3230_, v___x_3234_);
if (v___x_3235_ == 0)
{
v___y_3194_ = v_val_3228_;
v___y_3195_ = v___y_3212_;
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
goto v___jp_3193_;
}
else
{
lean_object* v___x_3236_; 
v___x_3236_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3228_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
lean_inc(v_a_3237_);
lean_dec_ref(v___x_3236_);
v___x_3238_ = l_Lean_MessageData_ofExpr(v_a_3237_);
v___x_3239_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3233_, v___x_3238_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_dec_ref(v___x_3239_);
v___y_3194_ = v_val_3228_;
v___y_3195_ = v___y_3212_;
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
goto v___jp_3193_;
}
else
{
lean_dec(v_val_3228_);
return v___x_3239_;
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec(v_val_3228_);
v_a_3240_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3236_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3236_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
}
}
else
{
lean_object* v_options_3248_; uint8_t v_hasTrace_3249_; 
lean_inc_ref(v_p_3229_);
v_options_3248_ = lean_ctor_get(v___y_3221_, 2);
v_hasTrace_3249_ = lean_ctor_get_uint8(v_options_3248_, sizeof(void*)*1);
if (v_hasTrace_3249_ == 0)
{
lean_object* v_v_3250_; 
v_v_3250_ = lean_ctor_get(v_p_3229_, 1);
lean_inc_n(v_v_3250_, 2);
lean_inc(v_val_3228_);
v___y_3151_ = v_v_3250_;
v___y_3152_ = v_val_3228_;
v___y_3153_ = v_v_3250_;
v___y_3154_ = v_p_3229_;
v___y_3155_ = v_val_3228_;
v___y_3156_ = v___y_3212_;
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
goto v___jp_3150_;
}
else
{
lean_object* v_v_3251_; lean_object* v_inheritedTraceOptions_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; 
v_v_3251_ = lean_ctor_get(v_p_3229_, 1);
lean_inc(v_v_3251_);
v_inheritedTraceOptions_3252_ = lean_ctor_get(v___y_3221_, 13);
v___x_3253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_3254_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_3255_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3252_, v_options_3248_, v___x_3254_);
if (v___x_3255_ == 0)
{
lean_inc(v_val_3228_);
lean_inc(v_v_3251_);
v___y_3151_ = v_v_3251_;
v___y_3152_ = v_val_3228_;
v___y_3153_ = v_v_3251_;
v___y_3154_ = v_p_3229_;
v___y_3155_ = v_val_3228_;
v___y_3156_ = v___y_3212_;
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
goto v___jp_3150_;
}
else
{
lean_object* v___x_3256_; 
v___x_3256_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f_spec__0(v_val_3228_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_a_3257_);
lean_dec_ref(v___x_3256_);
v___x_3258_ = l_Lean_MessageData_ofExpr(v_a_3257_);
v___x_3259_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_3253_, v___x_3258_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_dec_ref(v___x_3259_);
lean_inc(v_val_3228_);
lean_inc(v_v_3251_);
v___y_3151_ = v_v_3251_;
v___y_3152_ = v_val_3228_;
v___y_3153_ = v_v_3251_;
v___y_3154_ = v_p_3229_;
v___y_3155_ = v_val_3228_;
v___y_3156_ = v___y_3212_;
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
goto v___jp_3150_;
}
else
{
lean_dec(v_v_3251_);
lean_dec_ref(v_p_3229_);
lean_dec(v_val_3228_);
return v___x_3259_;
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_dec(v_v_3251_);
lean_dec_ref(v_p_3229_);
lean_dec(v_val_3228_);
v_a_3260_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3256_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3256_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
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
}
}
}
else
{
lean_object* v___x_3268_; lean_object* v___x_3270_; 
lean_dec(v_a_3224_);
v___x_3268_ = lean_box(0);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 0, v___x_3268_);
v___x_3270_ = v___x_3226_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3268_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
else
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
v_a_3273_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___x_3223_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3223_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___boxed(lean_object* v_c_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_c_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_);
lean_dec(v_a_3307_);
lean_dec_ref(v_a_3306_);
lean_dec(v_a_3305_);
lean_dec_ref(v_a_3304_);
lean_dec(v_a_3303_);
lean_dec_ref(v_a_3302_);
lean_dec(v_a_3301_);
lean_dec_ref(v_a_3300_);
lean_dec(v_a_3299_);
lean_dec(v_a_3298_);
lean_dec(v_a_3297_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_3310_, lean_object* v_as_3311_, size_t v_sz_3312_, size_t v_i_3313_, lean_object* v_b_3314_){
_start:
{
uint8_t v___x_3315_; 
v___x_3315_ = lean_usize_dec_lt(v_i_3313_, v_sz_3312_);
if (v___x_3315_ == 0)
{
return v_b_3314_;
}
else
{
lean_object* v_snd_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3357_; 
v_snd_3316_ = lean_ctor_get(v_b_3314_, 1);
v_isSharedCheck_3357_ = !lean_is_exclusive(v_b_3314_);
if (v_isSharedCheck_3357_ == 0)
{
lean_object* v_unused_3358_; 
v_unused_3358_ = lean_ctor_get(v_b_3314_, 0);
lean_dec(v_unused_3358_);
v___x_3318_ = v_b_3314_;
v_isShared_3319_ = v_isSharedCheck_3357_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_snd_3316_);
lean_dec(v_b_3314_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3357_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v_fst_3320_; lean_object* v_snd_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3356_; 
v_fst_3320_ = lean_ctor_get(v_snd_3316_, 0);
v_snd_3321_ = lean_ctor_get(v_snd_3316_, 1);
v_isSharedCheck_3356_ = !lean_is_exclusive(v_snd_3316_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3323_ = v_snd_3316_;
v_isShared_3324_ = v_isSharedCheck_3356_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_snd_3321_);
lean_inc(v_fst_3320_);
lean_dec(v_snd_3316_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3356_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v_a_3325_; lean_object* v_p_3326_; lean_object* v___x_3327_; lean_object* v_a_3329_; lean_object* v_b_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; 
v_a_3325_ = lean_array_uget(v_as_3311_, v_i_3313_);
v_p_3326_ = lean_ctor_get(v_a_3325_, 0);
v___x_3327_ = lean_box(0);
v_b_3336_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3326_, v_x_3310_);
v___x_3337_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3338_ = lean_int_dec_eq(v_b_3336_, v___x_3337_);
if (v___x_3338_ == 0)
{
lean_object* v___x_3340_; 
lean_inc(v_a_3325_);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 1, v_a_3325_);
lean_ctor_set(v___x_3318_, 0, v_b_3336_);
v___x_3340_ = v___x_3318_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_b_3336_);
lean_ctor_set(v_reuseFailAlloc_3351_, 1, v_a_3325_);
v___x_3340_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3348_; 
v_isSharedCheck_3348_ = !lean_is_exclusive(v_a_3325_);
if (v_isSharedCheck_3348_ == 0)
{
lean_object* v_unused_3349_; lean_object* v_unused_3350_; 
v_unused_3349_ = lean_ctor_get(v_a_3325_, 1);
lean_dec(v_unused_3349_);
v_unused_3350_ = lean_ctor_get(v_a_3325_, 0);
lean_dec(v_unused_3350_);
v___x_3342_ = v_a_3325_;
v_isShared_3343_ = v_isSharedCheck_3348_;
goto v_resetjp_3341_;
}
else
{
lean_dec(v_a_3325_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3348_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v_todo_3344_; lean_object* v___x_3346_; 
v_todo_3344_ = lean_array_push(v_snd_3321_, v___x_3340_);
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 1, v_todo_3344_);
lean_ctor_set(v___x_3342_, 0, v_fst_3320_);
v___x_3346_ = v___x_3342_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_fst_3320_);
lean_ctor_set(v_reuseFailAlloc_3347_, 1, v_todo_3344_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
v_a_3329_ = v___x_3346_;
goto v___jp_3328_;
}
}
}
}
else
{
lean_object* v_cs_x27_3352_; lean_object* v___x_3354_; 
lean_dec(v_b_3336_);
v_cs_x27_3352_ = l_Lean_PersistentArray_push___redArg(v_fst_3320_, v_a_3325_);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 1, v_snd_3321_);
lean_ctor_set(v___x_3318_, 0, v_cs_x27_3352_);
v___x_3354_ = v___x_3318_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_cs_x27_3352_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v_snd_3321_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
v_a_3329_ = v___x_3354_;
goto v___jp_3328_;
}
}
v___jp_3328_:
{
lean_object* v___x_3331_; 
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 1, v_a_3329_);
lean_ctor_set(v___x_3323_, 0, v___x_3327_);
v___x_3331_ = v___x_3323_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3327_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_a_3329_);
v___x_3331_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
size_t v___x_3332_; size_t v___x_3333_; 
v___x_3332_ = ((size_t)1ULL);
v___x_3333_ = lean_usize_add(v_i_3313_, v___x_3332_);
v_i_3313_ = v___x_3333_;
v_b_3314_ = v___x_3331_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_x_3359_, lean_object* v_as_3360_, lean_object* v_sz_3361_, lean_object* v_i_3362_, lean_object* v_b_3363_){
_start:
{
size_t v_sz_boxed_3364_; size_t v_i_boxed_3365_; lean_object* v_res_3366_; 
v_sz_boxed_3364_ = lean_unbox_usize(v_sz_3361_);
lean_dec(v_sz_3361_);
v_i_boxed_3365_ = lean_unbox_usize(v_i_3362_);
lean_dec(v_i_3362_);
v_res_3366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3359_, v_as_3360_, v_sz_boxed_3364_, v_i_boxed_3365_, v_b_3363_);
lean_dec_ref(v_as_3360_);
lean_dec(v_x_3359_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(lean_object* v_x_3367_, lean_object* v_as_3368_, size_t v_sz_3369_, size_t v_i_3370_, lean_object* v_b_3371_){
_start:
{
uint8_t v___x_3372_; 
v___x_3372_ = lean_usize_dec_lt(v_i_3370_, v_sz_3369_);
if (v___x_3372_ == 0)
{
return v_b_3371_;
}
else
{
lean_object* v_snd_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3414_; 
v_snd_3373_ = lean_ctor_get(v_b_3371_, 1);
v_isSharedCheck_3414_ = !lean_is_exclusive(v_b_3371_);
if (v_isSharedCheck_3414_ == 0)
{
lean_object* v_unused_3415_; 
v_unused_3415_ = lean_ctor_get(v_b_3371_, 0);
lean_dec(v_unused_3415_);
v___x_3375_ = v_b_3371_;
v_isShared_3376_ = v_isSharedCheck_3414_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_snd_3373_);
lean_dec(v_b_3371_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3414_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v_fst_3377_; lean_object* v_snd_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3413_; 
v_fst_3377_ = lean_ctor_get(v_snd_3373_, 0);
v_snd_3378_ = lean_ctor_get(v_snd_3373_, 1);
v_isSharedCheck_3413_ = !lean_is_exclusive(v_snd_3373_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3380_ = v_snd_3373_;
v_isShared_3381_ = v_isSharedCheck_3413_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_snd_3378_);
lean_inc(v_fst_3377_);
lean_dec(v_snd_3373_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3413_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v_a_3382_; lean_object* v_p_3383_; lean_object* v___x_3384_; lean_object* v_a_3386_; lean_object* v_b_3393_; lean_object* v___x_3394_; uint8_t v___x_3395_; 
v_a_3382_ = lean_array_uget(v_as_3368_, v_i_3370_);
v_p_3383_ = lean_ctor_get(v_a_3382_, 0);
v___x_3384_ = lean_box(0);
v_b_3393_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3383_, v_x_3367_);
v___x_3394_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3395_ = lean_int_dec_eq(v_b_3393_, v___x_3394_);
if (v___x_3395_ == 0)
{
lean_object* v___x_3397_; 
lean_inc(v_a_3382_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 1, v_a_3382_);
lean_ctor_set(v___x_3375_, 0, v_b_3393_);
v___x_3397_ = v___x_3375_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_b_3393_);
lean_ctor_set(v_reuseFailAlloc_3408_, 1, v_a_3382_);
v___x_3397_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3405_; 
v_isSharedCheck_3405_ = !lean_is_exclusive(v_a_3382_);
if (v_isSharedCheck_3405_ == 0)
{
lean_object* v_unused_3406_; lean_object* v_unused_3407_; 
v_unused_3406_ = lean_ctor_get(v_a_3382_, 1);
lean_dec(v_unused_3406_);
v_unused_3407_ = lean_ctor_get(v_a_3382_, 0);
lean_dec(v_unused_3407_);
v___x_3399_ = v_a_3382_;
v_isShared_3400_ = v_isSharedCheck_3405_;
goto v_resetjp_3398_;
}
else
{
lean_dec(v_a_3382_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3405_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v_todo_3401_; lean_object* v___x_3403_; 
v_todo_3401_ = lean_array_push(v_snd_3378_, v___x_3397_);
if (v_isShared_3400_ == 0)
{
lean_ctor_set(v___x_3399_, 1, v_todo_3401_);
lean_ctor_set(v___x_3399_, 0, v_fst_3377_);
v___x_3403_ = v___x_3399_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_fst_3377_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v_todo_3401_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
v_a_3386_ = v___x_3403_;
goto v___jp_3385_;
}
}
}
}
else
{
lean_object* v_cs_x27_3409_; lean_object* v___x_3411_; 
lean_dec(v_b_3393_);
v_cs_x27_3409_ = l_Lean_PersistentArray_push___redArg(v_fst_3377_, v_a_3382_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 1, v_snd_3378_);
lean_ctor_set(v___x_3375_, 0, v_cs_x27_3409_);
v___x_3411_ = v___x_3375_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_cs_x27_3409_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_snd_3378_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
v_a_3386_ = v___x_3411_;
goto v___jp_3385_;
}
}
v___jp_3385_:
{
lean_object* v___x_3388_; 
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 1, v_a_3386_);
lean_ctor_set(v___x_3380_, 0, v___x_3384_);
v___x_3388_ = v___x_3380_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3384_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_a_3386_);
v___x_3388_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
size_t v___x_3389_; size_t v___x_3390_; lean_object* v___x_3391_; 
v___x_3389_ = ((size_t)1ULL);
v___x_3390_ = lean_usize_add(v_i_3370_, v___x_3389_);
v___x_3391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2_spec__5(v_x_3367_, v_as_3368_, v_sz_3369_, v___x_3390_, v___x_3388_);
return v___x_3391_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_3416_, lean_object* v_as_3417_, lean_object* v_sz_3418_, lean_object* v_i_3419_, lean_object* v_b_3420_){
_start:
{
size_t v_sz_boxed_3421_; size_t v_i_boxed_3422_; lean_object* v_res_3423_; 
v_sz_boxed_3421_ = lean_unbox_usize(v_sz_3418_);
lean_dec(v_sz_3418_);
v_i_boxed_3422_ = lean_unbox_usize(v_i_3419_);
lean_dec(v_i_3419_);
v_res_3423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3416_, v_as_3417_, v_sz_boxed_3421_, v_i_boxed_3422_, v_b_3420_);
lean_dec_ref(v_as_3417_);
lean_dec(v_x_3416_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_x_3424_, lean_object* v_as_3425_, size_t v_sz_3426_, size_t v_i_3427_, lean_object* v_b_3428_){
_start:
{
uint8_t v___x_3429_; 
v___x_3429_ = lean_usize_dec_lt(v_i_3427_, v_sz_3426_);
if (v___x_3429_ == 0)
{
return v_b_3428_;
}
else
{
lean_object* v_snd_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3471_; 
v_snd_3430_ = lean_ctor_get(v_b_3428_, 1);
v_isSharedCheck_3471_ = !lean_is_exclusive(v_b_3428_);
if (v_isSharedCheck_3471_ == 0)
{
lean_object* v_unused_3472_; 
v_unused_3472_ = lean_ctor_get(v_b_3428_, 0);
lean_dec(v_unused_3472_);
v___x_3432_ = v_b_3428_;
v_isShared_3433_ = v_isSharedCheck_3471_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_snd_3430_);
lean_dec(v_b_3428_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3471_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v_fst_3434_; lean_object* v_snd_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3470_; 
v_fst_3434_ = lean_ctor_get(v_snd_3430_, 0);
v_snd_3435_ = lean_ctor_get(v_snd_3430_, 1);
v_isSharedCheck_3470_ = !lean_is_exclusive(v_snd_3430_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3437_ = v_snd_3430_;
v_isShared_3438_ = v_isSharedCheck_3470_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_snd_3435_);
lean_inc(v_fst_3434_);
lean_dec(v_snd_3430_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3470_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v_a_3439_; lean_object* v_p_3440_; lean_object* v___x_3441_; lean_object* v_a_3443_; lean_object* v_b_3450_; lean_object* v___x_3451_; uint8_t v___x_3452_; 
v_a_3439_ = lean_array_uget(v_as_3425_, v_i_3427_);
v_p_3440_ = lean_ctor_get(v_a_3439_, 0);
v___x_3441_ = lean_box(0);
v_b_3450_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3440_, v_x_3424_);
v___x_3451_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3452_ = lean_int_dec_eq(v_b_3450_, v___x_3451_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3454_; 
lean_inc(v_a_3439_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v_a_3439_);
lean_ctor_set(v___x_3432_, 0, v_b_3450_);
v___x_3454_ = v___x_3432_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_b_3450_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_a_3439_);
v___x_3454_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3462_; 
v_isSharedCheck_3462_ = !lean_is_exclusive(v_a_3439_);
if (v_isSharedCheck_3462_ == 0)
{
lean_object* v_unused_3463_; lean_object* v_unused_3464_; 
v_unused_3463_ = lean_ctor_get(v_a_3439_, 1);
lean_dec(v_unused_3463_);
v_unused_3464_ = lean_ctor_get(v_a_3439_, 0);
lean_dec(v_unused_3464_);
v___x_3456_ = v_a_3439_;
v_isShared_3457_ = v_isSharedCheck_3462_;
goto v_resetjp_3455_;
}
else
{
lean_dec(v_a_3439_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3462_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v_todo_3458_; lean_object* v___x_3460_; 
v_todo_3458_ = lean_array_push(v_snd_3435_, v___x_3454_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 1, v_todo_3458_);
lean_ctor_set(v___x_3456_, 0, v_fst_3434_);
v___x_3460_ = v___x_3456_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_fst_3434_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_todo_3458_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
v_a_3443_ = v___x_3460_;
goto v___jp_3442_;
}
}
}
}
else
{
lean_object* v_cs_x27_3466_; lean_object* v___x_3468_; 
lean_dec(v_b_3450_);
v_cs_x27_3466_ = l_Lean_PersistentArray_push___redArg(v_fst_3434_, v_a_3439_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v_snd_3435_);
lean_ctor_set(v___x_3432_, 0, v_cs_x27_3466_);
v___x_3468_ = v___x_3432_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_cs_x27_3466_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_snd_3435_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
v_a_3443_ = v___x_3468_;
goto v___jp_3442_;
}
}
v___jp_3442_:
{
lean_object* v___x_3445_; 
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 1, v_a_3443_);
lean_ctor_set(v___x_3437_, 0, v___x_3441_);
v___x_3445_ = v___x_3437_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3441_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_a_3443_);
v___x_3445_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
size_t v___x_3446_; size_t v___x_3447_; 
v___x_3446_ = ((size_t)1ULL);
v___x_3447_ = lean_usize_add(v_i_3427_, v___x_3446_);
v_i_3427_ = v___x_3447_;
v_b_3428_ = v___x_3445_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_x_3473_, lean_object* v_as_3474_, lean_object* v_sz_3475_, lean_object* v_i_3476_, lean_object* v_b_3477_){
_start:
{
size_t v_sz_boxed_3478_; size_t v_i_boxed_3479_; lean_object* v_res_3480_; 
v_sz_boxed_3478_ = lean_unbox_usize(v_sz_3475_);
lean_dec(v_sz_3475_);
v_i_boxed_3479_ = lean_unbox_usize(v_i_3476_);
lean_dec(v_i_3476_);
v_res_3480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3473_, v_as_3474_, v_sz_boxed_3478_, v_i_boxed_3479_, v_b_3477_);
lean_dec_ref(v_as_3474_);
lean_dec(v_x_3473_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_3481_, lean_object* v_as_3482_, size_t v_sz_3483_, size_t v_i_3484_, lean_object* v_b_3485_){
_start:
{
uint8_t v___x_3486_; 
v___x_3486_ = lean_usize_dec_lt(v_i_3484_, v_sz_3483_);
if (v___x_3486_ == 0)
{
return v_b_3485_;
}
else
{
lean_object* v_snd_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3528_; 
v_snd_3487_ = lean_ctor_get(v_b_3485_, 1);
v_isSharedCheck_3528_ = !lean_is_exclusive(v_b_3485_);
if (v_isSharedCheck_3528_ == 0)
{
lean_object* v_unused_3529_; 
v_unused_3529_ = lean_ctor_get(v_b_3485_, 0);
lean_dec(v_unused_3529_);
v___x_3489_ = v_b_3485_;
v_isShared_3490_ = v_isSharedCheck_3528_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_snd_3487_);
lean_dec(v_b_3485_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3528_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v_fst_3491_; lean_object* v_snd_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3527_; 
v_fst_3491_ = lean_ctor_get(v_snd_3487_, 0);
v_snd_3492_ = lean_ctor_get(v_snd_3487_, 1);
v_isSharedCheck_3527_ = !lean_is_exclusive(v_snd_3487_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3494_ = v_snd_3487_;
v_isShared_3495_ = v_isSharedCheck_3527_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_snd_3492_);
lean_inc(v_fst_3491_);
lean_dec(v_snd_3487_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3527_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v_a_3496_; lean_object* v_p_3497_; lean_object* v___x_3498_; lean_object* v_a_3500_; lean_object* v_b_3507_; lean_object* v___x_3508_; uint8_t v___x_3509_; 
v_a_3496_ = lean_array_uget(v_as_3482_, v_i_3484_);
v_p_3497_ = lean_ctor_get(v_a_3496_, 0);
v___x_3498_ = lean_box(0);
v_b_3507_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_3497_, v_x_3481_);
v___x_3508_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_3509_ = lean_int_dec_eq(v_b_3507_, v___x_3508_);
if (v___x_3509_ == 0)
{
lean_object* v___x_3511_; 
lean_inc(v_a_3496_);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 1, v_a_3496_);
lean_ctor_set(v___x_3489_, 0, v_b_3507_);
v___x_3511_ = v___x_3489_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_b_3507_);
lean_ctor_set(v_reuseFailAlloc_3522_, 1, v_a_3496_);
v___x_3511_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3519_; 
v_isSharedCheck_3519_ = !lean_is_exclusive(v_a_3496_);
if (v_isSharedCheck_3519_ == 0)
{
lean_object* v_unused_3520_; lean_object* v_unused_3521_; 
v_unused_3520_ = lean_ctor_get(v_a_3496_, 1);
lean_dec(v_unused_3520_);
v_unused_3521_ = lean_ctor_get(v_a_3496_, 0);
lean_dec(v_unused_3521_);
v___x_3513_ = v_a_3496_;
v_isShared_3514_ = v_isSharedCheck_3519_;
goto v_resetjp_3512_;
}
else
{
lean_dec(v_a_3496_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3519_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v_todo_3515_; lean_object* v___x_3517_; 
v_todo_3515_ = lean_array_push(v_snd_3492_, v___x_3511_);
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 1, v_todo_3515_);
lean_ctor_set(v___x_3513_, 0, v_fst_3491_);
v___x_3517_ = v___x_3513_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_fst_3491_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v_todo_3515_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
v_a_3500_ = v___x_3517_;
goto v___jp_3499_;
}
}
}
}
else
{
lean_object* v_cs_x27_3523_; lean_object* v___x_3525_; 
lean_dec(v_b_3507_);
v_cs_x27_3523_ = l_Lean_PersistentArray_push___redArg(v_fst_3491_, v_a_3496_);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 1, v_snd_3492_);
lean_ctor_set(v___x_3489_, 0, v_cs_x27_3523_);
v___x_3525_ = v___x_3489_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_cs_x27_3523_);
lean_ctor_set(v_reuseFailAlloc_3526_, 1, v_snd_3492_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
v_a_3500_ = v___x_3525_;
goto v___jp_3499_;
}
}
v___jp_3499_:
{
lean_object* v___x_3502_; 
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 1, v_a_3500_);
lean_ctor_set(v___x_3494_, 0, v___x_3498_);
v___x_3502_ = v___x_3494_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v_a_3500_);
v___x_3502_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
size_t v___x_3503_; size_t v___x_3504_; lean_object* v___x_3505_; 
v___x_3503_ = ((size_t)1ULL);
v___x_3504_ = lean_usize_add(v_i_3484_, v___x_3503_);
v___x_3505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3_spec__4(v_x_3481_, v_as_3482_, v_sz_3483_, v___x_3504_, v___x_3502_);
return v___x_3505_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_3530_, lean_object* v_as_3531_, lean_object* v_sz_3532_, lean_object* v_i_3533_, lean_object* v_b_3534_){
_start:
{
size_t v_sz_boxed_3535_; size_t v_i_boxed_3536_; lean_object* v_res_3537_; 
v_sz_boxed_3535_ = lean_unbox_usize(v_sz_3532_);
lean_dec(v_sz_3532_);
v_i_boxed_3536_ = lean_unbox_usize(v_i_3533_);
lean_dec(v_i_3533_);
v_res_3537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3530_, v_as_3531_, v_sz_boxed_3535_, v_i_boxed_3536_, v_b_3534_);
lean_dec_ref(v_as_3531_);
lean_dec(v_x_3530_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(lean_object* v_init_3538_, lean_object* v_x_3539_, lean_object* v_n_3540_, lean_object* v_b_3541_){
_start:
{
if (lean_obj_tag(v_n_3540_) == 0)
{
lean_object* v_cs_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3557_; 
v_cs_3542_ = lean_ctor_get(v_n_3540_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v_n_3540_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3544_ = v_n_3540_;
v_isShared_3545_ = v_isSharedCheck_3557_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_cs_3542_);
lean_dec(v_n_3540_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3557_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; size_t v_sz_3548_; size_t v___x_3549_; lean_object* v___x_3550_; lean_object* v_fst_3551_; 
v___x_3546_ = lean_box(0);
v___x_3547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3546_);
lean_ctor_set(v___x_3547_, 1, v_b_3541_);
v_sz_3548_ = lean_array_size(v_cs_3542_);
v___x_3549_ = ((size_t)0ULL);
v___x_3550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3538_, v_x_3539_, v_cs_3542_, v_sz_3548_, v___x_3549_, v___x_3547_);
lean_dec_ref(v_cs_3542_);
v_fst_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_fst_3551_);
if (lean_obj_tag(v_fst_3551_) == 0)
{
lean_object* v_snd_3552_; lean_object* v___x_3554_; 
v_snd_3552_ = lean_ctor_get(v___x_3550_, 1);
lean_inc(v_snd_3552_);
lean_dec_ref(v___x_3550_);
if (v_isShared_3545_ == 0)
{
lean_ctor_set_tag(v___x_3544_, 1);
lean_ctor_set(v___x_3544_, 0, v_snd_3552_);
v___x_3554_ = v___x_3544_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_snd_3552_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
else
{
lean_object* v_val_3556_; 
lean_dec_ref(v___x_3550_);
lean_del_object(v___x_3544_);
v_val_3556_ = lean_ctor_get(v_fst_3551_, 0);
lean_inc(v_val_3556_);
lean_dec_ref(v_fst_3551_);
return v_val_3556_;
}
}
}
else
{
lean_object* v_vs_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3573_; 
v_vs_3558_ = lean_ctor_get(v_n_3540_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v_n_3540_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3560_ = v_n_3540_;
v_isShared_3561_ = v_isSharedCheck_3573_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_vs_3558_);
lean_dec(v_n_3540_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3573_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; size_t v_sz_3564_; size_t v___x_3565_; lean_object* v___x_3566_; lean_object* v_fst_3567_; 
v___x_3562_ = lean_box(0);
v___x_3563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3562_);
lean_ctor_set(v___x_3563_, 1, v_b_3541_);
v_sz_3564_ = lean_array_size(v_vs_3558_);
v___x_3565_ = ((size_t)0ULL);
v___x_3566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__3(v_x_3539_, v_vs_3558_, v_sz_3564_, v___x_3565_, v___x_3563_);
lean_dec_ref(v_vs_3558_);
v_fst_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_fst_3567_);
if (lean_obj_tag(v_fst_3567_) == 0)
{
lean_object* v_snd_3568_; lean_object* v___x_3570_; 
v_snd_3568_ = lean_ctor_get(v___x_3566_, 1);
lean_inc(v_snd_3568_);
lean_dec_ref(v___x_3566_);
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 0, v_snd_3568_);
v___x_3570_ = v___x_3560_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_snd_3568_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
else
{
lean_object* v_val_3572_; 
lean_dec_ref(v___x_3566_);
lean_del_object(v___x_3560_);
v_val_3572_ = lean_ctor_get(v_fst_3567_, 0);
lean_inc(v_val_3572_);
lean_dec_ref(v_fst_3567_);
return v_val_3572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3574_, lean_object* v_x_3575_, lean_object* v_as_3576_, size_t v_sz_3577_, size_t v_i_3578_, lean_object* v_b_3579_){
_start:
{
uint8_t v___x_3580_; 
v___x_3580_ = lean_usize_dec_lt(v_i_3578_, v_sz_3577_);
if (v___x_3580_ == 0)
{
return v_b_3579_;
}
else
{
lean_object* v_snd_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3599_; 
v_snd_3581_ = lean_ctor_get(v_b_3579_, 1);
v_isSharedCheck_3599_ = !lean_is_exclusive(v_b_3579_);
if (v_isSharedCheck_3599_ == 0)
{
lean_object* v_unused_3600_; 
v_unused_3600_ = lean_ctor_get(v_b_3579_, 0);
lean_dec(v_unused_3600_);
v___x_3583_ = v_b_3579_;
v_isShared_3584_ = v_isSharedCheck_3599_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_snd_3581_);
lean_dec(v_b_3579_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3599_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v_a_3585_; lean_object* v___x_3586_; 
v_a_3585_ = lean_array_uget_borrowed(v_as_3576_, v_i_3578_);
lean_inc(v_snd_3581_);
lean_inc(v_a_3585_);
v___x_3586_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3574_, v_x_3575_, v_a_3585_, v_snd_3581_);
if (lean_obj_tag(v___x_3586_) == 0)
{
lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 0, v___x_3587_);
v___x_3589_ = v___x_3583_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3587_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_snd_3581_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
else
{
lean_object* v_a_3591_; lean_object* v___x_3592_; lean_object* v___x_3594_; 
lean_dec(v_snd_3581_);
v_a_3591_ = lean_ctor_get(v___x_3586_, 0);
lean_inc(v_a_3591_);
lean_dec_ref(v___x_3586_);
v___x_3592_ = lean_box(0);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 1, v_a_3591_);
lean_ctor_set(v___x_3583_, 0, v___x_3592_);
v___x_3594_ = v___x_3583_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3592_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v_a_3591_);
v___x_3594_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
size_t v___x_3595_; size_t v___x_3596_; 
v___x_3595_ = ((size_t)1ULL);
v___x_3596_ = lean_usize_add(v_i_3578_, v___x_3595_);
v_i_3578_ = v___x_3596_;
v_b_3579_ = v___x_3594_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3601_, lean_object* v_x_3602_, lean_object* v_as_3603_, lean_object* v_sz_3604_, lean_object* v_i_3605_, lean_object* v_b_3606_){
_start:
{
size_t v_sz_boxed_3607_; size_t v_i_boxed_3608_; lean_object* v_res_3609_; 
v_sz_boxed_3607_ = lean_unbox_usize(v_sz_3604_);
lean_dec(v_sz_3604_);
v_i_boxed_3608_ = lean_unbox_usize(v_i_3605_);
lean_dec(v_i_3605_);
v_res_3609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1_spec__2(v_init_3601_, v_x_3602_, v_as_3603_, v_sz_boxed_3607_, v_i_boxed_3608_, v_b_3606_);
lean_dec_ref(v_as_3603_);
lean_dec(v_x_3602_);
lean_dec_ref(v_init_3601_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3610_, lean_object* v_x_3611_, lean_object* v_n_3612_, lean_object* v_b_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3610_, v_x_3611_, v_n_3612_, v_b_3613_);
lean_dec(v_x_3611_);
lean_dec_ref(v_init_3610_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(lean_object* v_x_3615_, lean_object* v_t_3616_, lean_object* v_init_3617_){
_start:
{
lean_object* v_root_3618_; lean_object* v_tail_3619_; lean_object* v___x_3620_; 
v_root_3618_ = lean_ctor_get(v_t_3616_, 0);
lean_inc_ref(v_root_3618_);
v_tail_3619_ = lean_ctor_get(v_t_3616_, 1);
lean_inc_ref(v_tail_3619_);
lean_dec_ref(v_t_3616_);
lean_inc_ref(v_init_3617_);
v___x_3620_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__1(v_init_3617_, v_x_3615_, v_root_3618_, v_init_3617_);
lean_dec_ref(v_init_3617_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; 
lean_dec_ref(v_tail_3619_);
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_a_3621_);
lean_dec_ref(v___x_3620_);
return v_a_3621_;
}
else
{
lean_object* v_a_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; size_t v_sz_3625_; size_t v___x_3626_; lean_object* v___x_3627_; lean_object* v_fst_3628_; 
v_a_3622_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_a_3622_);
lean_dec_ref(v___x_3620_);
v___x_3623_ = lean_box(0);
v___x_3624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3623_);
lean_ctor_set(v___x_3624_, 1, v_a_3622_);
v_sz_3625_ = lean_array_size(v_tail_3619_);
v___x_3626_ = ((size_t)0ULL);
v___x_3627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0_spec__2(v_x_3615_, v_tail_3619_, v_sz_3625_, v___x_3626_, v___x_3624_);
lean_dec_ref(v_tail_3619_);
v_fst_3628_ = lean_ctor_get(v___x_3627_, 0);
lean_inc(v_fst_3628_);
if (lean_obj_tag(v_fst_3628_) == 0)
{
lean_object* v_snd_3629_; 
v_snd_3629_ = lean_ctor_get(v___x_3627_, 1);
lean_inc(v_snd_3629_);
lean_dec_ref(v___x_3627_);
return v_snd_3629_;
}
else
{
lean_object* v_val_3630_; 
lean_dec_ref(v___x_3627_);
v_val_3630_ = lean_ctor_get(v_fst_3628_, 0);
lean_inc(v_val_3630_);
lean_dec_ref(v_fst_3628_);
return v_val_3630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0___boxed(lean_object* v_x_3631_, lean_object* v_t_3632_, lean_object* v_init_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3631_, v_t_3632_, v_init_3633_);
lean_dec(v_x_3631_);
return v_res_3634_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3635_ = lean_unsigned_to_nat(32u);
v___x_3636_ = lean_mk_empty_array_with_capacity(v___x_3635_);
v___x_3637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3637_, 0, v___x_3636_);
return v___x_3637_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1(void){
_start:
{
size_t v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v_cs_x27_3643_; 
v___x_3638_ = ((size_t)5ULL);
v___x_3639_ = lean_unsigned_to_nat(0u);
v___x_3640_ = lean_unsigned_to_nat(32u);
v___x_3641_ = lean_mk_empty_array_with_capacity(v___x_3640_);
v___x_3642_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__0);
v_cs_x27_3643_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_cs_x27_3643_, 0, v___x_3642_);
lean_ctor_set(v_cs_x27_3643_, 1, v___x_3641_);
lean_ctor_set(v_cs_x27_3643_, 2, v___x_3639_);
lean_ctor_set(v_cs_x27_3643_, 3, v___x_3639_);
lean_ctor_set_usize(v_cs_x27_3643_, 4, v___x_3638_);
return v_cs_x27_3643_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3(void){
_start:
{
lean_object* v_todo_3646_; lean_object* v_cs_x27_3647_; lean_object* v___x_3648_; 
v_todo_3646_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__2));
v_cs_x27_3647_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__1);
v___x_3648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3648_, 0, v_cs_x27_3647_);
lean_ctor_set(v___x_3648_, 1, v_todo_3646_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(lean_object* v_x_3649_, lean_object* v_cs_3650_){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v_fst_3653_; lean_object* v_snd_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3661_; 
v___x_3651_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3, &l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___closed__3);
v___x_3652_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0_spec__0(v_x_3649_, v_cs_3650_, v___x_3651_);
v_fst_3653_ = lean_ctor_get(v___x_3652_, 0);
v_snd_3654_ = lean_ctor_get(v___x_3652_, 1);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3656_ = v___x_3652_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_snd_3654_);
lean_inc(v_fst_3653_);
lean_dec(v___x_3652_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_fst_3653_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_snd_3654_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0___boxed(lean_object* v_x_3662_, lean_object* v_cs_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3662_, v_cs_3663_);
lean_dec(v_x_3662_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(lean_object* v_x_3665_, lean_object* v_cs_3666_){
_start:
{
lean_object* v___x_3667_; 
v___x_3667_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3665_, v_cs_3666_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs___boxed(lean_object* v_x_3668_, lean_object* v_cs_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs(v_x_3668_, v_cs_3669_);
lean_dec(v_x_3668_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(lean_object* v_a_3671_, lean_object* v_y_3672_, lean_object* v_fst_3673_, lean_object* v_s_3674_){
_start:
{
lean_object* v_structs_3675_; lean_object* v_typeIdOf_3676_; lean_object* v_exprToStructId_3677_; lean_object* v_exprToStructIdEntries_3678_; lean_object* v_forbiddenNatModules_3679_; lean_object* v_natStructs_3680_; lean_object* v_natTypeIdOf_3681_; lean_object* v_exprToNatStructId_3682_; lean_object* v___x_3683_; uint8_t v___x_3684_; 
v_structs_3675_ = lean_ctor_get(v_s_3674_, 0);
v_typeIdOf_3676_ = lean_ctor_get(v_s_3674_, 1);
v_exprToStructId_3677_ = lean_ctor_get(v_s_3674_, 2);
v_exprToStructIdEntries_3678_ = lean_ctor_get(v_s_3674_, 3);
v_forbiddenNatModules_3679_ = lean_ctor_get(v_s_3674_, 4);
v_natStructs_3680_ = lean_ctor_get(v_s_3674_, 5);
v_natTypeIdOf_3681_ = lean_ctor_get(v_s_3674_, 6);
v_exprToNatStructId_3682_ = lean_ctor_get(v_s_3674_, 7);
v___x_3683_ = lean_array_get_size(v_structs_3675_);
v___x_3684_ = lean_nat_dec_lt(v_a_3671_, v___x_3683_);
if (v___x_3684_ == 0)
{
lean_dec_ref(v_fst_3673_);
return v_s_3674_;
}
else
{
lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3746_; 
lean_inc_ref(v_exprToNatStructId_3682_);
lean_inc_ref(v_natTypeIdOf_3681_);
lean_inc_ref(v_natStructs_3680_);
lean_inc_ref(v_forbiddenNatModules_3679_);
lean_inc_ref(v_exprToStructIdEntries_3678_);
lean_inc_ref(v_exprToStructId_3677_);
lean_inc_ref(v_typeIdOf_3676_);
lean_inc_ref(v_structs_3675_);
v_isSharedCheck_3746_ = !lean_is_exclusive(v_s_3674_);
if (v_isSharedCheck_3746_ == 0)
{
lean_object* v_unused_3747_; lean_object* v_unused_3748_; lean_object* v_unused_3749_; lean_object* v_unused_3750_; lean_object* v_unused_3751_; lean_object* v_unused_3752_; lean_object* v_unused_3753_; lean_object* v_unused_3754_; 
v_unused_3747_ = lean_ctor_get(v_s_3674_, 7);
lean_dec(v_unused_3747_);
v_unused_3748_ = lean_ctor_get(v_s_3674_, 6);
lean_dec(v_unused_3748_);
v_unused_3749_ = lean_ctor_get(v_s_3674_, 5);
lean_dec(v_unused_3749_);
v_unused_3750_ = lean_ctor_get(v_s_3674_, 4);
lean_dec(v_unused_3750_);
v_unused_3751_ = lean_ctor_get(v_s_3674_, 3);
lean_dec(v_unused_3751_);
v_unused_3752_ = lean_ctor_get(v_s_3674_, 2);
lean_dec(v_unused_3752_);
v_unused_3753_ = lean_ctor_get(v_s_3674_, 1);
lean_dec(v_unused_3753_);
v_unused_3754_ = lean_ctor_get(v_s_3674_, 0);
lean_dec(v_unused_3754_);
v___x_3686_ = v_s_3674_;
v_isShared_3687_ = v_isSharedCheck_3746_;
goto v_resetjp_3685_;
}
else
{
lean_dec(v_s_3674_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3746_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v_v_3688_; lean_object* v_id_3689_; lean_object* v_ringId_x3f_3690_; lean_object* v_type_3691_; lean_object* v_u_3692_; lean_object* v_intModuleInst_3693_; lean_object* v_leInst_x3f_3694_; lean_object* v_ltInst_x3f_3695_; lean_object* v_lawfulOrderLTInst_x3f_3696_; lean_object* v_isPreorderInst_x3f_3697_; lean_object* v_orderedAddInst_x3f_3698_; lean_object* v_isLinearInst_x3f_3699_; lean_object* v_noNatDivInst_x3f_3700_; lean_object* v_ringInst_x3f_3701_; lean_object* v_commRingInst_x3f_3702_; lean_object* v_orderedRingInst_x3f_3703_; lean_object* v_fieldInst_x3f_3704_; lean_object* v_charInst_x3f_3705_; lean_object* v_zero_3706_; lean_object* v_ofNatZero_3707_; lean_object* v_one_x3f_3708_; lean_object* v_leFn_x3f_3709_; lean_object* v_ltFn_x3f_3710_; lean_object* v_addFn_3711_; lean_object* v_zsmulFn_3712_; lean_object* v_nsmulFn_3713_; lean_object* v_zsmulFn_x3f_3714_; lean_object* v_nsmulFn_x3f_3715_; lean_object* v_homomulFn_x3f_3716_; lean_object* v_subFn_3717_; lean_object* v_negFn_3718_; lean_object* v_vars_3719_; lean_object* v_varMap_3720_; lean_object* v_lowers_3721_; lean_object* v_uppers_3722_; lean_object* v_diseqs_3723_; lean_object* v_assignment_3724_; uint8_t v_caseSplits_3725_; lean_object* v_conflict_x3f_3726_; lean_object* v_diseqSplits_3727_; lean_object* v_elimEqs_3728_; lean_object* v_elimStack_3729_; lean_object* v_occurs_3730_; lean_object* v_ignored_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3745_; 
v_v_3688_ = lean_array_fget(v_structs_3675_, v_a_3671_);
v_id_3689_ = lean_ctor_get(v_v_3688_, 0);
v_ringId_x3f_3690_ = lean_ctor_get(v_v_3688_, 1);
v_type_3691_ = lean_ctor_get(v_v_3688_, 2);
v_u_3692_ = lean_ctor_get(v_v_3688_, 3);
v_intModuleInst_3693_ = lean_ctor_get(v_v_3688_, 4);
v_leInst_x3f_3694_ = lean_ctor_get(v_v_3688_, 5);
v_ltInst_x3f_3695_ = lean_ctor_get(v_v_3688_, 6);
v_lawfulOrderLTInst_x3f_3696_ = lean_ctor_get(v_v_3688_, 7);
v_isPreorderInst_x3f_3697_ = lean_ctor_get(v_v_3688_, 8);
v_orderedAddInst_x3f_3698_ = lean_ctor_get(v_v_3688_, 9);
v_isLinearInst_x3f_3699_ = lean_ctor_get(v_v_3688_, 10);
v_noNatDivInst_x3f_3700_ = lean_ctor_get(v_v_3688_, 11);
v_ringInst_x3f_3701_ = lean_ctor_get(v_v_3688_, 12);
v_commRingInst_x3f_3702_ = lean_ctor_get(v_v_3688_, 13);
v_orderedRingInst_x3f_3703_ = lean_ctor_get(v_v_3688_, 14);
v_fieldInst_x3f_3704_ = lean_ctor_get(v_v_3688_, 15);
v_charInst_x3f_3705_ = lean_ctor_get(v_v_3688_, 16);
v_zero_3706_ = lean_ctor_get(v_v_3688_, 17);
v_ofNatZero_3707_ = lean_ctor_get(v_v_3688_, 18);
v_one_x3f_3708_ = lean_ctor_get(v_v_3688_, 19);
v_leFn_x3f_3709_ = lean_ctor_get(v_v_3688_, 20);
v_ltFn_x3f_3710_ = lean_ctor_get(v_v_3688_, 21);
v_addFn_3711_ = lean_ctor_get(v_v_3688_, 22);
v_zsmulFn_3712_ = lean_ctor_get(v_v_3688_, 23);
v_nsmulFn_3713_ = lean_ctor_get(v_v_3688_, 24);
v_zsmulFn_x3f_3714_ = lean_ctor_get(v_v_3688_, 25);
v_nsmulFn_x3f_3715_ = lean_ctor_get(v_v_3688_, 26);
v_homomulFn_x3f_3716_ = lean_ctor_get(v_v_3688_, 27);
v_subFn_3717_ = lean_ctor_get(v_v_3688_, 28);
v_negFn_3718_ = lean_ctor_get(v_v_3688_, 29);
v_vars_3719_ = lean_ctor_get(v_v_3688_, 30);
v_varMap_3720_ = lean_ctor_get(v_v_3688_, 31);
v_lowers_3721_ = lean_ctor_get(v_v_3688_, 32);
v_uppers_3722_ = lean_ctor_get(v_v_3688_, 33);
v_diseqs_3723_ = lean_ctor_get(v_v_3688_, 34);
v_assignment_3724_ = lean_ctor_get(v_v_3688_, 35);
v_caseSplits_3725_ = lean_ctor_get_uint8(v_v_3688_, sizeof(void*)*42);
v_conflict_x3f_3726_ = lean_ctor_get(v_v_3688_, 36);
v_diseqSplits_3727_ = lean_ctor_get(v_v_3688_, 37);
v_elimEqs_3728_ = lean_ctor_get(v_v_3688_, 38);
v_elimStack_3729_ = lean_ctor_get(v_v_3688_, 39);
v_occurs_3730_ = lean_ctor_get(v_v_3688_, 40);
v_ignored_3731_ = lean_ctor_get(v_v_3688_, 41);
v_isSharedCheck_3745_ = !lean_is_exclusive(v_v_3688_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3733_ = v_v_3688_;
v_isShared_3734_ = v_isSharedCheck_3745_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_ignored_3731_);
lean_inc(v_occurs_3730_);
lean_inc(v_elimStack_3729_);
lean_inc(v_elimEqs_3728_);
lean_inc(v_diseqSplits_3727_);
lean_inc(v_conflict_x3f_3726_);
lean_inc(v_assignment_3724_);
lean_inc(v_diseqs_3723_);
lean_inc(v_uppers_3722_);
lean_inc(v_lowers_3721_);
lean_inc(v_varMap_3720_);
lean_inc(v_vars_3719_);
lean_inc(v_negFn_3718_);
lean_inc(v_subFn_3717_);
lean_inc(v_homomulFn_x3f_3716_);
lean_inc(v_nsmulFn_x3f_3715_);
lean_inc(v_zsmulFn_x3f_3714_);
lean_inc(v_nsmulFn_3713_);
lean_inc(v_zsmulFn_3712_);
lean_inc(v_addFn_3711_);
lean_inc(v_ltFn_x3f_3710_);
lean_inc(v_leFn_x3f_3709_);
lean_inc(v_one_x3f_3708_);
lean_inc(v_ofNatZero_3707_);
lean_inc(v_zero_3706_);
lean_inc(v_charInst_x3f_3705_);
lean_inc(v_fieldInst_x3f_3704_);
lean_inc(v_orderedRingInst_x3f_3703_);
lean_inc(v_commRingInst_x3f_3702_);
lean_inc(v_ringInst_x3f_3701_);
lean_inc(v_noNatDivInst_x3f_3700_);
lean_inc(v_isLinearInst_x3f_3699_);
lean_inc(v_orderedAddInst_x3f_3698_);
lean_inc(v_isPreorderInst_x3f_3697_);
lean_inc(v_lawfulOrderLTInst_x3f_3696_);
lean_inc(v_ltInst_x3f_3695_);
lean_inc(v_leInst_x3f_3694_);
lean_inc(v_intModuleInst_3693_);
lean_inc(v_u_3692_);
lean_inc(v_type_3691_);
lean_inc(v_ringId_x3f_3690_);
lean_inc(v_id_3689_);
lean_dec(v_v_3688_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3745_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3735_; lean_object* v_xs_x27_3736_; lean_object* v___x_3737_; lean_object* v___x_3739_; 
v___x_3735_ = lean_box(0);
v_xs_x27_3736_ = lean_array_fset(v_structs_3675_, v_a_3671_, v___x_3735_);
v___x_3737_ = l_Lean_PersistentArray_set___redArg(v_diseqs_3723_, v_y_3672_, v_fst_3673_);
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 34, v___x_3737_);
v___x_3739_ = v___x_3733_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_id_3689_);
lean_ctor_set(v_reuseFailAlloc_3744_, 1, v_ringId_x3f_3690_);
lean_ctor_set(v_reuseFailAlloc_3744_, 2, v_type_3691_);
lean_ctor_set(v_reuseFailAlloc_3744_, 3, v_u_3692_);
lean_ctor_set(v_reuseFailAlloc_3744_, 4, v_intModuleInst_3693_);
lean_ctor_set(v_reuseFailAlloc_3744_, 5, v_leInst_x3f_3694_);
lean_ctor_set(v_reuseFailAlloc_3744_, 6, v_ltInst_x3f_3695_);
lean_ctor_set(v_reuseFailAlloc_3744_, 7, v_lawfulOrderLTInst_x3f_3696_);
lean_ctor_set(v_reuseFailAlloc_3744_, 8, v_isPreorderInst_x3f_3697_);
lean_ctor_set(v_reuseFailAlloc_3744_, 9, v_orderedAddInst_x3f_3698_);
lean_ctor_set(v_reuseFailAlloc_3744_, 10, v_isLinearInst_x3f_3699_);
lean_ctor_set(v_reuseFailAlloc_3744_, 11, v_noNatDivInst_x3f_3700_);
lean_ctor_set(v_reuseFailAlloc_3744_, 12, v_ringInst_x3f_3701_);
lean_ctor_set(v_reuseFailAlloc_3744_, 13, v_commRingInst_x3f_3702_);
lean_ctor_set(v_reuseFailAlloc_3744_, 14, v_orderedRingInst_x3f_3703_);
lean_ctor_set(v_reuseFailAlloc_3744_, 15, v_fieldInst_x3f_3704_);
lean_ctor_set(v_reuseFailAlloc_3744_, 16, v_charInst_x3f_3705_);
lean_ctor_set(v_reuseFailAlloc_3744_, 17, v_zero_3706_);
lean_ctor_set(v_reuseFailAlloc_3744_, 18, v_ofNatZero_3707_);
lean_ctor_set(v_reuseFailAlloc_3744_, 19, v_one_x3f_3708_);
lean_ctor_set(v_reuseFailAlloc_3744_, 20, v_leFn_x3f_3709_);
lean_ctor_set(v_reuseFailAlloc_3744_, 21, v_ltFn_x3f_3710_);
lean_ctor_set(v_reuseFailAlloc_3744_, 22, v_addFn_3711_);
lean_ctor_set(v_reuseFailAlloc_3744_, 23, v_zsmulFn_3712_);
lean_ctor_set(v_reuseFailAlloc_3744_, 24, v_nsmulFn_3713_);
lean_ctor_set(v_reuseFailAlloc_3744_, 25, v_zsmulFn_x3f_3714_);
lean_ctor_set(v_reuseFailAlloc_3744_, 26, v_nsmulFn_x3f_3715_);
lean_ctor_set(v_reuseFailAlloc_3744_, 27, v_homomulFn_x3f_3716_);
lean_ctor_set(v_reuseFailAlloc_3744_, 28, v_subFn_3717_);
lean_ctor_set(v_reuseFailAlloc_3744_, 29, v_negFn_3718_);
lean_ctor_set(v_reuseFailAlloc_3744_, 30, v_vars_3719_);
lean_ctor_set(v_reuseFailAlloc_3744_, 31, v_varMap_3720_);
lean_ctor_set(v_reuseFailAlloc_3744_, 32, v_lowers_3721_);
lean_ctor_set(v_reuseFailAlloc_3744_, 33, v_uppers_3722_);
lean_ctor_set(v_reuseFailAlloc_3744_, 34, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3744_, 35, v_assignment_3724_);
lean_ctor_set(v_reuseFailAlloc_3744_, 36, v_conflict_x3f_3726_);
lean_ctor_set(v_reuseFailAlloc_3744_, 37, v_diseqSplits_3727_);
lean_ctor_set(v_reuseFailAlloc_3744_, 38, v_elimEqs_3728_);
lean_ctor_set(v_reuseFailAlloc_3744_, 39, v_elimStack_3729_);
lean_ctor_set(v_reuseFailAlloc_3744_, 40, v_occurs_3730_);
lean_ctor_set(v_reuseFailAlloc_3744_, 41, v_ignored_3731_);
lean_ctor_set_uint8(v_reuseFailAlloc_3744_, sizeof(void*)*42, v_caseSplits_3725_);
v___x_3739_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
lean_object* v___x_3740_; lean_object* v___x_3742_; 
v___x_3740_ = lean_array_fset(v_xs_x27_3736_, v_a_3671_, v___x_3739_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 0, v___x_3740_);
v___x_3742_ = v___x_3686_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3740_);
lean_ctor_set(v_reuseFailAlloc_3743_, 1, v_typeIdOf_3676_);
lean_ctor_set(v_reuseFailAlloc_3743_, 2, v_exprToStructId_3677_);
lean_ctor_set(v_reuseFailAlloc_3743_, 3, v_exprToStructIdEntries_3678_);
lean_ctor_set(v_reuseFailAlloc_3743_, 4, v_forbiddenNatModules_3679_);
lean_ctor_set(v_reuseFailAlloc_3743_, 5, v_natStructs_3680_);
lean_ctor_set(v_reuseFailAlloc_3743_, 6, v_natTypeIdOf_3681_);
lean_ctor_set(v_reuseFailAlloc_3743_, 7, v_exprToNatStructId_3682_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed(lean_object* v_a_3755_, lean_object* v_y_3756_, lean_object* v_fst_3757_, lean_object* v_s_3758_){
_start:
{
lean_object* v_res_3759_; 
v_res_3759_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0(v_a_3755_, v_y_3756_, v_fst_3757_, v_s_3758_);
lean_dec(v_y_3756_);
lean_dec(v_a_3755_);
return v_res_3759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(lean_object* v_a_3760_, lean_object* v_x_3761_, lean_object* v_c_3762_, lean_object* v_as_3763_, size_t v_sz_3764_, size_t v_i_3765_, lean_object* v_b_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v_a_3780_; uint8_t v___x_3784_; 
v___x_3784_ = lean_usize_dec_lt(v_i_3765_, v_sz_3764_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; 
lean_dec_ref(v_c_3762_);
v___x_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3785_, 0, v_b_3766_);
return v___x_3785_;
}
else
{
lean_object* v_a_3786_; lean_object* v_fst_3787_; lean_object* v_snd_3788_; lean_object* v___x_3789_; 
lean_dec_ref(v_b_3766_);
v_a_3786_ = lean_array_uget_borrowed(v_as_3763_, v_i_3765_);
v_fst_3787_ = lean_ctor_get(v_a_3786_, 0);
v_snd_3788_ = lean_ctor_get(v_a_3786_, 1);
lean_inc(v_snd_3788_);
lean_inc(v_fst_3787_);
lean_inc_ref(v_c_3762_);
v___x_3789_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f(v_a_3760_, v_x_3761_, v_c_3762_, v_fst_3787_, v_snd_3788_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; lean_object* v___x_3791_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3790_);
lean_dec_ref(v___x_3789_);
v___x_3791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
if (lean_obj_tag(v_a_3790_) == 1)
{
lean_object* v_val_3792_; lean_object* v___x_3793_; 
v_val_3792_ = lean_ctor_get(v_a_3790_, 0);
lean_inc(v_val_3792_);
lean_dec_ref(v_a_3790_);
v___x_3793_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v_val_3792_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v___x_3794_; 
lean_dec_ref(v___x_3793_);
v___x_3794_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3804_; 
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3797_ = v___x_3794_;
v_isShared_3798_ = v_isSharedCheck_3804_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_a_3795_);
lean_dec(v___x_3794_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3804_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
uint8_t v___x_3799_; 
v___x_3799_ = lean_unbox(v_a_3795_);
lean_dec(v_a_3795_);
if (v___x_3799_ == 0)
{
lean_del_object(v___x_3797_);
v_a_3780_ = v___x_3791_;
goto v___jp_3779_;
}
else
{
lean_object* v___x_3800_; lean_object* v___x_3802_; 
lean_dec_ref(v_c_3762_);
v___x_3800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__2));
if (v_isShared_3798_ == 0)
{
lean_ctor_set(v___x_3797_, 0, v___x_3800_);
v___x_3802_ = v___x_3797_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v___x_3800_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3812_; 
lean_dec_ref(v_c_3762_);
v_a_3805_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3807_ = v___x_3794_;
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3794_);
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
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_dec_ref(v_c_3762_);
v_a_3813_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3793_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3793_);
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
else
{
lean_object* v___x_3821_; 
lean_dec(v_a_3790_);
v___x_3821_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_ignore(v_snd_3788_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_dec_ref(v___x_3821_);
v_a_3780_ = v___x_3791_;
goto v___jp_3779_;
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
lean_dec_ref(v_c_3762_);
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3821_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3821_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
}
else
{
lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3837_; 
lean_dec_ref(v_c_3762_);
v_a_3830_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3832_ = v___x_3789_;
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v___x_3789_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3835_; 
if (v_isShared_3833_ == 0)
{
v___x_3835_ = v___x_3832_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3830_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
}
v___jp_3779_:
{
size_t v___x_3781_; size_t v___x_3782_; 
v___x_3781_ = ((size_t)1ULL);
v___x_3782_ = lean_usize_add(v_i_3765_, v___x_3781_);
lean_inc_ref(v_a_3780_);
v_i_3765_ = v___x_3782_;
v_b_3766_ = v_a_3780_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0___boxed(lean_object** _args){
lean_object* v_a_3838_ = _args[0];
lean_object* v_x_3839_ = _args[1];
lean_object* v_c_3840_ = _args[2];
lean_object* v_as_3841_ = _args[3];
lean_object* v_sz_3842_ = _args[4];
lean_object* v_i_3843_ = _args[5];
lean_object* v_b_3844_ = _args[6];
lean_object* v___y_3845_ = _args[7];
lean_object* v___y_3846_ = _args[8];
lean_object* v___y_3847_ = _args[9];
lean_object* v___y_3848_ = _args[10];
lean_object* v___y_3849_ = _args[11];
lean_object* v___y_3850_ = _args[12];
lean_object* v___y_3851_ = _args[13];
lean_object* v___y_3852_ = _args[14];
lean_object* v___y_3853_ = _args[15];
lean_object* v___y_3854_ = _args[16];
lean_object* v___y_3855_ = _args[17];
lean_object* v___y_3856_ = _args[18];
_start:
{
size_t v_sz_boxed_3857_; size_t v_i_boxed_3858_; lean_object* v_res_3859_; 
v_sz_boxed_3857_ = lean_unbox_usize(v_sz_3842_);
lean_dec(v_sz_3842_);
v_i_boxed_3858_ = lean_unbox_usize(v_i_3843_);
lean_dec(v_i_3843_);
v_res_3859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3838_, v_x_3839_, v_c_3840_, v_as_3841_, v_sz_boxed_3857_, v_i_boxed_3858_, v_b_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
lean_dec(v___y_3851_);
lean_dec_ref(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
lean_dec(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v_as_3841_);
lean_dec(v_x_3839_);
lean_dec(v_a_3838_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(lean_object* v_a_3860_, lean_object* v_x_3861_, lean_object* v_c_3862_, lean_object* v_y_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_){
_start:
{
lean_object* v___x_3876_; 
v___x_3876_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3936_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3879_ = v___x_3876_;
v_isShared_3880_ = v_isSharedCheck_3936_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3876_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3936_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
uint8_t v___x_3881_; 
v___x_3881_ = lean_unbox(v_a_3877_);
lean_dec(v_a_3877_);
if (v___x_3881_ == 0)
{
lean_object* v___x_3882_; 
lean_del_object(v___x_3879_);
v___x_3882_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; lean_object* v___y_3885_; lean_object* v_diseqs_3918_; lean_object* v_size_3919_; lean_object* v___x_3920_; uint8_t v___x_3921_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3883_);
lean_dec_ref(v___x_3882_);
v_diseqs_3918_ = lean_ctor_get(v_a_3883_, 34);
lean_inc_ref(v_diseqs_3918_);
lean_dec(v_a_3883_);
v_size_3919_ = lean_ctor_get(v_diseqs_3918_, 2);
v___x_3920_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers___closed__0);
v___x_3921_ = lean_nat_dec_lt(v_y_3863_, v_size_3919_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; 
lean_dec_ref(v_diseqs_3918_);
v___x_3922_ = l_outOfBounds___redArg(v___x_3920_);
v___y_3885_ = v___x_3922_;
goto v___jp_3884_;
}
else
{
lean_object* v___x_3923_; 
v___x_3923_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3920_, v_diseqs_3918_, v_y_3863_);
lean_dec_ref(v_diseqs_3918_);
v___y_3885_ = v___x_3923_;
goto v___jp_3884_;
}
v___jp_3884_:
{
lean_object* v___x_3886_; lean_object* v_fst_3887_; lean_object* v_snd_3888_; lean_object* v___f_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3886_ = l_Lean_Meta_Grind_Arith_split___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_splitDiseqs_spec__0(v_x_3861_, v___y_3885_);
v_fst_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_fst_3887_);
v_snd_3888_ = lean_ctor_get(v___x_3886_, 1);
lean_inc(v_snd_3888_);
lean_dec_ref(v___x_3886_);
lean_inc(v_a_3864_);
v___f_3889_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3889_, 0, v_a_3864_);
lean_closure_set(v___f_3889_, 1, v_y_3863_);
lean_closure_set(v___f_3889_, 2, v_fst_3887_);
v___x_3890_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3891_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3890_, v___f_3889_, v_a_3865_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v___x_3892_; lean_object* v___x_3893_; size_t v_sz_3894_; size_t v___x_3895_; lean_object* v___x_3896_; 
lean_dec_ref(v___x_3891_);
v___x_3892_ = lean_box(0);
v___x_3893_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLeCnstrs_spec__0___closed__0));
v_sz_3894_ = lean_array_size(v_snd_3888_);
v___x_3895_ = ((size_t)0ULL);
v___x_3896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs_spec__0(v_a_3860_, v_x_3861_, v_c_3862_, v_snd_3888_, v_sz_3894_, v___x_3895_, v___x_3893_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_);
lean_dec(v_snd_3888_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3909_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3899_ = v___x_3896_;
v_isShared_3900_ = v_isSharedCheck_3909_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3896_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3909_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v_fst_3901_; 
v_fst_3901_ = lean_ctor_get(v_a_3897_, 0);
lean_inc(v_fst_3901_);
lean_dec(v_a_3897_);
if (lean_obj_tag(v_fst_3901_) == 0)
{
lean_object* v___x_3903_; 
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 0, v___x_3892_);
v___x_3903_ = v___x_3899_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3892_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
else
{
lean_object* v_val_3905_; lean_object* v___x_3907_; 
v_val_3905_ = lean_ctor_get(v_fst_3901_, 0);
lean_inc(v_val_3905_);
lean_dec_ref(v_fst_3901_);
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 0, v_val_3905_);
v___x_3907_ = v___x_3899_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_val_3905_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
else
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3917_; 
v_a_3910_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3912_ = v___x_3896_;
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3896_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3915_; 
if (v_isShared_3913_ == 0)
{
v___x_3915_ = v___x_3912_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_a_3910_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
else
{
lean_dec(v_snd_3888_);
lean_dec_ref(v_c_3862_);
return v___x_3891_;
}
}
}
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_dec(v_y_3863_);
lean_dec_ref(v_c_3862_);
v_a_3924_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3882_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3882_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
else
{
lean_object* v___x_3932_; lean_object* v___x_3934_; 
lean_dec(v_y_3863_);
lean_dec_ref(v_c_3862_);
v___x_3932_ = lean_box(0);
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 0, v___x_3932_);
v___x_3934_ = v___x_3879_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_dec(v_y_3863_);
lean_dec_ref(v_c_3862_);
v_a_3937_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3876_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3876_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs___boxed(lean_object* v_a_3945_, lean_object* v_x_3946_, lean_object* v_c_3947_, lean_object* v_y_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v_a_3945_, v_x_3946_, v_c_3947_, v_y_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
lean_dec(v_a_3955_);
lean_dec_ref(v_a_3954_);
lean_dec(v_a_3953_);
lean_dec_ref(v_a_3952_);
lean_dec(v_a_3951_);
lean_dec(v_a_3950_);
lean_dec(v_a_3949_);
lean_dec(v_x_3946_);
lean_dec(v_a_3945_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(lean_object* v_a_3962_, lean_object* v_x_3963_, lean_object* v_c_3964_, lean_object* v_y_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_){
_start:
{
lean_object* v___x_3978_; 
lean_inc(v_y_3965_);
lean_inc_ref(v_c_3964_);
lean_inc(v_x_3963_);
lean_inc(v_a_3962_);
v___x_3978_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateLowers(v_a_3962_, v_x_3963_, v_c_3964_, v_y_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v___x_3979_; 
lean_dec_ref(v___x_3978_);
lean_inc(v_y_3965_);
lean_inc_ref(v_c_3964_);
lean_inc(v_x_3963_);
lean_inc(v_a_3962_);
v___x_3979_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateUppers(v_a_3962_, v_x_3963_, v_c_3964_, v_y_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v___x_3980_; lean_object* v___x_3981_; 
lean_dec_ref(v___x_3979_);
v___x_3980_ = lean_nat_to_int(v_a_3962_);
v___x_3981_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateDiseqs(v___x_3980_, v_x_3963_, v_c_3964_, v_y_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_);
lean_dec(v_x_3963_);
lean_dec(v___x_3980_);
return v___x_3981_;
}
else
{
lean_dec(v_y_3965_);
lean_dec_ref(v_c_3964_);
lean_dec(v_x_3963_);
lean_dec(v_a_3962_);
return v___x_3979_;
}
}
else
{
lean_dec(v_y_3965_);
lean_dec_ref(v_c_3964_);
lean_dec(v_x_3963_);
lean_dec(v_a_3962_);
return v___x_3978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt___boxed(lean_object* v_a_3982_, lean_object* v_x_3983_, lean_object* v_c_3984_, lean_object* v_y_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_3982_, v_x_3983_, v_c_3984_, v_y_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_);
lean_dec(v_a_3996_);
lean_dec_ref(v_a_3995_);
lean_dec(v_a_3994_);
lean_dec_ref(v_a_3993_);
lean_dec(v_a_3992_);
lean_dec_ref(v_a_3991_);
lean_dec(v_a_3990_);
lean_dec_ref(v_a_3989_);
lean_dec(v_a_3988_);
lean_dec(v_a_3987_);
lean_dec(v_a_3986_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(lean_object* v_a_3999_, lean_object* v_x_4000_, lean_object* v_s_4001_){
_start:
{
lean_object* v_structs_4002_; lean_object* v_typeIdOf_4003_; lean_object* v_exprToStructId_4004_; lean_object* v_exprToStructIdEntries_4005_; lean_object* v_forbiddenNatModules_4006_; lean_object* v_natStructs_4007_; lean_object* v_natTypeIdOf_4008_; lean_object* v_exprToNatStructId_4009_; lean_object* v___x_4010_; uint8_t v___x_4011_; 
v_structs_4002_ = lean_ctor_get(v_s_4001_, 0);
v_typeIdOf_4003_ = lean_ctor_get(v_s_4001_, 1);
v_exprToStructId_4004_ = lean_ctor_get(v_s_4001_, 2);
v_exprToStructIdEntries_4005_ = lean_ctor_get(v_s_4001_, 3);
v_forbiddenNatModules_4006_ = lean_ctor_get(v_s_4001_, 4);
v_natStructs_4007_ = lean_ctor_get(v_s_4001_, 5);
v_natTypeIdOf_4008_ = lean_ctor_get(v_s_4001_, 6);
v_exprToNatStructId_4009_ = lean_ctor_get(v_s_4001_, 7);
v___x_4010_ = lean_array_get_size(v_structs_4002_);
v___x_4011_ = lean_nat_dec_lt(v_a_3999_, v___x_4010_);
if (v___x_4011_ == 0)
{
return v_s_4001_;
}
else
{
lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4074_; 
lean_inc_ref(v_exprToNatStructId_4009_);
lean_inc_ref(v_natTypeIdOf_4008_);
lean_inc_ref(v_natStructs_4007_);
lean_inc_ref(v_forbiddenNatModules_4006_);
lean_inc_ref(v_exprToStructIdEntries_4005_);
lean_inc_ref(v_exprToStructId_4004_);
lean_inc_ref(v_typeIdOf_4003_);
lean_inc_ref(v_structs_4002_);
v_isSharedCheck_4074_ = !lean_is_exclusive(v_s_4001_);
if (v_isSharedCheck_4074_ == 0)
{
lean_object* v_unused_4075_; lean_object* v_unused_4076_; lean_object* v_unused_4077_; lean_object* v_unused_4078_; lean_object* v_unused_4079_; lean_object* v_unused_4080_; lean_object* v_unused_4081_; lean_object* v_unused_4082_; 
v_unused_4075_ = lean_ctor_get(v_s_4001_, 7);
lean_dec(v_unused_4075_);
v_unused_4076_ = lean_ctor_get(v_s_4001_, 6);
lean_dec(v_unused_4076_);
v_unused_4077_ = lean_ctor_get(v_s_4001_, 5);
lean_dec(v_unused_4077_);
v_unused_4078_ = lean_ctor_get(v_s_4001_, 4);
lean_dec(v_unused_4078_);
v_unused_4079_ = lean_ctor_get(v_s_4001_, 3);
lean_dec(v_unused_4079_);
v_unused_4080_ = lean_ctor_get(v_s_4001_, 2);
lean_dec(v_unused_4080_);
v_unused_4081_ = lean_ctor_get(v_s_4001_, 1);
lean_dec(v_unused_4081_);
v_unused_4082_ = lean_ctor_get(v_s_4001_, 0);
lean_dec(v_unused_4082_);
v___x_4013_ = v_s_4001_;
v_isShared_4014_ = v_isSharedCheck_4074_;
goto v_resetjp_4012_;
}
else
{
lean_dec(v_s_4001_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4074_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v_v_4015_; lean_object* v_id_4016_; lean_object* v_ringId_x3f_4017_; lean_object* v_type_4018_; lean_object* v_u_4019_; lean_object* v_intModuleInst_4020_; lean_object* v_leInst_x3f_4021_; lean_object* v_ltInst_x3f_4022_; lean_object* v_lawfulOrderLTInst_x3f_4023_; lean_object* v_isPreorderInst_x3f_4024_; lean_object* v_orderedAddInst_x3f_4025_; lean_object* v_isLinearInst_x3f_4026_; lean_object* v_noNatDivInst_x3f_4027_; lean_object* v_ringInst_x3f_4028_; lean_object* v_commRingInst_x3f_4029_; lean_object* v_orderedRingInst_x3f_4030_; lean_object* v_fieldInst_x3f_4031_; lean_object* v_charInst_x3f_4032_; lean_object* v_zero_4033_; lean_object* v_ofNatZero_4034_; lean_object* v_one_x3f_4035_; lean_object* v_leFn_x3f_4036_; lean_object* v_ltFn_x3f_4037_; lean_object* v_addFn_4038_; lean_object* v_zsmulFn_4039_; lean_object* v_nsmulFn_4040_; lean_object* v_zsmulFn_x3f_4041_; lean_object* v_nsmulFn_x3f_4042_; lean_object* v_homomulFn_x3f_4043_; lean_object* v_subFn_4044_; lean_object* v_negFn_4045_; lean_object* v_vars_4046_; lean_object* v_varMap_4047_; lean_object* v_lowers_4048_; lean_object* v_uppers_4049_; lean_object* v_diseqs_4050_; lean_object* v_assignment_4051_; uint8_t v_caseSplits_4052_; lean_object* v_conflict_x3f_4053_; lean_object* v_diseqSplits_4054_; lean_object* v_elimEqs_4055_; lean_object* v_elimStack_4056_; lean_object* v_occurs_4057_; lean_object* v_ignored_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4073_; 
v_v_4015_ = lean_array_fget(v_structs_4002_, v_a_3999_);
v_id_4016_ = lean_ctor_get(v_v_4015_, 0);
v_ringId_x3f_4017_ = lean_ctor_get(v_v_4015_, 1);
v_type_4018_ = lean_ctor_get(v_v_4015_, 2);
v_u_4019_ = lean_ctor_get(v_v_4015_, 3);
v_intModuleInst_4020_ = lean_ctor_get(v_v_4015_, 4);
v_leInst_x3f_4021_ = lean_ctor_get(v_v_4015_, 5);
v_ltInst_x3f_4022_ = lean_ctor_get(v_v_4015_, 6);
v_lawfulOrderLTInst_x3f_4023_ = lean_ctor_get(v_v_4015_, 7);
v_isPreorderInst_x3f_4024_ = lean_ctor_get(v_v_4015_, 8);
v_orderedAddInst_x3f_4025_ = lean_ctor_get(v_v_4015_, 9);
v_isLinearInst_x3f_4026_ = lean_ctor_get(v_v_4015_, 10);
v_noNatDivInst_x3f_4027_ = lean_ctor_get(v_v_4015_, 11);
v_ringInst_x3f_4028_ = lean_ctor_get(v_v_4015_, 12);
v_commRingInst_x3f_4029_ = lean_ctor_get(v_v_4015_, 13);
v_orderedRingInst_x3f_4030_ = lean_ctor_get(v_v_4015_, 14);
v_fieldInst_x3f_4031_ = lean_ctor_get(v_v_4015_, 15);
v_charInst_x3f_4032_ = lean_ctor_get(v_v_4015_, 16);
v_zero_4033_ = lean_ctor_get(v_v_4015_, 17);
v_ofNatZero_4034_ = lean_ctor_get(v_v_4015_, 18);
v_one_x3f_4035_ = lean_ctor_get(v_v_4015_, 19);
v_leFn_x3f_4036_ = lean_ctor_get(v_v_4015_, 20);
v_ltFn_x3f_4037_ = lean_ctor_get(v_v_4015_, 21);
v_addFn_4038_ = lean_ctor_get(v_v_4015_, 22);
v_zsmulFn_4039_ = lean_ctor_get(v_v_4015_, 23);
v_nsmulFn_4040_ = lean_ctor_get(v_v_4015_, 24);
v_zsmulFn_x3f_4041_ = lean_ctor_get(v_v_4015_, 25);
v_nsmulFn_x3f_4042_ = lean_ctor_get(v_v_4015_, 26);
v_homomulFn_x3f_4043_ = lean_ctor_get(v_v_4015_, 27);
v_subFn_4044_ = lean_ctor_get(v_v_4015_, 28);
v_negFn_4045_ = lean_ctor_get(v_v_4015_, 29);
v_vars_4046_ = lean_ctor_get(v_v_4015_, 30);
v_varMap_4047_ = lean_ctor_get(v_v_4015_, 31);
v_lowers_4048_ = lean_ctor_get(v_v_4015_, 32);
v_uppers_4049_ = lean_ctor_get(v_v_4015_, 33);
v_diseqs_4050_ = lean_ctor_get(v_v_4015_, 34);
v_assignment_4051_ = lean_ctor_get(v_v_4015_, 35);
v_caseSplits_4052_ = lean_ctor_get_uint8(v_v_4015_, sizeof(void*)*42);
v_conflict_x3f_4053_ = lean_ctor_get(v_v_4015_, 36);
v_diseqSplits_4054_ = lean_ctor_get(v_v_4015_, 37);
v_elimEqs_4055_ = lean_ctor_get(v_v_4015_, 38);
v_elimStack_4056_ = lean_ctor_get(v_v_4015_, 39);
v_occurs_4057_ = lean_ctor_get(v_v_4015_, 40);
v_ignored_4058_ = lean_ctor_get(v_v_4015_, 41);
v_isSharedCheck_4073_ = !lean_is_exclusive(v_v_4015_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4060_ = v_v_4015_;
v_isShared_4061_ = v_isSharedCheck_4073_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_ignored_4058_);
lean_inc(v_occurs_4057_);
lean_inc(v_elimStack_4056_);
lean_inc(v_elimEqs_4055_);
lean_inc(v_diseqSplits_4054_);
lean_inc(v_conflict_x3f_4053_);
lean_inc(v_assignment_4051_);
lean_inc(v_diseqs_4050_);
lean_inc(v_uppers_4049_);
lean_inc(v_lowers_4048_);
lean_inc(v_varMap_4047_);
lean_inc(v_vars_4046_);
lean_inc(v_negFn_4045_);
lean_inc(v_subFn_4044_);
lean_inc(v_homomulFn_x3f_4043_);
lean_inc(v_nsmulFn_x3f_4042_);
lean_inc(v_zsmulFn_x3f_4041_);
lean_inc(v_nsmulFn_4040_);
lean_inc(v_zsmulFn_4039_);
lean_inc(v_addFn_4038_);
lean_inc(v_ltFn_x3f_4037_);
lean_inc(v_leFn_x3f_4036_);
lean_inc(v_one_x3f_4035_);
lean_inc(v_ofNatZero_4034_);
lean_inc(v_zero_4033_);
lean_inc(v_charInst_x3f_4032_);
lean_inc(v_fieldInst_x3f_4031_);
lean_inc(v_orderedRingInst_x3f_4030_);
lean_inc(v_commRingInst_x3f_4029_);
lean_inc(v_ringInst_x3f_4028_);
lean_inc(v_noNatDivInst_x3f_4027_);
lean_inc(v_isLinearInst_x3f_4026_);
lean_inc(v_orderedAddInst_x3f_4025_);
lean_inc(v_isPreorderInst_x3f_4024_);
lean_inc(v_lawfulOrderLTInst_x3f_4023_);
lean_inc(v_ltInst_x3f_4022_);
lean_inc(v_leInst_x3f_4021_);
lean_inc(v_intModuleInst_4020_);
lean_inc(v_u_4019_);
lean_inc(v_type_4018_);
lean_inc(v_ringId_x3f_4017_);
lean_inc(v_id_4016_);
lean_dec(v_v_4015_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4073_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4062_; lean_object* v_xs_x27_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4067_; 
v___x_4062_ = lean_box(0);
v_xs_x27_4063_ = lean_array_fset(v_structs_4002_, v_a_3999_, v___x_4062_);
v___x_4064_ = lean_box(1);
v___x_4065_ = l_Lean_PersistentArray_set___redArg(v_occurs_4057_, v_x_4000_, v___x_4064_);
if (v_isShared_4061_ == 0)
{
lean_ctor_set(v___x_4060_, 40, v___x_4065_);
v___x_4067_ = v___x_4060_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_id_4016_);
lean_ctor_set(v_reuseFailAlloc_4072_, 1, v_ringId_x3f_4017_);
lean_ctor_set(v_reuseFailAlloc_4072_, 2, v_type_4018_);
lean_ctor_set(v_reuseFailAlloc_4072_, 3, v_u_4019_);
lean_ctor_set(v_reuseFailAlloc_4072_, 4, v_intModuleInst_4020_);
lean_ctor_set(v_reuseFailAlloc_4072_, 5, v_leInst_x3f_4021_);
lean_ctor_set(v_reuseFailAlloc_4072_, 6, v_ltInst_x3f_4022_);
lean_ctor_set(v_reuseFailAlloc_4072_, 7, v_lawfulOrderLTInst_x3f_4023_);
lean_ctor_set(v_reuseFailAlloc_4072_, 8, v_isPreorderInst_x3f_4024_);
lean_ctor_set(v_reuseFailAlloc_4072_, 9, v_orderedAddInst_x3f_4025_);
lean_ctor_set(v_reuseFailAlloc_4072_, 10, v_isLinearInst_x3f_4026_);
lean_ctor_set(v_reuseFailAlloc_4072_, 11, v_noNatDivInst_x3f_4027_);
lean_ctor_set(v_reuseFailAlloc_4072_, 12, v_ringInst_x3f_4028_);
lean_ctor_set(v_reuseFailAlloc_4072_, 13, v_commRingInst_x3f_4029_);
lean_ctor_set(v_reuseFailAlloc_4072_, 14, v_orderedRingInst_x3f_4030_);
lean_ctor_set(v_reuseFailAlloc_4072_, 15, v_fieldInst_x3f_4031_);
lean_ctor_set(v_reuseFailAlloc_4072_, 16, v_charInst_x3f_4032_);
lean_ctor_set(v_reuseFailAlloc_4072_, 17, v_zero_4033_);
lean_ctor_set(v_reuseFailAlloc_4072_, 18, v_ofNatZero_4034_);
lean_ctor_set(v_reuseFailAlloc_4072_, 19, v_one_x3f_4035_);
lean_ctor_set(v_reuseFailAlloc_4072_, 20, v_leFn_x3f_4036_);
lean_ctor_set(v_reuseFailAlloc_4072_, 21, v_ltFn_x3f_4037_);
lean_ctor_set(v_reuseFailAlloc_4072_, 22, v_addFn_4038_);
lean_ctor_set(v_reuseFailAlloc_4072_, 23, v_zsmulFn_4039_);
lean_ctor_set(v_reuseFailAlloc_4072_, 24, v_nsmulFn_4040_);
lean_ctor_set(v_reuseFailAlloc_4072_, 25, v_zsmulFn_x3f_4041_);
lean_ctor_set(v_reuseFailAlloc_4072_, 26, v_nsmulFn_x3f_4042_);
lean_ctor_set(v_reuseFailAlloc_4072_, 27, v_homomulFn_x3f_4043_);
lean_ctor_set(v_reuseFailAlloc_4072_, 28, v_subFn_4044_);
lean_ctor_set(v_reuseFailAlloc_4072_, 29, v_negFn_4045_);
lean_ctor_set(v_reuseFailAlloc_4072_, 30, v_vars_4046_);
lean_ctor_set(v_reuseFailAlloc_4072_, 31, v_varMap_4047_);
lean_ctor_set(v_reuseFailAlloc_4072_, 32, v_lowers_4048_);
lean_ctor_set(v_reuseFailAlloc_4072_, 33, v_uppers_4049_);
lean_ctor_set(v_reuseFailAlloc_4072_, 34, v_diseqs_4050_);
lean_ctor_set(v_reuseFailAlloc_4072_, 35, v_assignment_4051_);
lean_ctor_set(v_reuseFailAlloc_4072_, 36, v_conflict_x3f_4053_);
lean_ctor_set(v_reuseFailAlloc_4072_, 37, v_diseqSplits_4054_);
lean_ctor_set(v_reuseFailAlloc_4072_, 38, v_elimEqs_4055_);
lean_ctor_set(v_reuseFailAlloc_4072_, 39, v_elimStack_4056_);
lean_ctor_set(v_reuseFailAlloc_4072_, 40, v___x_4065_);
lean_ctor_set(v_reuseFailAlloc_4072_, 41, v_ignored_4058_);
lean_ctor_set_uint8(v_reuseFailAlloc_4072_, sizeof(void*)*42, v_caseSplits_4052_);
v___x_4067_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
lean_object* v___x_4068_; lean_object* v___x_4070_; 
v___x_4068_ = lean_array_fset(v_xs_x27_4063_, v_a_3999_, v___x_4067_);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 0, v___x_4068_);
v___x_4070_ = v___x_4013_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4068_);
lean_ctor_set(v_reuseFailAlloc_4071_, 1, v_typeIdOf_4003_);
lean_ctor_set(v_reuseFailAlloc_4071_, 2, v_exprToStructId_4004_);
lean_ctor_set(v_reuseFailAlloc_4071_, 3, v_exprToStructIdEntries_4005_);
lean_ctor_set(v_reuseFailAlloc_4071_, 4, v_forbiddenNatModules_4006_);
lean_ctor_set(v_reuseFailAlloc_4071_, 5, v_natStructs_4007_);
lean_ctor_set(v_reuseFailAlloc_4071_, 6, v_natTypeIdOf_4008_);
lean_ctor_set(v_reuseFailAlloc_4071_, 7, v_exprToNatStructId_4009_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed(lean_object* v_a_4083_, lean_object* v_x_4084_, lean_object* v_s_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0(v_a_4083_, v_x_4084_, v_s_4085_);
lean_dec(v_x_4084_);
lean_dec(v_a_4083_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(lean_object* v_a_4087_, lean_object* v_x_4088_, lean_object* v_c_4089_, lean_object* v_init_4090_, lean_object* v_x_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
if (lean_obj_tag(v_x_4091_) == 0)
{
lean_object* v_k_4104_; lean_object* v_l_4105_; lean_object* v_r_4106_; lean_object* v___x_4107_; 
v_k_4104_ = lean_ctor_get(v_x_4091_, 1);
lean_inc(v_k_4104_);
v_l_4105_ = lean_ctor_get(v_x_4091_, 3);
lean_inc(v_l_4105_);
v_r_4106_ = lean_ctor_get(v_x_4091_, 4);
lean_inc(v_r_4106_);
lean_dec_ref(v_x_4091_);
lean_inc_ref(v_c_4089_);
lean_inc(v_x_4088_);
lean_inc(v_a_4087_);
v___x_4107_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4087_, v_x_4088_, v_c_4089_, v_init_4090_, v_l_4105_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_object* v___x_4108_; 
lean_dec_ref(v___x_4107_);
lean_inc_ref(v_c_4089_);
lean_inc(v_x_4088_);
lean_inc(v_a_4087_);
v___x_4108_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4087_, v_x_4088_, v_c_4089_, v_k_4104_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v___x_4109_; 
lean_dec_ref(v___x_4108_);
v___x_4109_ = lean_box(0);
v_init_4090_ = v___x_4109_;
v_x_4091_ = v_r_4106_;
goto _start;
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
lean_dec(v_r_4106_);
lean_dec_ref(v_c_4089_);
lean_dec(v_x_4088_);
lean_dec(v_a_4087_);
v_a_4111_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4108_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4108_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
else
{
lean_dec(v_r_4106_);
lean_dec(v_k_4104_);
lean_dec_ref(v_c_4089_);
lean_dec(v_x_4088_);
lean_dec(v_a_4087_);
return v___x_4107_;
}
}
else
{
lean_object* v___x_4119_; lean_object* v___x_4120_; 
lean_dec_ref(v_c_4089_);
lean_dec(v_x_4088_);
lean_dec(v_a_4087_);
v___x_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4119_, 0, v_init_4090_);
v___x_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4119_);
return v___x_4120_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0___boxed(lean_object** _args){
lean_object* v_a_4121_ = _args[0];
lean_object* v_x_4122_ = _args[1];
lean_object* v_c_4123_ = _args[2];
lean_object* v_init_4124_ = _args[3];
lean_object* v_x_4125_ = _args[4];
lean_object* v___y_4126_ = _args[5];
lean_object* v___y_4127_ = _args[6];
lean_object* v___y_4128_ = _args[7];
lean_object* v___y_4129_ = _args[8];
lean_object* v___y_4130_ = _args[9];
lean_object* v___y_4131_ = _args[10];
lean_object* v___y_4132_ = _args[11];
lean_object* v___y_4133_ = _args[12];
lean_object* v___y_4134_ = _args[13];
lean_object* v___y_4135_ = _args[14];
lean_object* v___y_4136_ = _args[15];
lean_object* v___y_4137_ = _args[16];
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4121_, v_x_4122_, v_c_4123_, v_init_4124_, v_x_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec(v___y_4127_);
lean_dec(v___y_4126_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(lean_object* v_a_4139_, lean_object* v_x_4140_, lean_object* v_c_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_){
_start:
{
lean_object* v___x_4154_; 
v___x_4154_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_a_4155_; lean_object* v_occurs_4156_; lean_object* v_size_4157_; lean_object* v___f_4158_; lean_object* v___y_4160_; lean_object* v___x_4182_; uint8_t v___x_4183_; 
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4155_);
lean_dec_ref(v___x_4154_);
v_occurs_4156_ = lean_ctor_get(v_a_4155_, 40);
lean_inc_ref(v_occurs_4156_);
lean_dec(v_a_4155_);
v_size_4157_ = lean_ctor_get(v_occurs_4156_, 2);
lean_inc(v_x_4140_);
lean_inc(v_a_4142_);
v___f_4158_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4158_, 0, v_a_4142_);
lean_closure_set(v___f_4158_, 1, v_x_4140_);
v___x_4182_ = lean_box(1);
v___x_4183_ = lean_nat_dec_lt(v_x_4140_, v_size_4157_);
if (v___x_4183_ == 0)
{
lean_object* v___x_4184_; 
lean_dec_ref(v_occurs_4156_);
v___x_4184_ = l_outOfBounds___redArg(v___x_4182_);
v___y_4160_ = v___x_4184_;
goto v___jp_4159_;
}
else
{
lean_object* v___x_4185_; 
v___x_4185_ = l_Lean_PersistentArray_get_x21___redArg(v___x_4182_, v_occurs_4156_, v_x_4140_);
lean_dec_ref(v_occurs_4156_);
v___y_4160_ = v___x_4185_;
goto v___jp_4159_;
}
v___jp_4159_:
{
lean_object* v___x_4161_; lean_object* v___x_4162_; 
v___x_4161_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4162_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4161_, v___f_4158_, v_a_4143_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v___x_4163_; 
lean_dec_ref(v___x_4162_);
lean_inc_ref(v_c_4141_);
lean_inc_n(v_x_4140_, 2);
lean_inc(v_a_4139_);
v___x_4163_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccsAt(v_a_4139_, v_x_4140_, v_c_4141_, v_x_4140_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
if (lean_obj_tag(v___x_4163_) == 0)
{
lean_object* v___x_4164_; lean_object* v___x_4165_; 
lean_dec_ref(v___x_4163_);
v___x_4164_ = lean_box(0);
v___x_4165_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs_spec__0(v_a_4139_, v_x_4140_, v_c_4141_, v___x_4164_, v___y_4160_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4172_; 
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4172_ == 0)
{
lean_object* v_unused_4173_; 
v_unused_4173_ = lean_ctor_get(v___x_4165_, 0);
lean_dec(v_unused_4173_);
v___x_4167_ = v___x_4165_;
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
else
{
lean_dec(v___x_4165_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4170_; 
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 0, v___x_4164_);
v___x_4170_ = v___x_4167_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v___x_4164_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
else
{
lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4181_; 
v_a_4174_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4181_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_4176_ = v___x_4165_;
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4165_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4179_; 
if (v_isShared_4177_ == 0)
{
v___x_4179_ = v___x_4176_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_a_4174_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
}
else
{
lean_dec(v___y_4160_);
lean_dec_ref(v_c_4141_);
lean_dec(v_x_4140_);
lean_dec(v_a_4139_);
return v___x_4163_;
}
}
else
{
lean_dec(v___y_4160_);
lean_dec_ref(v_c_4141_);
lean_dec(v_x_4140_);
lean_dec(v_a_4139_);
return v___x_4162_;
}
}
}
else
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4193_; 
lean_dec_ref(v_c_4141_);
lean_dec(v_x_4140_);
lean_dec(v_a_4139_);
v_a_4186_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4193_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4188_ = v___x_4154_;
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_4154_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
if (v_isShared_4189_ == 0)
{
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_a_4186_);
v___x_4191_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
return v___x_4191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs___boxed(lean_object* v_a_4194_, lean_object* v_x_4195_, lean_object* v_c_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_){
_start:
{
lean_object* v_res_4209_; 
v_res_4209_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v_a_4194_, v_x_4195_, v_c_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
lean_dec(v_a_4207_);
lean_dec_ref(v_a_4206_);
lean_dec(v_a_4205_);
lean_dec_ref(v_a_4204_);
lean_dec(v_a_4203_);
lean_dec_ref(v_a_4202_);
lean_dec(v_a_4201_);
lean_dec_ref(v_a_4200_);
lean_dec(v_a_4199_);
lean_dec(v_a_4198_);
lean_dec(v_a_4197_);
return v_res_4209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(lean_object* v_c_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_){
_start:
{
lean_object* v_p_4227_; 
v_p_4227_ = lean_ctor_get(v_c_4210_, 0);
if (lean_obj_tag(v_p_4227_) == 1)
{
lean_object* v_k_4228_; lean_object* v_v_4229_; lean_object* v_p_4230_; lean_object* v_y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___x_4281_; lean_object* v___x_4282_; uint8_t v___x_4283_; 
v_k_4228_ = lean_ctor_get(v_p_4227_, 0);
v_v_4229_ = lean_ctor_get(v_p_4227_, 1);
v_p_4230_ = lean_ctor_get(v_p_4227_, 2);
v___x_4281_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__0_spec__0___closed__0);
v___x_4282_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4283_ = lean_int_dec_eq(v_k_4228_, v___x_4282_);
if (v___x_4283_ == 0)
{
uint8_t v___x_4284_; 
v___x_4284_ = lean_int_dec_eq(v_k_4228_, v___x_4281_);
if (v___x_4284_ == 0)
{
goto v___jp_4223_;
}
else
{
if (lean_obj_tag(v_p_4230_) == 1)
{
lean_object* v_k_4285_; lean_object* v_v_4286_; lean_object* v_p_4287_; uint8_t v___x_4288_; 
v_k_4285_ = lean_ctor_get(v_p_4230_, 0);
v_v_4286_ = lean_ctor_get(v_p_4230_, 1);
v_p_4287_ = lean_ctor_get(v_p_4230_, 2);
v___x_4288_ = lean_int_dec_eq(v_k_4285_, v___x_4282_);
if (v___x_4288_ == 0)
{
goto v___jp_4223_;
}
else
{
if (lean_obj_tag(v_p_4287_) == 0)
{
v_y_4232_ = v_v_4286_;
v___y_4233_ = v_a_4211_;
v___y_4234_ = v_a_4212_;
v___y_4235_ = v_a_4213_;
v___y_4236_ = v_a_4214_;
v___y_4237_ = v_a_4215_;
v___y_4238_ = v_a_4216_;
v___y_4239_ = v_a_4217_;
v___y_4240_ = v_a_4218_;
v___y_4241_ = v_a_4219_;
v___y_4242_ = v_a_4220_;
v___y_4243_ = v_a_4221_;
goto v___jp_4231_;
}
else
{
goto v___jp_4223_;
}
}
}
else
{
goto v___jp_4223_;
}
}
}
else
{
if (lean_obj_tag(v_p_4230_) == 1)
{
lean_object* v_k_4289_; lean_object* v_v_4290_; lean_object* v_p_4291_; uint8_t v___x_4292_; 
v_k_4289_ = lean_ctor_get(v_p_4230_, 0);
v_v_4290_ = lean_ctor_get(v_p_4230_, 1);
v_p_4291_ = lean_ctor_get(v_p_4230_, 2);
v___x_4292_ = lean_int_dec_eq(v_k_4289_, v___x_4281_);
if (v___x_4292_ == 0)
{
goto v___jp_4223_;
}
else
{
if (lean_obj_tag(v_p_4291_) == 0)
{
v_y_4232_ = v_v_4290_;
v___y_4233_ = v_a_4211_;
v___y_4234_ = v_a_4212_;
v___y_4235_ = v_a_4213_;
v___y_4236_ = v_a_4214_;
v___y_4237_ = v_a_4215_;
v___y_4238_ = v_a_4216_;
v___y_4239_ = v_a_4217_;
v___y_4240_ = v_a_4218_;
v___y_4241_ = v_a_4219_;
v___y_4242_ = v_a_4220_;
v___y_4243_ = v_a_4221_;
goto v___jp_4231_;
}
else
{
goto v___jp_4223_;
}
}
}
else
{
goto v___jp_4223_;
}
}
v___jp_4231_:
{
lean_object* v___x_4244_; 
v___x_4244_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_v_4229_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v_a_4245_; lean_object* v___x_4246_; 
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
lean_inc(v_a_4245_);
lean_dec_ref(v___x_4244_);
v___x_4246_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
if (lean_obj_tag(v___x_4246_) == 0)
{
lean_object* v_a_4247_; lean_object* v___x_4248_; 
v_a_4247_ = lean_ctor_get(v___x_4246_, 0);
lean_inc(v_a_4247_);
lean_dec_ref(v___x_4246_);
v___x_4248_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_4245_, v_a_4247_, v___y_4234_);
lean_dec(v_a_4247_);
lean_dec(v_a_4245_);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4264_; 
v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4251_ = v___x_4248_;
v_isShared_4252_ = v_isSharedCheck_4264_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4248_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4264_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
uint8_t v___x_4253_; 
v___x_4253_ = lean_unbox(v_a_4249_);
lean_dec(v_a_4249_);
if (v___x_4253_ == 0)
{
uint8_t v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4257_; 
v___x_4254_ = 1;
v___x_4255_ = lean_box(v___x_4254_);
if (v_isShared_4252_ == 0)
{
lean_ctor_set(v___x_4251_, 0, v___x_4255_);
v___x_4257_ = v___x_4251_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v___x_4255_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
else
{
uint8_t v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4262_; 
v___x_4259_ = 0;
v___x_4260_ = lean_box(v___x_4259_);
if (v_isShared_4252_ == 0)
{
lean_ctor_set(v___x_4251_, 0, v___x_4260_);
v___x_4262_ = v___x_4251_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4260_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
}
else
{
return v___x_4248_;
}
}
else
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4272_; 
lean_dec(v_a_4245_);
v_a_4265_ = lean_ctor_get(v___x_4246_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4246_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4267_ = v___x_4246_;
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v___x_4246_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4270_; 
if (v_isShared_4268_ == 0)
{
v___x_4270_ = v___x_4267_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_a_4265_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
}
else
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
v_a_4273_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4275_ = v___x_4244_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4244_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
}
else
{
goto v___jp_4223_;
}
v___jp_4223_:
{
uint8_t v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___x_4224_ = 0;
v___x_4225_ = lean_box(v___x_4224_);
v___x_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4226_, 0, v___x_4225_);
return v___x_4226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq___boxed(lean_object* v_c_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v_c_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_);
lean_dec(v_a_4304_);
lean_dec_ref(v_a_4303_);
lean_dec(v_a_4302_);
lean_dec_ref(v_a_4301_);
lean_dec(v_a_4300_);
lean_dec_ref(v_a_4299_);
lean_dec(v_a_4298_);
lean_dec_ref(v_a_4297_);
lean_dec(v_a_4296_);
lean_dec(v_a_4295_);
lean_dec(v_a_4294_);
lean_dec_ref(v_c_4293_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(lean_object* v_c_4307_){
_start:
{
lean_object* v_p_4309_; 
v_p_4309_ = lean_ctor_get(v_c_4307_, 0);
if (lean_obj_tag(v_p_4309_) == 1)
{
lean_object* v_k_4310_; lean_object* v___x_4311_; uint8_t v___x_4312_; 
v_k_4310_ = lean_ctor_get(v_p_4309_, 0);
v___x_4311_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_applyEq_x3f___closed__0);
v___x_4312_ = lean_int_dec_lt(v_k_4310_, v___x_4311_);
if (v___x_4312_ == 0)
{
lean_object* v___x_4313_; 
v___x_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4313_, 0, v_c_4307_);
return v___x_4313_;
}
else
{
lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; 
v___x_4314_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
lean_inc_ref(v_p_4309_);
v___x_4315_ = l_Lean_Grind_Linarith_Poly_mul(v_p_4309_, v___x_4314_);
v___x_4316_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4316_, 0, v_c_4307_);
v___x_4317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4317_, 0, v___x_4315_);
lean_ctor_set(v___x_4317_, 1, v___x_4316_);
v___x_4318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4318_, 0, v___x_4317_);
return v___x_4318_;
}
}
else
{
lean_object* v___x_4319_; 
v___x_4319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4319_, 0, v_c_4307_);
return v___x_4319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg___boxed(lean_object* v_c_4320_, lean_object* v_a_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4320_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(lean_object* v_c_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_){
_start:
{
lean_object* v___x_4336_; 
v___x_4336_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v_c_4323_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___boxed(lean_object* v_c_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos(v_c_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_);
lean_dec(v_a_4348_);
lean_dec_ref(v_a_4347_);
lean_dec(v_a_4346_);
lean_dec_ref(v_a_4345_);
lean_dec(v_a_4344_);
lean_dec_ref(v_a_4343_);
lean_dec(v_a_4342_);
lean_dec_ref(v_a_4341_);
lean_dec(v_a_4340_);
lean_dec(v_a_4339_);
lean_dec(v_a_4338_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(lean_object* v___y_4351_, lean_object* v_snd_4352_, lean_object* v_fst_4353_, lean_object* v_s_4354_){
_start:
{
lean_object* v_structs_4355_; lean_object* v_typeIdOf_4356_; lean_object* v_exprToStructId_4357_; lean_object* v_exprToStructIdEntries_4358_; lean_object* v_forbiddenNatModules_4359_; lean_object* v_natStructs_4360_; lean_object* v_natTypeIdOf_4361_; lean_object* v_exprToNatStructId_4362_; lean_object* v___x_4363_; uint8_t v___x_4364_; 
v_structs_4355_ = lean_ctor_get(v_s_4354_, 0);
v_typeIdOf_4356_ = lean_ctor_get(v_s_4354_, 1);
v_exprToStructId_4357_ = lean_ctor_get(v_s_4354_, 2);
v_exprToStructIdEntries_4358_ = lean_ctor_get(v_s_4354_, 3);
v_forbiddenNatModules_4359_ = lean_ctor_get(v_s_4354_, 4);
v_natStructs_4360_ = lean_ctor_get(v_s_4354_, 5);
v_natTypeIdOf_4361_ = lean_ctor_get(v_s_4354_, 6);
v_exprToNatStructId_4362_ = lean_ctor_get(v_s_4354_, 7);
v___x_4363_ = lean_array_get_size(v_structs_4355_);
v___x_4364_ = lean_nat_dec_lt(v___y_4351_, v___x_4363_);
if (v___x_4364_ == 0)
{
lean_dec(v_fst_4353_);
lean_dec_ref(v_snd_4352_);
return v_s_4354_;
}
else
{
lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4428_; 
lean_inc_ref(v_exprToNatStructId_4362_);
lean_inc_ref(v_natTypeIdOf_4361_);
lean_inc_ref(v_natStructs_4360_);
lean_inc_ref(v_forbiddenNatModules_4359_);
lean_inc_ref(v_exprToStructIdEntries_4358_);
lean_inc_ref(v_exprToStructId_4357_);
lean_inc_ref(v_typeIdOf_4356_);
lean_inc_ref(v_structs_4355_);
v_isSharedCheck_4428_ = !lean_is_exclusive(v_s_4354_);
if (v_isSharedCheck_4428_ == 0)
{
lean_object* v_unused_4429_; lean_object* v_unused_4430_; lean_object* v_unused_4431_; lean_object* v_unused_4432_; lean_object* v_unused_4433_; lean_object* v_unused_4434_; lean_object* v_unused_4435_; lean_object* v_unused_4436_; 
v_unused_4429_ = lean_ctor_get(v_s_4354_, 7);
lean_dec(v_unused_4429_);
v_unused_4430_ = lean_ctor_get(v_s_4354_, 6);
lean_dec(v_unused_4430_);
v_unused_4431_ = lean_ctor_get(v_s_4354_, 5);
lean_dec(v_unused_4431_);
v_unused_4432_ = lean_ctor_get(v_s_4354_, 4);
lean_dec(v_unused_4432_);
v_unused_4433_ = lean_ctor_get(v_s_4354_, 3);
lean_dec(v_unused_4433_);
v_unused_4434_ = lean_ctor_get(v_s_4354_, 2);
lean_dec(v_unused_4434_);
v_unused_4435_ = lean_ctor_get(v_s_4354_, 1);
lean_dec(v_unused_4435_);
v_unused_4436_ = lean_ctor_get(v_s_4354_, 0);
lean_dec(v_unused_4436_);
v___x_4366_ = v_s_4354_;
v_isShared_4367_ = v_isSharedCheck_4428_;
goto v_resetjp_4365_;
}
else
{
lean_dec(v_s_4354_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4428_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v_v_4368_; lean_object* v_id_4369_; lean_object* v_ringId_x3f_4370_; lean_object* v_type_4371_; lean_object* v_u_4372_; lean_object* v_intModuleInst_4373_; lean_object* v_leInst_x3f_4374_; lean_object* v_ltInst_x3f_4375_; lean_object* v_lawfulOrderLTInst_x3f_4376_; lean_object* v_isPreorderInst_x3f_4377_; lean_object* v_orderedAddInst_x3f_4378_; lean_object* v_isLinearInst_x3f_4379_; lean_object* v_noNatDivInst_x3f_4380_; lean_object* v_ringInst_x3f_4381_; lean_object* v_commRingInst_x3f_4382_; lean_object* v_orderedRingInst_x3f_4383_; lean_object* v_fieldInst_x3f_4384_; lean_object* v_charInst_x3f_4385_; lean_object* v_zero_4386_; lean_object* v_ofNatZero_4387_; lean_object* v_one_x3f_4388_; lean_object* v_leFn_x3f_4389_; lean_object* v_ltFn_x3f_4390_; lean_object* v_addFn_4391_; lean_object* v_zsmulFn_4392_; lean_object* v_nsmulFn_4393_; lean_object* v_zsmulFn_x3f_4394_; lean_object* v_nsmulFn_x3f_4395_; lean_object* v_homomulFn_x3f_4396_; lean_object* v_subFn_4397_; lean_object* v_negFn_4398_; lean_object* v_vars_4399_; lean_object* v_varMap_4400_; lean_object* v_lowers_4401_; lean_object* v_uppers_4402_; lean_object* v_diseqs_4403_; lean_object* v_assignment_4404_; uint8_t v_caseSplits_4405_; lean_object* v_conflict_x3f_4406_; lean_object* v_diseqSplits_4407_; lean_object* v_elimEqs_4408_; lean_object* v_elimStack_4409_; lean_object* v_occurs_4410_; lean_object* v_ignored_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4427_; 
v_v_4368_ = lean_array_fget(v_structs_4355_, v___y_4351_);
v_id_4369_ = lean_ctor_get(v_v_4368_, 0);
v_ringId_x3f_4370_ = lean_ctor_get(v_v_4368_, 1);
v_type_4371_ = lean_ctor_get(v_v_4368_, 2);
v_u_4372_ = lean_ctor_get(v_v_4368_, 3);
v_intModuleInst_4373_ = lean_ctor_get(v_v_4368_, 4);
v_leInst_x3f_4374_ = lean_ctor_get(v_v_4368_, 5);
v_ltInst_x3f_4375_ = lean_ctor_get(v_v_4368_, 6);
v_lawfulOrderLTInst_x3f_4376_ = lean_ctor_get(v_v_4368_, 7);
v_isPreorderInst_x3f_4377_ = lean_ctor_get(v_v_4368_, 8);
v_orderedAddInst_x3f_4378_ = lean_ctor_get(v_v_4368_, 9);
v_isLinearInst_x3f_4379_ = lean_ctor_get(v_v_4368_, 10);
v_noNatDivInst_x3f_4380_ = lean_ctor_get(v_v_4368_, 11);
v_ringInst_x3f_4381_ = lean_ctor_get(v_v_4368_, 12);
v_commRingInst_x3f_4382_ = lean_ctor_get(v_v_4368_, 13);
v_orderedRingInst_x3f_4383_ = lean_ctor_get(v_v_4368_, 14);
v_fieldInst_x3f_4384_ = lean_ctor_get(v_v_4368_, 15);
v_charInst_x3f_4385_ = lean_ctor_get(v_v_4368_, 16);
v_zero_4386_ = lean_ctor_get(v_v_4368_, 17);
v_ofNatZero_4387_ = lean_ctor_get(v_v_4368_, 18);
v_one_x3f_4388_ = lean_ctor_get(v_v_4368_, 19);
v_leFn_x3f_4389_ = lean_ctor_get(v_v_4368_, 20);
v_ltFn_x3f_4390_ = lean_ctor_get(v_v_4368_, 21);
v_addFn_4391_ = lean_ctor_get(v_v_4368_, 22);
v_zsmulFn_4392_ = lean_ctor_get(v_v_4368_, 23);
v_nsmulFn_4393_ = lean_ctor_get(v_v_4368_, 24);
v_zsmulFn_x3f_4394_ = lean_ctor_get(v_v_4368_, 25);
v_nsmulFn_x3f_4395_ = lean_ctor_get(v_v_4368_, 26);
v_homomulFn_x3f_4396_ = lean_ctor_get(v_v_4368_, 27);
v_subFn_4397_ = lean_ctor_get(v_v_4368_, 28);
v_negFn_4398_ = lean_ctor_get(v_v_4368_, 29);
v_vars_4399_ = lean_ctor_get(v_v_4368_, 30);
v_varMap_4400_ = lean_ctor_get(v_v_4368_, 31);
v_lowers_4401_ = lean_ctor_get(v_v_4368_, 32);
v_uppers_4402_ = lean_ctor_get(v_v_4368_, 33);
v_diseqs_4403_ = lean_ctor_get(v_v_4368_, 34);
v_assignment_4404_ = lean_ctor_get(v_v_4368_, 35);
v_caseSplits_4405_ = lean_ctor_get_uint8(v_v_4368_, sizeof(void*)*42);
v_conflict_x3f_4406_ = lean_ctor_get(v_v_4368_, 36);
v_diseqSplits_4407_ = lean_ctor_get(v_v_4368_, 37);
v_elimEqs_4408_ = lean_ctor_get(v_v_4368_, 38);
v_elimStack_4409_ = lean_ctor_get(v_v_4368_, 39);
v_occurs_4410_ = lean_ctor_get(v_v_4368_, 40);
v_ignored_4411_ = lean_ctor_get(v_v_4368_, 41);
v_isSharedCheck_4427_ = !lean_is_exclusive(v_v_4368_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4413_ = v_v_4368_;
v_isShared_4414_ = v_isSharedCheck_4427_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_ignored_4411_);
lean_inc(v_occurs_4410_);
lean_inc(v_elimStack_4409_);
lean_inc(v_elimEqs_4408_);
lean_inc(v_diseqSplits_4407_);
lean_inc(v_conflict_x3f_4406_);
lean_inc(v_assignment_4404_);
lean_inc(v_diseqs_4403_);
lean_inc(v_uppers_4402_);
lean_inc(v_lowers_4401_);
lean_inc(v_varMap_4400_);
lean_inc(v_vars_4399_);
lean_inc(v_negFn_4398_);
lean_inc(v_subFn_4397_);
lean_inc(v_homomulFn_x3f_4396_);
lean_inc(v_nsmulFn_x3f_4395_);
lean_inc(v_zsmulFn_x3f_4394_);
lean_inc(v_nsmulFn_4393_);
lean_inc(v_zsmulFn_4392_);
lean_inc(v_addFn_4391_);
lean_inc(v_ltFn_x3f_4390_);
lean_inc(v_leFn_x3f_4389_);
lean_inc(v_one_x3f_4388_);
lean_inc(v_ofNatZero_4387_);
lean_inc(v_zero_4386_);
lean_inc(v_charInst_x3f_4385_);
lean_inc(v_fieldInst_x3f_4384_);
lean_inc(v_orderedRingInst_x3f_4383_);
lean_inc(v_commRingInst_x3f_4382_);
lean_inc(v_ringInst_x3f_4381_);
lean_inc(v_noNatDivInst_x3f_4380_);
lean_inc(v_isLinearInst_x3f_4379_);
lean_inc(v_orderedAddInst_x3f_4378_);
lean_inc(v_isPreorderInst_x3f_4377_);
lean_inc(v_lawfulOrderLTInst_x3f_4376_);
lean_inc(v_ltInst_x3f_4375_);
lean_inc(v_leInst_x3f_4374_);
lean_inc(v_intModuleInst_4373_);
lean_inc(v_u_4372_);
lean_inc(v_type_4371_);
lean_inc(v_ringId_x3f_4370_);
lean_inc(v_id_4369_);
lean_dec(v_v_4368_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4427_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4415_; lean_object* v_xs_x27_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4421_; 
v___x_4415_ = lean_box(0);
v_xs_x27_4416_ = lean_array_fset(v_structs_4355_, v___y_4351_, v___x_4415_);
v___x_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4417_, 0, v_snd_4352_);
v___x_4418_ = l_Lean_PersistentArray_set___redArg(v_elimEqs_4408_, v_fst_4353_, v___x_4417_);
v___x_4419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4419_, 0, v_fst_4353_);
lean_ctor_set(v___x_4419_, 1, v_elimStack_4409_);
if (v_isShared_4414_ == 0)
{
lean_ctor_set(v___x_4413_, 39, v___x_4419_);
lean_ctor_set(v___x_4413_, 38, v___x_4418_);
v___x_4421_ = v___x_4413_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_id_4369_);
lean_ctor_set(v_reuseFailAlloc_4426_, 1, v_ringId_x3f_4370_);
lean_ctor_set(v_reuseFailAlloc_4426_, 2, v_type_4371_);
lean_ctor_set(v_reuseFailAlloc_4426_, 3, v_u_4372_);
lean_ctor_set(v_reuseFailAlloc_4426_, 4, v_intModuleInst_4373_);
lean_ctor_set(v_reuseFailAlloc_4426_, 5, v_leInst_x3f_4374_);
lean_ctor_set(v_reuseFailAlloc_4426_, 6, v_ltInst_x3f_4375_);
lean_ctor_set(v_reuseFailAlloc_4426_, 7, v_lawfulOrderLTInst_x3f_4376_);
lean_ctor_set(v_reuseFailAlloc_4426_, 8, v_isPreorderInst_x3f_4377_);
lean_ctor_set(v_reuseFailAlloc_4426_, 9, v_orderedAddInst_x3f_4378_);
lean_ctor_set(v_reuseFailAlloc_4426_, 10, v_isLinearInst_x3f_4379_);
lean_ctor_set(v_reuseFailAlloc_4426_, 11, v_noNatDivInst_x3f_4380_);
lean_ctor_set(v_reuseFailAlloc_4426_, 12, v_ringInst_x3f_4381_);
lean_ctor_set(v_reuseFailAlloc_4426_, 13, v_commRingInst_x3f_4382_);
lean_ctor_set(v_reuseFailAlloc_4426_, 14, v_orderedRingInst_x3f_4383_);
lean_ctor_set(v_reuseFailAlloc_4426_, 15, v_fieldInst_x3f_4384_);
lean_ctor_set(v_reuseFailAlloc_4426_, 16, v_charInst_x3f_4385_);
lean_ctor_set(v_reuseFailAlloc_4426_, 17, v_zero_4386_);
lean_ctor_set(v_reuseFailAlloc_4426_, 18, v_ofNatZero_4387_);
lean_ctor_set(v_reuseFailAlloc_4426_, 19, v_one_x3f_4388_);
lean_ctor_set(v_reuseFailAlloc_4426_, 20, v_leFn_x3f_4389_);
lean_ctor_set(v_reuseFailAlloc_4426_, 21, v_ltFn_x3f_4390_);
lean_ctor_set(v_reuseFailAlloc_4426_, 22, v_addFn_4391_);
lean_ctor_set(v_reuseFailAlloc_4426_, 23, v_zsmulFn_4392_);
lean_ctor_set(v_reuseFailAlloc_4426_, 24, v_nsmulFn_4393_);
lean_ctor_set(v_reuseFailAlloc_4426_, 25, v_zsmulFn_x3f_4394_);
lean_ctor_set(v_reuseFailAlloc_4426_, 26, v_nsmulFn_x3f_4395_);
lean_ctor_set(v_reuseFailAlloc_4426_, 27, v_homomulFn_x3f_4396_);
lean_ctor_set(v_reuseFailAlloc_4426_, 28, v_subFn_4397_);
lean_ctor_set(v_reuseFailAlloc_4426_, 29, v_negFn_4398_);
lean_ctor_set(v_reuseFailAlloc_4426_, 30, v_vars_4399_);
lean_ctor_set(v_reuseFailAlloc_4426_, 31, v_varMap_4400_);
lean_ctor_set(v_reuseFailAlloc_4426_, 32, v_lowers_4401_);
lean_ctor_set(v_reuseFailAlloc_4426_, 33, v_uppers_4402_);
lean_ctor_set(v_reuseFailAlloc_4426_, 34, v_diseqs_4403_);
lean_ctor_set(v_reuseFailAlloc_4426_, 35, v_assignment_4404_);
lean_ctor_set(v_reuseFailAlloc_4426_, 36, v_conflict_x3f_4406_);
lean_ctor_set(v_reuseFailAlloc_4426_, 37, v_diseqSplits_4407_);
lean_ctor_set(v_reuseFailAlloc_4426_, 38, v___x_4418_);
lean_ctor_set(v_reuseFailAlloc_4426_, 39, v___x_4419_);
lean_ctor_set(v_reuseFailAlloc_4426_, 40, v_occurs_4410_);
lean_ctor_set(v_reuseFailAlloc_4426_, 41, v_ignored_4411_);
lean_ctor_set_uint8(v_reuseFailAlloc_4426_, sizeof(void*)*42, v_caseSplits_4405_);
v___x_4421_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
lean_object* v___x_4422_; lean_object* v___x_4424_; 
v___x_4422_ = lean_array_fset(v_xs_x27_4416_, v___y_4351_, v___x_4421_);
if (v_isShared_4367_ == 0)
{
lean_ctor_set(v___x_4366_, 0, v___x_4422_);
v___x_4424_ = v___x_4366_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4422_);
lean_ctor_set(v_reuseFailAlloc_4425_, 1, v_typeIdOf_4356_);
lean_ctor_set(v_reuseFailAlloc_4425_, 2, v_exprToStructId_4357_);
lean_ctor_set(v_reuseFailAlloc_4425_, 3, v_exprToStructIdEntries_4358_);
lean_ctor_set(v_reuseFailAlloc_4425_, 4, v_forbiddenNatModules_4359_);
lean_ctor_set(v_reuseFailAlloc_4425_, 5, v_natStructs_4360_);
lean_ctor_set(v_reuseFailAlloc_4425_, 6, v_natTypeIdOf_4361_);
lean_ctor_set(v_reuseFailAlloc_4425_, 7, v_exprToNatStructId_4362_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed(lean_object* v___y_4437_, lean_object* v_snd_4438_, lean_object* v_fst_4439_, lean_object* v_s_4440_){
_start:
{
lean_object* v_res_4441_; 
v_res_4441_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0(v___y_4437_, v_snd_4438_, v_fst_4439_, v_s_4440_);
lean_dec(v___y_4437_);
return v_res_4441_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1(void){
_start:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; 
v___x_4443_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__0));
v___x_4444_ = l_Lean_stringToMessageData(v___x_4443_);
return v___x_4444_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4(void){
_start:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
v___x_4450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4451_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4452_ = l_Lean_Name_append(v___x_4451_, v___x_4450_);
return v___x_4452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(lean_object* v_c_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_){
_start:
{
lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4491_; lean_object* v___y_4492_; lean_object* v___y_4493_; lean_object* v___y_4494_; lean_object* v___y_4495_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; lean_object* v___y_4500_; lean_object* v___y_4501_; lean_object* v___y_4502_; lean_object* v___y_4503_; lean_object* v___y_4504_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v_options_4532_; lean_object* v_inheritedTraceOptions_4533_; uint8_t v_hasTrace_4534_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v___y_4545_; lean_object* v___y_4546_; lean_object* v___y_4547_; lean_object* v___y_4548_; lean_object* v___y_4549_; lean_object* v___y_4550_; lean_object* v_options_4551_; lean_object* v_inheritedTraceOptions_4552_; lean_object* v___y_4553_; lean_object* v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; lean_object* v___y_4575_; lean_object* v___y_4576_; lean_object* v___y_4577_; lean_object* v___y_4578_; lean_object* v___y_4579_; lean_object* v___y_4580_; 
v_options_4532_ = lean_ctor_get(v_a_4463_, 2);
v_inheritedTraceOptions_4533_ = lean_ctor_get(v_a_4463_, 13);
v_hasTrace_4534_ = lean_ctor_get_uint8(v_options_4532_, sizeof(void*)*1);
if (v_hasTrace_4534_ == 0)
{
v___y_4570_ = v_a_4454_;
v___y_4571_ = v_a_4455_;
v___y_4572_ = v_a_4456_;
v___y_4573_ = v_a_4457_;
v___y_4574_ = v_a_4458_;
v___y_4575_ = v_a_4459_;
v___y_4576_ = v_a_4460_;
v___y_4577_ = v_a_4461_;
v___y_4578_ = v_a_4462_;
v___y_4579_ = v_a_4463_;
v___y_4580_ = v_a_4464_;
goto v___jp_4569_;
}
else
{
lean_object* v_cls_4676_; lean_object* v___x_4677_; uint8_t v___x_4678_; 
v_cls_4676_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__6));
v___x_4677_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__7);
v___x_4678_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4533_, v_options_4532_, v___x_4677_);
if (v___x_4678_ == 0)
{
v___y_4570_ = v_a_4454_;
v___y_4571_ = v_a_4455_;
v___y_4572_ = v_a_4456_;
v___y_4573_ = v_a_4457_;
v___y_4574_ = v_a_4458_;
v___y_4575_ = v_a_4459_;
v___y_4576_ = v_a_4460_;
v___y_4577_ = v_a_4461_;
v___y_4578_ = v_a_4462_;
v___y_4579_ = v_a_4463_;
v___y_4580_ = v_a_4464_;
goto v___jp_4569_;
}
else
{
lean_object* v___x_4679_; 
v___x_4679_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_c_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_);
if (lean_obj_tag(v___x_4679_) == 0)
{
lean_object* v_a_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; 
v_a_4680_ = lean_ctor_get(v___x_4679_, 0);
lean_inc(v_a_4680_);
lean_dec_ref(v___x_4679_);
v___x_4681_ = l_Lean_MessageData_ofExpr(v_a_4680_);
v___x_4682_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4676_, v___x_4681_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_dec_ref(v___x_4682_);
v___y_4570_ = v_a_4454_;
v___y_4571_ = v_a_4455_;
v___y_4572_ = v_a_4456_;
v___y_4573_ = v_a_4457_;
v___y_4574_ = v_a_4458_;
v___y_4575_ = v_a_4459_;
v___y_4576_ = v_a_4460_;
v___y_4577_ = v_a_4461_;
v___y_4578_ = v_a_4462_;
v___y_4579_ = v_a_4463_;
v___y_4580_ = v_a_4464_;
goto v___jp_4569_;
}
else
{
lean_dec_ref(v_c_4453_);
return v___x_4682_;
}
}
else
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4690_; 
lean_dec_ref(v_c_4453_);
v_a_4683_ = lean_ctor_get(v___x_4679_, 0);
v_isSharedCheck_4690_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4685_ = v___x_4679_;
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v___x_4679_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4688_; 
if (v_isShared_4686_ == 0)
{
v___x_4688_ = v___x_4685_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_a_4683_);
v___x_4688_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
return v___x_4688_;
}
}
}
}
}
v___jp_4466_:
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4467_ = lean_box(0);
v___x_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4468_, 0, v___x_4467_);
return v___x_4468_;
}
v___jp_4469_:
{
lean_object* v___f_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; 
lean_inc(v___y_4475_);
v___f_4486_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4486_, 0, v___y_4475_);
lean_closure_set(v___f_4486_, 1, v___y_4470_);
lean_closure_set(v___f_4486_, 2, v___y_4471_);
v___x_4487_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4488_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4487_, v___f_4486_, v___y_4476_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v___x_4489_; 
lean_dec_ref(v___x_4488_);
v___x_4489_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_updateOccs(v___y_4474_, v___y_4473_, v___y_4472_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_);
return v___x_4489_;
}
else
{
lean_dec(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
return v___x_4488_;
}
}
v___jp_4490_:
{
lean_object* v___x_4507_; 
v___x_4507_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_object* v_a_4508_; uint8_t v_caseSplits_4509_; 
v_a_4508_ = lean_ctor_get(v___x_4507_, 0);
lean_inc(v_a_4508_);
lean_dec_ref(v___x_4507_);
v_caseSplits_4509_ = lean_ctor_get_uint8(v_a_4508_, sizeof(void*)*42);
lean_dec(v_a_4508_);
if (v_caseSplits_4509_ == 0)
{
lean_object* v___x_4510_; 
v___x_4510_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_isImpliedEq(v___y_4493_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_);
if (lean_obj_tag(v___x_4510_) == 0)
{
lean_object* v_a_4511_; uint8_t v___x_4512_; 
v_a_4511_ = lean_ctor_get(v___x_4510_, 0);
lean_inc(v_a_4511_);
lean_dec_ref(v___x_4510_);
v___x_4512_ = lean_unbox(v_a_4511_);
lean_dec(v_a_4511_);
if (v___x_4512_ == 0)
{
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
v___y_4480_ = v___y_4501_;
v___y_4481_ = v___y_4502_;
v___y_4482_ = v___y_4503_;
v___y_4483_ = v___y_4504_;
v___y_4484_ = v___y_4505_;
v___y_4485_ = v___y_4506_;
goto v___jp_4469_;
}
else
{
lean_object* v___x_4513_; lean_object* v_a_4514_; lean_object* v___x_4515_; 
lean_inc_ref(v___y_4493_);
v___x_4513_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_ensureLeadCoeffPos___redArg(v___y_4493_);
v_a_4514_ = lean_ctor_get(v___x_4513_, 0);
lean_inc(v_a_4514_);
lean_dec_ref(v___x_4513_);
v___x_4515_ = l_Lean_Meta_Grind_Arith_Linear_propagateImpEq(v_a_4514_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_);
if (lean_obj_tag(v___x_4515_) == 0)
{
lean_dec_ref(v___x_4515_);
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
v___y_4480_ = v___y_4501_;
v___y_4481_ = v___y_4502_;
v___y_4482_ = v___y_4503_;
v___y_4483_ = v___y_4504_;
v___y_4484_ = v___y_4505_;
v___y_4485_ = v___y_4506_;
goto v___jp_4469_;
}
else
{
lean_dec(v___y_4495_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
return v___x_4515_;
}
}
}
else
{
lean_object* v_a_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4523_; 
lean_dec(v___y_4495_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
v_a_4516_ = lean_ctor_get(v___x_4510_, 0);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4518_ = v___x_4510_;
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_a_4516_);
lean_dec(v___x_4510_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4521_; 
if (v_isShared_4519_ == 0)
{
v___x_4521_ = v___x_4518_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_a_4516_);
v___x_4521_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
return v___x_4521_;
}
}
}
}
else
{
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
v___y_4480_ = v___y_4501_;
v___y_4481_ = v___y_4502_;
v___y_4482_ = v___y_4503_;
v___y_4483_ = v___y_4504_;
v___y_4484_ = v___y_4505_;
v___y_4485_ = v___y_4506_;
goto v___jp_4469_;
}
}
else
{
lean_object* v_a_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4531_; 
lean_dec(v___y_4495_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
v_a_4524_ = lean_ctor_get(v___x_4507_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4526_ = v___x_4507_;
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_a_4524_);
lean_dec(v___x_4507_);
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
v___jp_4535_:
{
lean_object* v___x_4554_; lean_object* v___x_4555_; uint8_t v___x_4556_; 
v___x_4554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__4));
v___x_4555_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert___closed__5);
v___x_4556_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4552_, v_options_4551_, v___x_4555_);
if (v___x_4556_ == 0)
{
v___y_4491_ = v___y_4536_;
v___y_4492_ = v___y_4537_;
v___y_4493_ = v___y_4538_;
v___y_4494_ = v___y_4539_;
v___y_4495_ = v___y_4540_;
v___y_4496_ = v___y_4541_;
v___y_4497_ = v___y_4542_;
v___y_4498_ = v___y_4543_;
v___y_4499_ = v___y_4544_;
v___y_4500_ = v___y_4545_;
v___y_4501_ = v___y_4546_;
v___y_4502_ = v___y_4547_;
v___y_4503_ = v___y_4548_;
v___y_4504_ = v___y_4549_;
v___y_4505_ = v___y_4550_;
v___y_4506_ = v___y_4553_;
goto v___jp_4490_;
}
else
{
lean_object* v___x_4557_; 
v___x_4557_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v___y_4538_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4553_);
if (lean_obj_tag(v___x_4557_) == 0)
{
lean_object* v_a_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
v_a_4558_ = lean_ctor_get(v___x_4557_, 0);
lean_inc(v_a_4558_);
lean_dec_ref(v___x_4557_);
v___x_4559_ = l_Lean_MessageData_ofExpr(v_a_4558_);
v___x_4560_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4554_, v___x_4559_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4553_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_dec_ref(v___x_4560_);
v___y_4491_ = v___y_4536_;
v___y_4492_ = v___y_4537_;
v___y_4493_ = v___y_4538_;
v___y_4494_ = v___y_4539_;
v___y_4495_ = v___y_4540_;
v___y_4496_ = v___y_4541_;
v___y_4497_ = v___y_4542_;
v___y_4498_ = v___y_4543_;
v___y_4499_ = v___y_4544_;
v___y_4500_ = v___y_4545_;
v___y_4501_ = v___y_4546_;
v___y_4502_ = v___y_4547_;
v___y_4503_ = v___y_4548_;
v___y_4504_ = v___y_4549_;
v___y_4505_ = v___y_4550_;
v___y_4506_ = v___y_4553_;
goto v___jp_4490_;
}
else
{
lean_dec(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec(v___y_4537_);
lean_dec_ref(v___y_4536_);
return v___x_4560_;
}
}
else
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4568_; 
lean_dec(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec(v___y_4537_);
lean_dec_ref(v___y_4536_);
v_a_4561_ = lean_ctor_get(v___x_4557_, 0);
v_isSharedCheck_4568_ = !lean_is_exclusive(v___x_4557_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4563_ = v___x_4557_;
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4557_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4566_; 
if (v_isShared_4564_ == 0)
{
v___x_4566_ = v___x_4563_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4561_);
v___x_4566_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
return v___x_4566_;
}
}
}
}
}
v___jp_4569_:
{
lean_object* v___x_4581_; 
lean_inc_ref(v___y_4579_);
v___x_4581_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_applySubsts(v_c_4453_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4581_) == 0)
{
lean_object* v_a_4582_; lean_object* v_p_4583_; lean_object* v___x_4584_; uint8_t v___x_4585_; 
v_a_4582_ = lean_ctor_get(v___x_4581_, 0);
lean_inc(v_a_4582_);
lean_dec_ref(v___x_4581_);
v_p_4583_ = lean_ctor_get(v_a_4582_, 0);
v___x_4584_ = lean_box(0);
v___x_4585_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_4583_, v___x_4584_);
if (v___x_4585_ == 0)
{
lean_object* v___x_4586_; 
v___x_4586_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_norm(v_a_4582_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_object* v_a_4587_; lean_object* v_snd_4588_; lean_object* v_options_4589_; uint8_t v_hasTrace_4590_; 
v_a_4587_ = lean_ctor_get(v___x_4586_, 0);
lean_inc(v_a_4587_);
lean_dec_ref(v___x_4586_);
v_snd_4588_ = lean_ctor_get(v_a_4587_, 1);
lean_inc(v_snd_4588_);
v_options_4589_ = lean_ctor_get(v___y_4579_, 2);
v_hasTrace_4590_ = lean_ctor_get_uint8(v_options_4589_, sizeof(void*)*1);
if (v_hasTrace_4590_ == 0)
{
lean_object* v_fst_4591_; lean_object* v_fst_4592_; lean_object* v_snd_4593_; 
v_fst_4591_ = lean_ctor_get(v_a_4587_, 0);
lean_inc(v_fst_4591_);
lean_dec(v_a_4587_);
v_fst_4592_ = lean_ctor_get(v_snd_4588_, 0);
lean_inc_n(v_fst_4592_, 2);
v_snd_4593_ = lean_ctor_get(v_snd_4588_, 1);
lean_inc_n(v_snd_4593_, 2);
lean_dec(v_snd_4588_);
v___y_4491_ = v_snd_4593_;
v___y_4492_ = v_fst_4592_;
v___y_4493_ = v_snd_4593_;
v___y_4494_ = v_fst_4592_;
v___y_4495_ = v_fst_4591_;
v___y_4496_ = v___y_4570_;
v___y_4497_ = v___y_4571_;
v___y_4498_ = v___y_4572_;
v___y_4499_ = v___y_4573_;
v___y_4500_ = v___y_4574_;
v___y_4501_ = v___y_4575_;
v___y_4502_ = v___y_4576_;
v___y_4503_ = v___y_4577_;
v___y_4504_ = v___y_4578_;
v___y_4505_ = v___y_4579_;
v___y_4506_ = v___y_4580_;
goto v___jp_4490_;
}
else
{
lean_object* v_fst_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4640_; 
v_fst_4594_ = lean_ctor_get(v_a_4587_, 0);
v_isSharedCheck_4640_ = !lean_is_exclusive(v_a_4587_);
if (v_isSharedCheck_4640_ == 0)
{
lean_object* v_unused_4641_; 
v_unused_4641_ = lean_ctor_get(v_a_4587_, 1);
lean_dec(v_unused_4641_);
v___x_4596_ = v_a_4587_;
v_isShared_4597_ = v_isSharedCheck_4640_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_fst_4594_);
lean_dec(v_a_4587_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4640_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v_fst_4598_; lean_object* v_snd_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4639_; 
v_fst_4598_ = lean_ctor_get(v_snd_4588_, 0);
v_snd_4599_ = lean_ctor_get(v_snd_4588_, 1);
v_isSharedCheck_4639_ = !lean_is_exclusive(v_snd_4588_);
if (v_isSharedCheck_4639_ == 0)
{
v___x_4601_ = v_snd_4588_;
v_isShared_4602_ = v_isSharedCheck_4639_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_snd_4599_);
lean_inc(v_fst_4598_);
lean_dec(v_snd_4588_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4639_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v_inheritedTraceOptions_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; uint8_t v___x_4606_; 
v_inheritedTraceOptions_4603_ = lean_ctor_get(v___y_4579_, 13);
v___x_4604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__4));
v___x_4605_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__7);
v___x_4606_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4603_, v_options_4589_, v___x_4605_);
if (v___x_4606_ == 0)
{
lean_del_object(v___x_4601_);
lean_del_object(v___x_4596_);
lean_inc(v_fst_4598_);
lean_inc(v_snd_4599_);
v___y_4536_ = v_snd_4599_;
v___y_4537_ = v_fst_4598_;
v___y_4538_ = v_snd_4599_;
v___y_4539_ = v_fst_4598_;
v___y_4540_ = v_fst_4594_;
v___y_4541_ = v___y_4570_;
v___y_4542_ = v___y_4571_;
v___y_4543_ = v___y_4572_;
v___y_4544_ = v___y_4573_;
v___y_4545_ = v___y_4574_;
v___y_4546_ = v___y_4575_;
v___y_4547_ = v___y_4576_;
v___y_4548_ = v___y_4577_;
v___y_4549_ = v___y_4578_;
v___y_4550_ = v___y_4579_;
v_options_4551_ = v_options_4589_;
v_inheritedTraceOptions_4552_ = v_inheritedTraceOptions_4603_;
v___y_4553_ = v___y_4580_;
goto v___jp_4535_;
}
else
{
lean_object* v___x_4607_; 
v___x_4607_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_fst_4598_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4607_) == 0)
{
lean_object* v_a_4608_; lean_object* v___x_4609_; 
v_a_4608_ = lean_ctor_get(v___x_4607_, 0);
lean_inc(v_a_4608_);
lean_dec_ref(v___x_4607_);
v___x_4609_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_snd_4599_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_object* v_a_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4614_; 
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
lean_inc(v_a_4610_);
lean_dec_ref(v___x_4609_);
v___x_4611_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__1);
v___x_4612_ = l_Lean_MessageData_ofExpr(v_a_4608_);
if (v_isShared_4602_ == 0)
{
lean_ctor_set_tag(v___x_4601_, 7);
lean_ctor_set(v___x_4601_, 1, v___x_4612_);
lean_ctor_set(v___x_4601_, 0, v___x_4611_);
v___x_4614_ = v___x_4601_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v___x_4611_);
lean_ctor_set(v_reuseFailAlloc_4622_, 1, v___x_4612_);
v___x_4614_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
lean_object* v___x_4615_; lean_object* v___x_4617_; 
v___x_4615_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
if (v_isShared_4597_ == 0)
{
lean_ctor_set_tag(v___x_4596_, 7);
lean_ctor_set(v___x_4596_, 1, v___x_4615_);
lean_ctor_set(v___x_4596_, 0, v___x_4614_);
v___x_4617_ = v___x_4596_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v___x_4614_);
lean_ctor_set(v_reuseFailAlloc_4621_, 1, v___x_4615_);
v___x_4617_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4618_ = l_Lean_MessageData_ofExpr(v_a_4610_);
v___x_4619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4619_, 0, v___x_4617_);
lean_ctor_set(v___x_4619_, 1, v___x_4618_);
v___x_4620_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4604_, v___x_4619_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_dec_ref(v___x_4620_);
lean_inc(v_fst_4598_);
lean_inc(v_snd_4599_);
v___y_4536_ = v_snd_4599_;
v___y_4537_ = v_fst_4598_;
v___y_4538_ = v_snd_4599_;
v___y_4539_ = v_fst_4598_;
v___y_4540_ = v_fst_4594_;
v___y_4541_ = v___y_4570_;
v___y_4542_ = v___y_4571_;
v___y_4543_ = v___y_4572_;
v___y_4544_ = v___y_4573_;
v___y_4545_ = v___y_4574_;
v___y_4546_ = v___y_4575_;
v___y_4547_ = v___y_4576_;
v___y_4548_ = v___y_4577_;
v___y_4549_ = v___y_4578_;
v___y_4550_ = v___y_4579_;
v_options_4551_ = v_options_4589_;
v_inheritedTraceOptions_4552_ = v_inheritedTraceOptions_4603_;
v___y_4553_ = v___y_4580_;
goto v___jp_4535_;
}
else
{
lean_dec(v_snd_4599_);
lean_dec(v_fst_4598_);
lean_dec(v_fst_4594_);
return v___x_4620_;
}
}
}
}
else
{
lean_object* v_a_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4630_; 
lean_dec(v_a_4608_);
lean_del_object(v___x_4601_);
lean_dec(v_snd_4599_);
lean_dec(v_fst_4598_);
lean_del_object(v___x_4596_);
lean_dec(v_fst_4594_);
v_a_4623_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4625_ = v___x_4609_;
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_a_4623_);
lean_dec(v___x_4609_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4628_; 
if (v_isShared_4626_ == 0)
{
v___x_4628_ = v___x_4625_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v_a_4623_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
return v___x_4628_;
}
}
}
}
else
{
lean_object* v_a_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4638_; 
lean_del_object(v___x_4601_);
lean_dec(v_snd_4599_);
lean_dec(v_fst_4598_);
lean_del_object(v___x_4596_);
lean_dec(v_fst_4594_);
v_a_4631_ = lean_ctor_get(v___x_4607_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4633_ = v___x_4607_;
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_a_4631_);
lean_dec(v___x_4607_);
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
}
}
}
}
else
{
lean_object* v_a_4642_; lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4649_; 
v_a_4642_ = lean_ctor_get(v___x_4586_, 0);
v_isSharedCheck_4649_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4649_ == 0)
{
v___x_4644_ = v___x_4586_;
v_isShared_4645_ = v_isSharedCheck_4649_;
goto v_resetjp_4643_;
}
else
{
lean_inc(v_a_4642_);
lean_dec(v___x_4586_);
v___x_4644_ = lean_box(0);
v_isShared_4645_ = v_isSharedCheck_4649_;
goto v_resetjp_4643_;
}
v_resetjp_4643_:
{
lean_object* v___x_4647_; 
if (v_isShared_4645_ == 0)
{
v___x_4647_ = v___x_4644_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v_a_4642_);
v___x_4647_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
return v___x_4647_;
}
}
}
}
else
{
lean_object* v_options_4650_; uint8_t v_hasTrace_4651_; 
v_options_4650_ = lean_ctor_get(v___y_4579_, 2);
v_hasTrace_4651_ = lean_ctor_get_uint8(v_options_4650_, sizeof(void*)*1);
if (v_hasTrace_4651_ == 0)
{
lean_dec(v_a_4582_);
goto v___jp_4466_;
}
else
{
lean_object* v_inheritedTraceOptions_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; uint8_t v___x_4655_; 
v_inheritedTraceOptions_4652_ = lean_ctor_get(v___y_4579_, 13);
v___x_4653_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__3));
v___x_4654_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___closed__4);
v___x_4655_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4652_, v_options_4650_, v___x_4654_);
if (v___x_4655_ == 0)
{
lean_dec(v_a_4582_);
goto v___jp_4466_;
}
else
{
lean_object* v___x_4656_; 
v___x_4656_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__1(v_a_4582_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
lean_dec(v_a_4582_);
if (lean_obj_tag(v___x_4656_) == 0)
{
lean_object* v_a_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; 
v_a_4657_ = lean_ctor_get(v___x_4656_, 0);
lean_inc(v_a_4657_);
lean_dec_ref(v___x_4656_);
v___x_4658_ = l_Lean_MessageData_ofExpr(v_a_4657_);
v___x_4659_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v___x_4653_, v___x_4658_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4659_) == 0)
{
lean_dec_ref(v___x_4659_);
goto v___jp_4466_;
}
else
{
return v___x_4659_;
}
}
else
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4667_; 
v_a_4660_ = lean_ctor_get(v___x_4656_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4662_ = v___x_4656_;
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___x_4656_);
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
}
}
}
else
{
lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4675_; 
v_a_4668_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4675_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4675_ == 0)
{
v___x_4670_ = v___x_4581_;
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_dec(v___x_4581_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert___boxed(lean_object* v_c_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_){
_start:
{
lean_object* v_res_4704_; 
v_res_4704_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v_c_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_);
lean_dec(v_a_4702_);
lean_dec_ref(v_a_4701_);
lean_dec(v_a_4700_);
lean_dec_ref(v_a_4699_);
lean_dec(v_a_4698_);
lean_dec_ref(v_a_4697_);
lean_dec(v_a_4696_);
lean_dec_ref(v_a_4695_);
lean_dec(v_a_4694_);
lean_dec(v_a_4693_);
lean_dec(v_a_4692_);
return v_res_4704_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2(void){
_start:
{
lean_object* v_cls_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; 
v_cls_4709_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__6));
v___x_4711_ = l_Lean_Name_append(v___x_4710_, v_cls_4709_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(lean_object* v_a_4712_, lean_object* v_b_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_){
_start:
{
lean_object* v_options_4722_; uint8_t v_hasTrace_4723_; 
v_options_4722_ = lean_ctor_get(v_a_4716_, 2);
v_hasTrace_4723_ = lean_ctor_get_uint8(v_options_4722_, sizeof(void*)*1);
if (v_hasTrace_4723_ == 0)
{
lean_dec_ref(v_b_4713_);
lean_dec_ref(v_a_4712_);
goto v___jp_4719_;
}
else
{
lean_object* v_inheritedTraceOptions_4724_; lean_object* v_cls_4725_; lean_object* v___x_4726_; uint8_t v___x_4727_; 
v_inheritedTraceOptions_4724_ = lean_ctor_get(v_a_4716_, 13);
v_cls_4725_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__1));
v___x_4726_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___closed__2);
v___x_4727_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4724_, v_options_4722_, v___x_4726_);
if (v___x_4727_ == 0)
{
lean_dec_ref(v_b_4713_);
lean_dec_ref(v_a_4712_);
goto v___jp_4719_;
}
else
{
lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4728_ = l_Lean_MessageData_ofExpr(v_a_4712_);
v___x_4729_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar___closed__9);
v___x_4730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4730_, 0, v___x_4728_);
lean_ctor_set(v___x_4730_, 1, v___x_4729_);
v___x_4731_ = l_Lean_MessageData_ofExpr(v_b_4713_);
v___x_4732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4732_, 0, v___x_4730_);
lean_ctor_set(v___x_4732_, 1, v___x_4731_);
v___x_4733_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Grind_Linarith_Poly_substVar_spec__2___redArg(v_cls_4725_, v___x_4732_, v_a_4714_, v_a_4715_, v_a_4716_, v_a_4717_);
return v___x_4733_;
}
}
v___jp_4719_:
{
lean_object* v___x_4720_; lean_object* v___x_4721_; 
v___x_4720_ = lean_box(0);
v___x_4721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4720_);
return v___x_4721_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg___boxed(lean_object* v_a_4734_, lean_object* v_b_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_){
_start:
{
lean_object* v_res_4741_; 
v_res_4741_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4734_, v_b_4735_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_);
lean_dec(v_a_4739_);
lean_dec_ref(v_a_4738_);
lean_dec(v_a_4737_);
lean_dec_ref(v_a_4736_);
return v_res_4741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(lean_object* v_a_4742_, lean_object* v_b_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_){
_start:
{
lean_object* v___x_4756_; 
v___x_4756_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_4742_, v_b_4743_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___boxed(lean_object* v_a_4757_, lean_object* v_b_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_){
_start:
{
lean_object* v_res_4771_; 
v_res_4771_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq(v_a_4757_, v_b_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_);
lean_dec(v_a_4769_);
lean_dec_ref(v_a_4768_);
lean_dec(v_a_4767_);
lean_dec_ref(v_a_4766_);
lean_dec(v_a_4765_);
lean_dec_ref(v_a_4764_);
lean_dec(v_a_4763_);
lean_dec_ref(v_a_4762_);
lean_dec(v_a_4761_);
lean_dec(v_a_4760_);
lean_dec(v_a_4759_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(lean_object* v_a_4772_, lean_object* v_b_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_){
_start:
{
lean_object* v___x_4786_; 
v___x_4786_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4772_, v_a_4775_);
if (lean_obj_tag(v___x_4786_) == 0)
{
lean_object* v_a_4787_; uint8_t v___x_4788_; lean_object* v___x_4789_; 
v_a_4787_ = lean_ctor_get(v___x_4786_, 0);
lean_inc(v_a_4787_);
lean_dec_ref(v___x_4786_);
v___x_4788_ = 0;
lean_inc_ref(v_a_4772_);
v___x_4789_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_4772_, v___x_4788_, v_a_4787_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_);
if (lean_obj_tag(v___x_4789_) == 0)
{
lean_object* v_a_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4839_; 
v_a_4790_ = lean_ctor_get(v___x_4789_, 0);
v_isSharedCheck_4839_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4839_ == 0)
{
v___x_4792_ = v___x_4789_;
v_isShared_4793_ = v_isSharedCheck_4839_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_a_4790_);
lean_dec(v___x_4789_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4839_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
if (lean_obj_tag(v_a_4790_) == 1)
{
lean_object* v_val_4794_; lean_object* v___x_4795_; 
lean_del_object(v___x_4792_);
v_val_4794_ = lean_ctor_get(v_a_4790_, 0);
lean_inc(v_val_4794_);
lean_dec_ref(v_a_4790_);
v___x_4795_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4773_, v_a_4775_);
if (lean_obj_tag(v___x_4795_) == 0)
{
lean_object* v_a_4796_; lean_object* v___x_4797_; 
v_a_4796_ = lean_ctor_get(v___x_4795_, 0);
lean_inc(v_a_4796_);
lean_dec_ref(v___x_4795_);
lean_inc_ref(v_b_4773_);
v___x_4797_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_4773_, v___x_4788_, v_a_4796_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_);
if (lean_obj_tag(v___x_4797_) == 0)
{
lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4818_; 
v_a_4798_ = lean_ctor_get(v___x_4797_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4797_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4800_ = v___x_4797_;
v_isShared_4801_ = v_isSharedCheck_4818_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4797_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4818_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
if (lean_obj_tag(v_a_4798_) == 1)
{
lean_object* v_val_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; uint8_t v___x_4806_; 
v_val_4802_ = lean_ctor_get(v_a_4798_, 0);
lean_inc_n(v_val_4802_, 2);
lean_dec_ref(v_a_4798_);
lean_inc(v_val_4794_);
v___x_4803_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4803_, 0, v_val_4794_);
lean_ctor_set(v___x_4803_, 1, v_val_4802_);
v___x_4804_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4803_);
v___x_4805_ = lean_box(0);
v___x_4806_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4804_, v___x_4805_);
if (v___x_4806_ == 0)
{
lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; 
lean_del_object(v___x_4800_);
v___x_4807_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4807_, 0, v_a_4772_);
lean_ctor_set(v___x_4807_, 1, v_b_4773_);
lean_ctor_set(v___x_4807_, 2, v_val_4794_);
lean_ctor_set(v___x_4807_, 3, v_val_4802_);
v___x_4808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4808_, 0, v___x_4804_);
lean_ctor_set(v___x_4808_, 1, v___x_4807_);
v___x_4809_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_4808_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_);
return v___x_4809_;
}
else
{
lean_object* v___x_4810_; lean_object* v___x_4812_; 
lean_dec(v___x_4804_);
lean_dec(v_val_4802_);
lean_dec(v_val_4794_);
lean_dec_ref(v_b_4773_);
lean_dec_ref(v_a_4772_);
v___x_4810_ = lean_box(0);
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 0, v___x_4810_);
v___x_4812_ = v___x_4800_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v___x_4810_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
}
else
{
lean_object* v___x_4814_; lean_object* v___x_4816_; 
lean_dec(v_a_4798_);
lean_dec(v_val_4794_);
lean_dec_ref(v_b_4773_);
lean_dec_ref(v_a_4772_);
v___x_4814_ = lean_box(0);
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 0, v___x_4814_);
v___x_4816_ = v___x_4800_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v___x_4814_);
v___x_4816_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
return v___x_4816_;
}
}
}
}
else
{
lean_object* v_a_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4826_; 
lean_dec(v_val_4794_);
lean_dec_ref(v_b_4773_);
lean_dec_ref(v_a_4772_);
v_a_4819_ = lean_ctor_get(v___x_4797_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4797_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4821_ = v___x_4797_;
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_a_4819_);
lean_dec(v___x_4797_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4824_; 
if (v_isShared_4822_ == 0)
{
v___x_4824_ = v___x_4821_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_a_4819_);
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
lean_dec(v_val_4794_);
lean_dec_ref(v_b_4773_);
lean_dec_ref(v_a_4772_);
v_a_4827_ = lean_ctor_get(v___x_4795_, 0);
v_isSharedCheck_4834_ = !lean_is_exclusive(v___x_4795_);
if (v_isSharedCheck_4834_ == 0)
{
v___x_4829_ = v___x_4795_;
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
else
{
lean_inc(v_a_4827_);
lean_dec(v___x_4795_);
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
lean_object* v___x_4835_; lean_object* v___x_4837_; 
lean_dec(v_a_4790_);
lean_dec_ref(v_b_4773_);
lean_dec_ref(v_a_4772_);
v___x_4835_ = lean_box(0);
if (v_isShared_4793_ == 0)
{
lean_ctor_set(v___x_4792_, 0, v___x_4835_);
v___x_4837_ = v___x_4792_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4838_; 
v_reuseFailAlloc_4838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4838_, 0, v___x_4835_);
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
lean_dec_ref(v_b_4773_);
lean_dec_ref(v_a_4772_);
v_a_4840_ = lean_ctor_get(v___x_4789_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4842_ = v___x_4789_;
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_a_4840_);
lean_dec(v___x_4789_);
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
lean_object* v_a_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4855_; 
lean_dec_ref(v_b_4773_);
lean_dec_ref(v_a_4772_);
v_a_4848_ = lean_ctor_get(v___x_4786_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4786_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4850_ = v___x_4786_;
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_a_4848_);
lean_dec(v___x_4786_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v___x_4853_; 
if (v_isShared_4851_ == 0)
{
v___x_4853_ = v___x_4850_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v_a_4848_);
v___x_4853_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
return v___x_4853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq___boxed(lean_object* v_a_4856_, lean_object* v_b_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_){
_start:
{
lean_object* v_res_4870_; 
v_res_4870_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_4856_, v_b_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_);
lean_dec(v_a_4868_);
lean_dec_ref(v_a_4867_);
lean_dec(v_a_4866_);
lean_dec_ref(v_a_4865_);
lean_dec(v_a_4864_);
lean_dec_ref(v_a_4863_);
lean_dec(v_a_4862_);
lean_dec_ref(v_a_4861_);
lean_dec(v_a_4860_);
lean_dec(v_a_4859_);
lean_dec(v_a_4858_);
return v_res_4870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(lean_object* v_a_4871_, lean_object* v_b_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_){
_start:
{
lean_object* v___x_4885_; 
v___x_4885_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
if (lean_obj_tag(v___x_4885_) == 0)
{
lean_object* v_a_4886_; lean_object* v___x_4887_; 
v_a_4886_ = lean_ctor_get(v___x_4885_, 0);
lean_inc(v_a_4886_);
lean_dec_ref(v___x_4885_);
lean_inc_ref(v_a_4871_);
v___x_4887_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_4871_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
if (lean_obj_tag(v___x_4887_) == 0)
{
lean_object* v_a_4888_; lean_object* v_fst_4889_; lean_object* v___x_4890_; 
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
lean_inc(v_a_4888_);
lean_dec_ref(v___x_4887_);
v_fst_4889_ = lean_ctor_get(v_a_4888_, 0);
lean_inc(v_fst_4889_);
lean_dec(v_a_4888_);
lean_inc_ref(v_b_4872_);
v___x_4890_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_4872_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
if (lean_obj_tag(v___x_4890_) == 0)
{
lean_object* v_a_4891_; lean_object* v_fst_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4975_; 
v_a_4891_ = lean_ctor_get(v___x_4890_, 0);
lean_inc(v_a_4891_);
lean_dec_ref(v___x_4890_);
v_fst_4892_ = lean_ctor_get(v_a_4891_, 0);
v_isSharedCheck_4975_ = !lean_is_exclusive(v_a_4891_);
if (v_isSharedCheck_4975_ == 0)
{
lean_object* v_unused_4976_; 
v_unused_4976_ = lean_ctor_get(v_a_4891_, 1);
lean_dec(v_unused_4976_);
v___x_4894_ = v_a_4891_;
v_isShared_4895_ = v_isSharedCheck_4975_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_fst_4892_);
lean_dec(v_a_4891_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4975_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4896_; 
v___x_4896_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4871_, v_a_4874_);
if (lean_obj_tag(v___x_4896_) == 0)
{
lean_object* v_a_4897_; lean_object* v_id_4898_; lean_object* v_structId_4899_; uint8_t v___x_4900_; lean_object* v___x_4901_; 
v_a_4897_ = lean_ctor_get(v___x_4896_, 0);
lean_inc(v_a_4897_);
lean_dec_ref(v___x_4896_);
v_id_4898_ = lean_ctor_get(v_a_4886_, 0);
lean_inc(v_id_4898_);
v_structId_4899_ = lean_ctor_get(v_a_4886_, 1);
lean_inc(v_structId_4899_);
lean_dec(v_a_4886_);
v___x_4900_ = 0;
v___x_4901_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4889_, v___x_4900_, v_a_4897_, v_structId_4899_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
if (lean_obj_tag(v___x_4901_) == 0)
{
lean_object* v_a_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4958_; 
v_a_4902_ = lean_ctor_get(v___x_4901_, 0);
v_isSharedCheck_4958_ = !lean_is_exclusive(v___x_4901_);
if (v_isSharedCheck_4958_ == 0)
{
v___x_4904_ = v___x_4901_;
v_isShared_4905_ = v_isSharedCheck_4958_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_a_4902_);
lean_dec(v___x_4901_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4958_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
if (lean_obj_tag(v_a_4902_) == 1)
{
lean_object* v_val_4906_; lean_object* v___x_4907_; 
lean_del_object(v___x_4904_);
v_val_4906_ = lean_ctor_get(v_a_4902_, 0);
lean_inc(v_val_4906_);
lean_dec_ref(v_a_4902_);
v___x_4907_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4872_, v_a_4874_);
if (lean_obj_tag(v___x_4907_) == 0)
{
lean_object* v_a_4908_; lean_object* v___x_4909_; 
v_a_4908_ = lean_ctor_get(v___x_4907_, 0);
lean_inc(v_a_4908_);
lean_dec_ref(v___x_4907_);
v___x_4909_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_4892_, v___x_4900_, v_a_4908_, v_structId_4899_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v_a_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4937_; 
v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4912_ = v___x_4909_;
v_isShared_4913_ = v_isSharedCheck_4937_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_a_4910_);
lean_dec(v___x_4909_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4937_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
if (lean_obj_tag(v_a_4910_) == 1)
{
lean_object* v_val_4914_; lean_object* v___x_4916_; 
v_val_4914_ = lean_ctor_get(v_a_4910_, 0);
lean_inc_n(v_val_4914_, 2);
lean_dec_ref(v_a_4910_);
lean_inc(v_val_4906_);
if (v_isShared_4895_ == 0)
{
lean_ctor_set_tag(v___x_4894_, 3);
lean_ctor_set(v___x_4894_, 1, v_val_4914_);
lean_ctor_set(v___x_4894_, 0, v_val_4906_);
v___x_4916_ = v___x_4894_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4932_; 
v_reuseFailAlloc_4932_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4932_, 0, v_val_4906_);
lean_ctor_set(v_reuseFailAlloc_4932_, 1, v_val_4914_);
v___x_4916_ = v_reuseFailAlloc_4932_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
lean_object* v___x_4917_; lean_object* v___x_4918_; uint8_t v___x_4919_; 
v___x_4917_ = l_Lean_Grind_Linarith_Expr_norm(v___x_4916_);
v___x_4918_ = lean_box(0);
v___x_4919_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4917_, v___x_4918_);
if (v___x_4919_ == 0)
{
lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; 
lean_del_object(v___x_4912_);
lean_inc(v_val_4914_);
lean_inc(v_val_4906_);
lean_inc(v_id_4898_);
lean_inc_ref(v_b_4872_);
lean_inc_ref(v_a_4871_);
v___x_4920_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4920_, 0, v_a_4871_);
lean_ctor_set(v___x_4920_, 1, v_b_4872_);
lean_ctor_set(v___x_4920_, 2, v_id_4898_);
lean_ctor_set(v___x_4920_, 3, v_val_4906_);
lean_ctor_set(v___x_4920_, 4, v_val_4914_);
lean_inc(v___x_4917_);
v___x_4921_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4921_, 0, v___x_4917_);
lean_ctor_set(v___x_4921_, 1, v___x_4920_);
lean_ctor_set_uint8(v___x_4921_, sizeof(void*)*2, v___x_4900_);
v___x_4922_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4921_, v_structId_4899_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
if (lean_obj_tag(v___x_4922_) == 0)
{
lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; 
lean_dec_ref(v___x_4922_);
v___x_4923_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27___closed__0);
v___x_4924_ = l_Lean_Grind_Linarith_Poly_mul(v___x_4917_, v___x_4923_);
v___x_4925_ = lean_alloc_ctor(11, 5, 0);
lean_ctor_set(v___x_4925_, 0, v_b_4872_);
lean_ctor_set(v___x_4925_, 1, v_a_4871_);
lean_ctor_set(v___x_4925_, 2, v_id_4898_);
lean_ctor_set(v___x_4925_, 3, v_val_4914_);
lean_ctor_set(v___x_4925_, 4, v_val_4906_);
v___x_4926_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4926_, 0, v___x_4924_);
lean_ctor_set(v___x_4926_, 1, v___x_4925_);
lean_ctor_set_uint8(v___x_4926_, sizeof(void*)*2, v___x_4900_);
v___x_4927_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(v___x_4926_, v_structId_4899_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
lean_dec(v_structId_4899_);
return v___x_4927_;
}
else
{
lean_dec(v___x_4917_);
lean_dec(v_val_4914_);
lean_dec(v_val_4906_);
lean_dec(v_structId_4899_);
lean_dec(v_id_4898_);
lean_dec_ref(v_b_4872_);
lean_dec_ref(v_a_4871_);
return v___x_4922_;
}
}
else
{
lean_object* v___x_4928_; lean_object* v___x_4930_; 
lean_dec(v___x_4917_);
lean_dec(v_val_4914_);
lean_dec(v_val_4906_);
lean_dec(v_structId_4899_);
lean_dec(v_id_4898_);
lean_dec_ref(v_b_4872_);
lean_dec_ref(v_a_4871_);
v___x_4928_ = lean_box(0);
if (v_isShared_4913_ == 0)
{
lean_ctor_set(v___x_4912_, 0, v___x_4928_);
v___x_4930_ = v___x_4912_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v___x_4928_);
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
lean_object* v___x_4933_; lean_object* v___x_4935_; 
lean_dec(v_a_4910_);
lean_dec(v_val_4906_);
lean_dec(v_structId_4899_);
lean_dec(v_id_4898_);
lean_del_object(v___x_4894_);
lean_dec_ref(v_b_4872_);
lean_dec_ref(v_a_4871_);
v___x_4933_ = lean_box(0);
if (v_isShared_4913_ == 0)
{
lean_ctor_set(v___x_4912_, 0, v___x_4933_);
v___x_4935_ = v___x_4912_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v___x_4933_);
v___x_4935_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
return v___x_4935_;
}
}
}
}
else
{
lean_object* v_a_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4945_; 
lean_dec(v_val_4906_);
lean_dec(v_structId_4899_);
lean_dec(v_id_4898_);
lean_del_object(v___x_4894_);
lean_dec_ref(v_b_4872_);
lean_dec_ref(v_a_4871_);
v_a_4938_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4940_ = v___x_4909_;
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_dec(v___x_4909_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4943_; 
if (v_isShared_4941_ == 0)
{
v___x_4943_ = v___x_4940_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4938_);
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
lean_dec(v_val_4906_);
lean_dec(v_structId_4899_);
lean_dec(v_id_4898_);
lean_del_object(v___x_4894_);
lean_dec(v_fst_4892_);
lean_dec_ref(v_b_4872_);
lean_dec_ref(v_a_4871_);
v_a_4946_ = lean_ctor_get(v___x_4907_, 0);
v_isSharedCheck_4953_ = !lean_is_exclusive(v___x_4907_);
if (v_isSharedCheck_4953_ == 0)
{
v___x_4948_ = v___x_4907_;
v_isShared_4949_ = v_isSharedCheck_4953_;
goto v_resetjp_4947_;
}
else
{
lean_inc(v_a_4946_);
lean_dec(v___x_4907_);
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
lean_object* v___x_4954_; lean_object* v___x_4956_; 
lean_dec(v_a_4902_);
lean_dec(v_structId_4899_);
lean_dec(v_id_4898_);
lean_del_object(v___x_4894_);
lean_dec(v_fst_4892_);
lean_dec_ref(v_b_4872_);
lean_dec_ref(v_a_4871_);
v___x_4954_ = lean_box(0);
if (v_isShared_4905_ == 0)
{
lean_ctor_set(v___x_4904_, 0, v___x_4954_);
v___x_4956_ = v___x_4904_;
goto v_reusejp_4955_;
}
else
{
lean_object* v_reuseFailAlloc_4957_; 
v_reuseFailAlloc_4957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4957_, 0, v___x_4954_);
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
lean_dec(v_structId_4899_);
lean_dec(v_id_4898_);
lean_del_object(v___x_4894_);
lean_dec(v_fst_4892_);
lean_dec_ref(v_b_4872_);
lean_dec_ref(v_a_4871_);
v_a_4959_ = lean_ctor_get(v___x_4901_, 0);
v_isSharedCheck_4966_ = !lean_is_exclusive(v___x_4901_);
if (v_isSharedCheck_4966_ == 0)
{
v___x_4961_ = v___x_4901_;
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_a_4959_);
lean_dec(v___x_4901_);
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
lean_object* v_a_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_4974_; 
lean_del_object(v___x_4894_);
lean_dec(v_fst_4892_);
lean_dec(v_fst_4889_);
lean_dec(v_a_4886_);
lean_dec_ref(v_b_4872_);
lean_dec_ref(v_a_4871_);
v_a_4967_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4969_ = v___x_4896_;
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_a_4967_);
lean_dec(v___x_4896_);
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
}
else
{
lean_object* v_a_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_4984_; 
lean_dec(v_fst_4889_);
lean_dec(v_a_4886_);
lean_dec_ref(v_b_4872_);
lean_dec_ref(v_a_4871_);
v_a_4977_ = lean_ctor_get(v___x_4890_, 0);
v_isSharedCheck_4984_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4984_ == 0)
{
v___x_4979_ = v___x_4890_;
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
else
{
lean_inc(v_a_4977_);
lean_dec(v___x_4890_);
v___x_4979_ = lean_box(0);
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
v_resetjp_4978_:
{
lean_object* v___x_4982_; 
if (v_isShared_4980_ == 0)
{
v___x_4982_ = v___x_4979_;
goto v_reusejp_4981_;
}
else
{
lean_object* v_reuseFailAlloc_4983_; 
v_reuseFailAlloc_4983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4983_, 0, v_a_4977_);
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
lean_dec(v_a_4886_);
lean_dec_ref(v_b_4872_);
lean_dec_ref(v_a_4871_);
v_a_4985_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4992_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4992_ == 0)
{
v___x_4987_ = v___x_4887_;
v_isShared_4988_ = v_isSharedCheck_4992_;
goto v_resetjp_4986_;
}
else
{
lean_inc(v_a_4985_);
lean_dec(v___x_4887_);
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
lean_dec_ref(v_b_4872_);
lean_dec_ref(v_a_4871_);
v_a_4993_ = lean_ctor_get(v___x_4885_, 0);
v_isSharedCheck_5000_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_5000_ == 0)
{
v___x_4995_ = v___x_4885_;
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
else
{
lean_inc(v_a_4993_);
lean_dec(v___x_4885_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27___boxed(lean_object* v_a_5001_, lean_object* v_b_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_){
_start:
{
lean_object* v_res_5015_; 
v_res_5015_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5001_, v_b_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_);
lean_dec(v_a_5013_);
lean_dec_ref(v_a_5012_);
lean_dec(v_a_5011_);
lean_dec_ref(v_a_5010_);
lean_dec(v_a_5009_);
lean_dec_ref(v_a_5008_);
lean_dec(v_a_5007_);
lean_dec_ref(v_a_5006_);
lean_dec(v_a_5005_);
lean_dec(v_a_5004_);
lean_dec(v_a_5003_);
return v_res_5015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(lean_object* v_a_5016_, lean_object* v_b_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_){
_start:
{
lean_object* v___x_5030_; 
v___x_5030_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_);
if (lean_obj_tag(v___x_5030_) == 0)
{
lean_object* v_a_5031_; lean_object* v___x_5032_; 
v_a_5031_ = lean_ctor_get(v___x_5030_, 0);
lean_inc(v_a_5031_);
lean_dec_ref(v___x_5030_);
lean_inc_ref(v_a_5016_);
v___x_5032_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5016_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_);
if (lean_obj_tag(v___x_5032_) == 0)
{
lean_object* v_a_5033_; lean_object* v_fst_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5130_; 
v_a_5033_ = lean_ctor_get(v___x_5032_, 0);
lean_inc(v_a_5033_);
lean_dec_ref(v___x_5032_);
v_fst_5034_ = lean_ctor_get(v_a_5033_, 0);
v_isSharedCheck_5130_ = !lean_is_exclusive(v_a_5033_);
if (v_isSharedCheck_5130_ == 0)
{
lean_object* v_unused_5131_; 
v_unused_5131_ = lean_ctor_get(v_a_5033_, 1);
lean_dec(v_unused_5131_);
v___x_5036_ = v_a_5033_;
v_isShared_5037_ = v_isSharedCheck_5130_;
goto v_resetjp_5035_;
}
else
{
lean_inc(v_fst_5034_);
lean_dec(v_a_5033_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5130_;
goto v_resetjp_5035_;
}
v_resetjp_5035_:
{
lean_object* v___x_5038_; 
lean_inc_ref(v_b_5017_);
v___x_5038_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_);
if (lean_obj_tag(v___x_5038_) == 0)
{
lean_object* v_a_5039_; lean_object* v_fst_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5120_; 
v_a_5039_ = lean_ctor_get(v___x_5038_, 0);
lean_inc(v_a_5039_);
lean_dec_ref(v___x_5038_);
v_fst_5040_ = lean_ctor_get(v_a_5039_, 0);
v_isSharedCheck_5120_ = !lean_is_exclusive(v_a_5039_);
if (v_isSharedCheck_5120_ == 0)
{
lean_object* v_unused_5121_; 
v_unused_5121_ = lean_ctor_get(v_a_5039_, 1);
lean_dec(v_unused_5121_);
v___x_5042_ = v_a_5039_;
v_isShared_5043_ = v_isSharedCheck_5120_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_fst_5040_);
lean_dec(v_a_5039_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5120_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
lean_object* v___x_5044_; 
v___x_5044_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5016_, v_a_5019_);
if (lean_obj_tag(v___x_5044_) == 0)
{
lean_object* v_a_5045_; lean_object* v_id_5046_; lean_object* v_structId_5047_; uint8_t v___x_5048_; lean_object* v___x_5049_; 
v_a_5045_ = lean_ctor_get(v___x_5044_, 0);
lean_inc(v_a_5045_);
lean_dec_ref(v___x_5044_);
v_id_5046_ = lean_ctor_get(v_a_5031_, 0);
lean_inc(v_id_5046_);
v_structId_5047_ = lean_ctor_get(v_a_5031_, 1);
lean_inc(v_structId_5047_);
lean_dec(v_a_5031_);
v___x_5048_ = 0;
v___x_5049_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5034_, v___x_5048_, v_a_5045_, v_structId_5047_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_);
if (lean_obj_tag(v___x_5049_) == 0)
{
lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5103_; 
v_a_5050_ = lean_ctor_get(v___x_5049_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5052_ = v___x_5049_;
v_isShared_5053_ = v_isSharedCheck_5103_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_dec(v___x_5049_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5103_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
if (lean_obj_tag(v_a_5050_) == 1)
{
lean_object* v_val_5054_; lean_object* v___x_5055_; 
lean_del_object(v___x_5052_);
v_val_5054_ = lean_ctor_get(v_a_5050_, 0);
lean_inc(v_val_5054_);
lean_dec_ref(v_a_5050_);
v___x_5055_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5017_, v_a_5019_);
if (lean_obj_tag(v___x_5055_) == 0)
{
lean_object* v_a_5056_; lean_object* v___x_5057_; 
v_a_5056_ = lean_ctor_get(v___x_5055_, 0);
lean_inc(v_a_5056_);
lean_dec_ref(v___x_5055_);
v___x_5057_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5040_, v___x_5048_, v_a_5056_, v_structId_5047_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_);
if (lean_obj_tag(v___x_5057_) == 0)
{
lean_object* v_a_5058_; lean_object* v___x_5060_; uint8_t v_isShared_5061_; uint8_t v_isSharedCheck_5082_; 
v_a_5058_ = lean_ctor_get(v___x_5057_, 0);
v_isSharedCheck_5082_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5082_ == 0)
{
v___x_5060_ = v___x_5057_;
v_isShared_5061_ = v_isSharedCheck_5082_;
goto v_resetjp_5059_;
}
else
{
lean_inc(v_a_5058_);
lean_dec(v___x_5057_);
v___x_5060_ = lean_box(0);
v_isShared_5061_ = v_isSharedCheck_5082_;
goto v_resetjp_5059_;
}
v_resetjp_5059_:
{
if (lean_obj_tag(v_a_5058_) == 1)
{
lean_object* v_val_5062_; lean_object* v___x_5064_; 
v_val_5062_ = lean_ctor_get(v_a_5058_, 0);
lean_inc_n(v_val_5062_, 2);
lean_dec_ref(v_a_5058_);
lean_inc(v_val_5054_);
if (v_isShared_5043_ == 0)
{
lean_ctor_set_tag(v___x_5042_, 3);
lean_ctor_set(v___x_5042_, 1, v_val_5062_);
lean_ctor_set(v___x_5042_, 0, v_val_5054_);
v___x_5064_ = v___x_5042_;
goto v_reusejp_5063_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_val_5054_);
lean_ctor_set(v_reuseFailAlloc_5077_, 1, v_val_5062_);
v___x_5064_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5063_;
}
v_reusejp_5063_:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; uint8_t v___x_5067_; 
v___x_5065_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5064_);
v___x_5066_ = lean_box(0);
v___x_5067_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_5065_, v___x_5066_);
if (v___x_5067_ == 0)
{
lean_object* v___x_5068_; lean_object* v___x_5070_; 
lean_del_object(v___x_5060_);
v___x_5068_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5068_, 0, v_a_5016_);
lean_ctor_set(v___x_5068_, 1, v_b_5017_);
lean_ctor_set(v___x_5068_, 2, v_id_5046_);
lean_ctor_set(v___x_5068_, 3, v_val_5054_);
lean_ctor_set(v___x_5068_, 4, v_val_5062_);
if (v_isShared_5037_ == 0)
{
lean_ctor_set(v___x_5036_, 1, v___x_5068_);
lean_ctor_set(v___x_5036_, 0, v___x_5065_);
v___x_5070_ = v___x_5036_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v___x_5065_);
lean_ctor_set(v_reuseFailAlloc_5072_, 1, v___x_5068_);
v___x_5070_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
lean_object* v___x_5071_; 
v___x_5071_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_EqCnstr_assert(v___x_5070_, v_structId_5047_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_);
lean_dec(v_structId_5047_);
return v___x_5071_;
}
}
else
{
lean_object* v___x_5073_; lean_object* v___x_5075_; 
lean_dec(v___x_5065_);
lean_dec(v_val_5062_);
lean_dec(v_val_5054_);
lean_dec(v_structId_5047_);
lean_dec(v_id_5046_);
lean_del_object(v___x_5036_);
lean_dec_ref(v_b_5017_);
lean_dec_ref(v_a_5016_);
v___x_5073_ = lean_box(0);
if (v_isShared_5061_ == 0)
{
lean_ctor_set(v___x_5060_, 0, v___x_5073_);
v___x_5075_ = v___x_5060_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v___x_5073_);
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
lean_object* v___x_5078_; lean_object* v___x_5080_; 
lean_dec(v_a_5058_);
lean_dec(v_val_5054_);
lean_dec(v_structId_5047_);
lean_dec(v_id_5046_);
lean_del_object(v___x_5042_);
lean_del_object(v___x_5036_);
lean_dec_ref(v_b_5017_);
lean_dec_ref(v_a_5016_);
v___x_5078_ = lean_box(0);
if (v_isShared_5061_ == 0)
{
lean_ctor_set(v___x_5060_, 0, v___x_5078_);
v___x_5080_ = v___x_5060_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v___x_5078_);
v___x_5080_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
return v___x_5080_;
}
}
}
}
else
{
lean_object* v_a_5083_; lean_object* v___x_5085_; uint8_t v_isShared_5086_; uint8_t v_isSharedCheck_5090_; 
lean_dec(v_val_5054_);
lean_dec(v_structId_5047_);
lean_dec(v_id_5046_);
lean_del_object(v___x_5042_);
lean_del_object(v___x_5036_);
lean_dec_ref(v_b_5017_);
lean_dec_ref(v_a_5016_);
v_a_5083_ = lean_ctor_get(v___x_5057_, 0);
v_isSharedCheck_5090_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5085_ = v___x_5057_;
v_isShared_5086_ = v_isSharedCheck_5090_;
goto v_resetjp_5084_;
}
else
{
lean_inc(v_a_5083_);
lean_dec(v___x_5057_);
v___x_5085_ = lean_box(0);
v_isShared_5086_ = v_isSharedCheck_5090_;
goto v_resetjp_5084_;
}
v_resetjp_5084_:
{
lean_object* v___x_5088_; 
if (v_isShared_5086_ == 0)
{
v___x_5088_ = v___x_5085_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v_a_5083_);
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
lean_dec(v_val_5054_);
lean_dec(v_structId_5047_);
lean_dec(v_id_5046_);
lean_del_object(v___x_5042_);
lean_dec(v_fst_5040_);
lean_del_object(v___x_5036_);
lean_dec_ref(v_b_5017_);
lean_dec_ref(v_a_5016_);
v_a_5091_ = lean_ctor_get(v___x_5055_, 0);
v_isSharedCheck_5098_ = !lean_is_exclusive(v___x_5055_);
if (v_isSharedCheck_5098_ == 0)
{
v___x_5093_ = v___x_5055_;
v_isShared_5094_ = v_isSharedCheck_5098_;
goto v_resetjp_5092_;
}
else
{
lean_inc(v_a_5091_);
lean_dec(v___x_5055_);
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
lean_object* v___x_5099_; lean_object* v___x_5101_; 
lean_dec(v_a_5050_);
lean_dec(v_structId_5047_);
lean_dec(v_id_5046_);
lean_del_object(v___x_5042_);
lean_dec(v_fst_5040_);
lean_del_object(v___x_5036_);
lean_dec_ref(v_b_5017_);
lean_dec_ref(v_a_5016_);
v___x_5099_ = lean_box(0);
if (v_isShared_5053_ == 0)
{
lean_ctor_set(v___x_5052_, 0, v___x_5099_);
v___x_5101_ = v___x_5052_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v___x_5099_);
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
lean_dec(v_structId_5047_);
lean_dec(v_id_5046_);
lean_del_object(v___x_5042_);
lean_dec(v_fst_5040_);
lean_del_object(v___x_5036_);
lean_dec_ref(v_b_5017_);
lean_dec_ref(v_a_5016_);
v_a_5104_ = lean_ctor_get(v___x_5049_, 0);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5106_ = v___x_5049_;
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
else
{
lean_inc(v_a_5104_);
lean_dec(v___x_5049_);
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
lean_object* v_a_5112_; lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5119_; 
lean_del_object(v___x_5042_);
lean_dec(v_fst_5040_);
lean_del_object(v___x_5036_);
lean_dec(v_fst_5034_);
lean_dec(v_a_5031_);
lean_dec_ref(v_b_5017_);
lean_dec_ref(v_a_5016_);
v_a_5112_ = lean_ctor_get(v___x_5044_, 0);
v_isSharedCheck_5119_ = !lean_is_exclusive(v___x_5044_);
if (v_isSharedCheck_5119_ == 0)
{
v___x_5114_ = v___x_5044_;
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
else
{
lean_inc(v_a_5112_);
lean_dec(v___x_5044_);
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
lean_del_object(v___x_5036_);
lean_dec(v_fst_5034_);
lean_dec(v_a_5031_);
lean_dec_ref(v_b_5017_);
lean_dec_ref(v_a_5016_);
v_a_5122_ = lean_ctor_get(v___x_5038_, 0);
v_isSharedCheck_5129_ = !lean_is_exclusive(v___x_5038_);
if (v_isSharedCheck_5129_ == 0)
{
v___x_5124_ = v___x_5038_;
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_a_5122_);
lean_dec(v___x_5038_);
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
}
else
{
lean_object* v_a_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5139_; 
lean_dec(v_a_5031_);
lean_dec_ref(v_b_5017_);
lean_dec_ref(v_a_5016_);
v_a_5132_ = lean_ctor_get(v___x_5032_, 0);
v_isSharedCheck_5139_ = !lean_is_exclusive(v___x_5032_);
if (v_isSharedCheck_5139_ == 0)
{
v___x_5134_ = v___x_5032_;
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_a_5132_);
lean_dec(v___x_5032_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
lean_object* v___x_5137_; 
if (v_isShared_5135_ == 0)
{
v___x_5137_ = v___x_5134_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5138_; 
v_reuseFailAlloc_5138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5138_, 0, v_a_5132_);
v___x_5137_ = v_reuseFailAlloc_5138_;
goto v_reusejp_5136_;
}
v_reusejp_5136_:
{
return v___x_5137_;
}
}
}
}
else
{
lean_object* v_a_5140_; lean_object* v___x_5142_; uint8_t v_isShared_5143_; uint8_t v_isSharedCheck_5147_; 
lean_dec_ref(v_b_5017_);
lean_dec_ref(v_a_5016_);
v_a_5140_ = lean_ctor_get(v___x_5030_, 0);
v_isSharedCheck_5147_ = !lean_is_exclusive(v___x_5030_);
if (v_isSharedCheck_5147_ == 0)
{
v___x_5142_ = v___x_5030_;
v_isShared_5143_ = v_isSharedCheck_5147_;
goto v_resetjp_5141_;
}
else
{
lean_inc(v_a_5140_);
lean_dec(v___x_5030_);
v___x_5142_ = lean_box(0);
v_isShared_5143_ = v_isSharedCheck_5147_;
goto v_resetjp_5141_;
}
v_resetjp_5141_:
{
lean_object* v___x_5145_; 
if (v_isShared_5143_ == 0)
{
v___x_5145_ = v___x_5142_;
goto v_reusejp_5144_;
}
else
{
lean_object* v_reuseFailAlloc_5146_; 
v_reuseFailAlloc_5146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5146_, 0, v_a_5140_);
v___x_5145_ = v_reuseFailAlloc_5146_;
goto v_reusejp_5144_;
}
v_reusejp_5144_:
{
return v___x_5145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq___boxed(lean_object* v_a_5148_, lean_object* v_b_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_){
_start:
{
lean_object* v_res_5162_; 
v_res_5162_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5148_, v_b_5149_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_);
lean_dec(v_a_5160_);
lean_dec_ref(v_a_5159_);
lean_dec(v_a_5158_);
lean_dec_ref(v_a_5157_);
lean_dec(v_a_5156_);
lean_dec_ref(v_a_5155_);
lean_dec(v_a_5154_);
lean_dec_ref(v_a_5153_);
lean_dec(v_a_5152_);
lean_dec(v_a_5151_);
lean_dec(v_a_5150_);
return v_res_5162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq(lean_object* v_a_5163_, lean_object* v_b_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_){
_start:
{
uint8_t v___x_5176_; 
v___x_5176_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_5163_, v_b_5164_);
if (v___x_5176_ == 0)
{
lean_object* v___x_5177_; 
v___x_5177_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5163_, v_b_5164_, v_a_5165_, v_a_5173_);
if (lean_obj_tag(v___x_5177_) == 0)
{
lean_object* v_a_5178_; 
v_a_5178_ = lean_ctor_get(v___x_5177_, 0);
lean_inc(v_a_5178_);
lean_dec_ref(v___x_5177_);
if (lean_obj_tag(v_a_5178_) == 1)
{
lean_object* v_val_5179_; lean_object* v___x_5180_; 
v_val_5179_ = lean_ctor_get(v_a_5178_, 0);
lean_inc(v_val_5179_);
lean_dec_ref(v_a_5178_);
v___x_5180_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_val_5179_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_);
if (lean_obj_tag(v___x_5180_) == 0)
{
lean_object* v_a_5181_; uint8_t v___x_5182_; 
v_a_5181_ = lean_ctor_get(v___x_5180_, 0);
lean_inc(v_a_5181_);
lean_dec_ref(v___x_5180_);
v___x_5182_ = lean_unbox(v_a_5181_);
lean_dec(v_a_5181_);
if (v___x_5182_ == 0)
{
lean_object* v___x_5183_; 
v___x_5183_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5179_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_);
if (lean_obj_tag(v___x_5183_) == 0)
{
lean_object* v_a_5184_; uint8_t v___x_5185_; 
v_a_5184_ = lean_ctor_get(v___x_5183_, 0);
lean_inc(v_a_5184_);
lean_dec_ref(v___x_5183_);
v___x_5185_ = lean_unbox(v_a_5184_);
lean_dec(v_a_5184_);
if (v___x_5185_ == 0)
{
lean_object* v___x_5186_; 
v___x_5186_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq(v_a_5163_, v_b_5164_, v_val_5179_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_);
lean_dec(v_val_5179_);
return v___x_5186_;
}
else
{
lean_object* v___x_5187_; 
lean_dec(v_val_5179_);
v___x_5187_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq___redArg(v_a_5163_, v_b_5164_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_);
return v___x_5187_;
}
}
else
{
lean_object* v_a_5188_; lean_object* v___x_5190_; uint8_t v_isShared_5191_; uint8_t v_isSharedCheck_5195_; 
lean_dec(v_val_5179_);
lean_dec_ref(v_b_5164_);
lean_dec_ref(v_a_5163_);
v_a_5188_ = lean_ctor_get(v___x_5183_, 0);
v_isSharedCheck_5195_ = !lean_is_exclusive(v___x_5183_);
if (v_isSharedCheck_5195_ == 0)
{
v___x_5190_ = v___x_5183_;
v_isShared_5191_ = v_isSharedCheck_5195_;
goto v_resetjp_5189_;
}
else
{
lean_inc(v_a_5188_);
lean_dec(v___x_5183_);
v___x_5190_ = lean_box(0);
v_isShared_5191_ = v_isSharedCheck_5195_;
goto v_resetjp_5189_;
}
v_resetjp_5189_:
{
lean_object* v___x_5193_; 
if (v_isShared_5191_ == 0)
{
v___x_5193_ = v___x_5190_;
goto v_reusejp_5192_;
}
else
{
lean_object* v_reuseFailAlloc_5194_; 
v_reuseFailAlloc_5194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5194_, 0, v_a_5188_);
v___x_5193_ = v_reuseFailAlloc_5194_;
goto v_reusejp_5192_;
}
v_reusejp_5192_:
{
return v___x_5193_;
}
}
}
}
else
{
lean_object* v___x_5196_; 
v___x_5196_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5179_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_);
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
v___x_5199_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleEq_x27(v_a_5163_, v_b_5164_, v_val_5179_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_);
lean_dec(v_val_5179_);
return v___x_5199_;
}
else
{
lean_object* v___x_5200_; 
v___x_5200_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingEq_x27(v_a_5163_, v_b_5164_, v_val_5179_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_);
lean_dec(v_val_5179_);
return v___x_5200_;
}
}
else
{
lean_object* v_a_5201_; lean_object* v___x_5203_; uint8_t v_isShared_5204_; uint8_t v_isSharedCheck_5208_; 
lean_dec(v_val_5179_);
lean_dec_ref(v_b_5164_);
lean_dec_ref(v_a_5163_);
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
}
else
{
lean_object* v_a_5209_; lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5216_; 
lean_dec(v_val_5179_);
lean_dec_ref(v_b_5164_);
lean_dec_ref(v_a_5163_);
v_a_5209_ = lean_ctor_get(v___x_5180_, 0);
v_isSharedCheck_5216_ = !lean_is_exclusive(v___x_5180_);
if (v_isSharedCheck_5216_ == 0)
{
v___x_5211_ = v___x_5180_;
v_isShared_5212_ = v_isSharedCheck_5216_;
goto v_resetjp_5210_;
}
else
{
lean_inc(v_a_5209_);
lean_dec(v___x_5180_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5216_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
lean_object* v___x_5214_; 
if (v_isShared_5212_ == 0)
{
v___x_5214_ = v___x_5211_;
goto v_reusejp_5213_;
}
else
{
lean_object* v_reuseFailAlloc_5215_; 
v_reuseFailAlloc_5215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5215_, 0, v_a_5209_);
v___x_5214_ = v_reuseFailAlloc_5215_;
goto v_reusejp_5213_;
}
v_reusejp_5213_:
{
return v___x_5214_;
}
}
}
}
else
{
lean_object* v___x_5217_; 
lean_dec(v_a_5178_);
v___x_5217_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5163_, v_b_5164_, v_a_5165_, v_a_5173_);
if (lean_obj_tag(v___x_5217_) == 0)
{
lean_object* v_a_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5240_; 
v_a_5218_ = lean_ctor_get(v___x_5217_, 0);
v_isSharedCheck_5240_ = !lean_is_exclusive(v___x_5217_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5220_ = v___x_5217_;
v_isShared_5221_ = v_isSharedCheck_5240_;
goto v_resetjp_5219_;
}
else
{
lean_inc(v_a_5218_);
lean_dec(v___x_5217_);
v___x_5220_ = lean_box(0);
v_isShared_5221_ = v_isSharedCheck_5240_;
goto v_resetjp_5219_;
}
v_resetjp_5219_:
{
if (lean_obj_tag(v_a_5218_) == 1)
{
lean_object* v_val_5222_; lean_object* v___x_5223_; 
lean_del_object(v___x_5220_);
v_val_5222_ = lean_ctor_get(v_a_5218_, 0);
lean_inc(v_val_5222_);
lean_dec_ref(v_a_5218_);
v___x_5223_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_val_5222_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_);
if (lean_obj_tag(v___x_5223_) == 0)
{
lean_object* v_a_5224_; lean_object* v_orderedAddInst_x3f_5225_; 
v_a_5224_ = lean_ctor_get(v___x_5223_, 0);
lean_inc(v_a_5224_);
lean_dec_ref(v___x_5223_);
v_orderedAddInst_x3f_5225_ = lean_ctor_get(v_a_5224_, 9);
lean_inc(v_orderedAddInst_x3f_5225_);
lean_dec(v_a_5224_);
if (lean_obj_tag(v_orderedAddInst_x3f_5225_) == 0)
{
lean_object* v___x_5226_; 
v___x_5226_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq(v_a_5163_, v_b_5164_, v_val_5222_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_);
lean_dec(v_val_5222_);
return v___x_5226_;
}
else
{
lean_object* v___x_5227_; 
lean_dec_ref(v_orderedAddInst_x3f_5225_);
v___x_5227_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleEq_x27(v_a_5163_, v_b_5164_, v_val_5222_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_);
lean_dec(v_val_5222_);
return v___x_5227_;
}
}
else
{
lean_object* v_a_5228_; lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5235_; 
lean_dec(v_val_5222_);
lean_dec_ref(v_b_5164_);
lean_dec_ref(v_a_5163_);
v_a_5228_ = lean_ctor_get(v___x_5223_, 0);
v_isSharedCheck_5235_ = !lean_is_exclusive(v___x_5223_);
if (v_isSharedCheck_5235_ == 0)
{
v___x_5230_ = v___x_5223_;
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
else
{
lean_inc(v_a_5228_);
lean_dec(v___x_5223_);
v___x_5230_ = lean_box(0);
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
v_resetjp_5229_:
{
lean_object* v___x_5233_; 
if (v_isShared_5231_ == 0)
{
v___x_5233_ = v___x_5230_;
goto v_reusejp_5232_;
}
else
{
lean_object* v_reuseFailAlloc_5234_; 
v_reuseFailAlloc_5234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5234_, 0, v_a_5228_);
v___x_5233_ = v_reuseFailAlloc_5234_;
goto v_reusejp_5232_;
}
v_reusejp_5232_:
{
return v___x_5233_;
}
}
}
}
else
{
lean_object* v___x_5236_; lean_object* v___x_5238_; 
lean_dec(v_a_5218_);
lean_dec_ref(v_b_5164_);
lean_dec_ref(v_a_5163_);
v___x_5236_ = lean_box(0);
if (v_isShared_5221_ == 0)
{
lean_ctor_set(v___x_5220_, 0, v___x_5236_);
v___x_5238_ = v___x_5220_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v___x_5236_);
v___x_5238_ = v_reuseFailAlloc_5239_;
goto v_reusejp_5237_;
}
v_reusejp_5237_:
{
return v___x_5238_;
}
}
}
}
else
{
lean_object* v_a_5241_; lean_object* v___x_5243_; uint8_t v_isShared_5244_; uint8_t v_isSharedCheck_5248_; 
lean_dec_ref(v_b_5164_);
lean_dec_ref(v_a_5163_);
v_a_5241_ = lean_ctor_get(v___x_5217_, 0);
v_isSharedCheck_5248_ = !lean_is_exclusive(v___x_5217_);
if (v_isSharedCheck_5248_ == 0)
{
v___x_5243_ = v___x_5217_;
v_isShared_5244_ = v_isSharedCheck_5248_;
goto v_resetjp_5242_;
}
else
{
lean_inc(v_a_5241_);
lean_dec(v___x_5217_);
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
}
else
{
lean_object* v_a_5249_; lean_object* v___x_5251_; uint8_t v_isShared_5252_; uint8_t v_isSharedCheck_5256_; 
lean_dec_ref(v_b_5164_);
lean_dec_ref(v_a_5163_);
v_a_5249_ = lean_ctor_get(v___x_5177_, 0);
v_isSharedCheck_5256_ = !lean_is_exclusive(v___x_5177_);
if (v_isSharedCheck_5256_ == 0)
{
v___x_5251_ = v___x_5177_;
v_isShared_5252_ = v_isSharedCheck_5256_;
goto v_resetjp_5250_;
}
else
{
lean_inc(v_a_5249_);
lean_dec(v___x_5177_);
v___x_5251_ = lean_box(0);
v_isShared_5252_ = v_isSharedCheck_5256_;
goto v_resetjp_5250_;
}
v_resetjp_5250_:
{
lean_object* v___x_5254_; 
if (v_isShared_5252_ == 0)
{
v___x_5254_ = v___x_5251_;
goto v_reusejp_5253_;
}
else
{
lean_object* v_reuseFailAlloc_5255_; 
v_reuseFailAlloc_5255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5255_, 0, v_a_5249_);
v___x_5254_ = v_reuseFailAlloc_5255_;
goto v_reusejp_5253_;
}
v_reusejp_5253_:
{
return v___x_5254_;
}
}
}
}
else
{
lean_object* v___x_5257_; lean_object* v___x_5258_; 
lean_dec_ref(v_b_5164_);
lean_dec_ref(v_a_5163_);
v___x_5257_ = lean_box(0);
v___x_5258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5258_, 0, v___x_5257_);
return v___x_5258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed(lean_object* v_a_5259_, lean_object* v_b_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_){
_start:
{
lean_object* v_res_5272_; 
v_res_5272_ = l_Lean_Meta_Grind_Arith_Linear_processNewEq(v_a_5259_, v_b_5260_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_);
lean_dec(v_a_5270_);
lean_dec_ref(v_a_5269_);
lean_dec(v_a_5268_);
lean_dec_ref(v_a_5267_);
lean_dec(v_a_5266_);
lean_dec_ref(v_a_5265_);
lean_dec(v_a_5264_);
lean_dec_ref(v_a_5263_);
lean_dec(v_a_5262_);
lean_dec(v_a_5261_);
return v_res_5272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(lean_object* v_a_5273_, lean_object* v_b_5274_, lean_object* v_a_5275_, lean_object* v_a_5276_, lean_object* v_a_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_, lean_object* v_a_5281_, lean_object* v_a_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_){
_start:
{
uint8_t v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; 
v___x_5287_ = 0;
v___x_5288_ = lean_unsigned_to_nat(0u);
v___x_5289_ = lean_box(v___x_5287_);
lean_inc_ref(v_a_5273_);
v___x_5290_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5290_, 0, v_a_5273_);
lean_closure_set(v___x_5290_, 1, v___x_5289_);
lean_closure_set(v___x_5290_, 2, v___x_5288_);
v___x_5291_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5290_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_, v_a_5285_);
if (lean_obj_tag(v___x_5291_) == 0)
{
lean_object* v_a_5292_; lean_object* v___x_5294_; uint8_t v_isShared_5295_; uint8_t v_isSharedCheck_5393_; 
v_a_5292_ = lean_ctor_get(v___x_5291_, 0);
v_isSharedCheck_5393_ = !lean_is_exclusive(v___x_5291_);
if (v_isSharedCheck_5393_ == 0)
{
v___x_5294_ = v___x_5291_;
v_isShared_5295_ = v_isSharedCheck_5393_;
goto v_resetjp_5293_;
}
else
{
lean_inc(v_a_5292_);
lean_dec(v___x_5291_);
v___x_5294_ = lean_box(0);
v_isShared_5295_ = v_isSharedCheck_5393_;
goto v_resetjp_5293_;
}
v_resetjp_5293_:
{
if (lean_obj_tag(v_a_5292_) == 1)
{
lean_object* v_val_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; 
lean_del_object(v___x_5294_);
v_val_5296_ = lean_ctor_get(v_a_5292_, 0);
lean_inc(v_val_5296_);
lean_dec_ref(v_a_5292_);
v___x_5297_ = lean_box(v___x_5287_);
lean_inc_ref(v_b_5274_);
v___x_5298_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_reify_x3f___boxed), 15, 3);
lean_closure_set(v___x_5298_, 0, v_b_5274_);
lean_closure_set(v___x_5298_, 1, v___x_5297_);
lean_closure_set(v___x_5298_, 2, v___x_5288_);
v___x_5299_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_5298_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_, v_a_5285_);
if (lean_obj_tag(v___x_5299_) == 0)
{
lean_object* v_a_5300_; lean_object* v___x_5302_; uint8_t v_isShared_5303_; uint8_t v_isSharedCheck_5380_; 
v_a_5300_ = lean_ctor_get(v___x_5299_, 0);
v_isSharedCheck_5380_ = !lean_is_exclusive(v___x_5299_);
if (v_isSharedCheck_5380_ == 0)
{
v___x_5302_ = v___x_5299_;
v_isShared_5303_ = v_isSharedCheck_5380_;
goto v_resetjp_5301_;
}
else
{
lean_inc(v_a_5300_);
lean_dec(v___x_5299_);
v___x_5302_ = lean_box(0);
v_isShared_5303_ = v_isSharedCheck_5380_;
goto v_resetjp_5301_;
}
v_resetjp_5301_:
{
if (lean_obj_tag(v_a_5300_) == 1)
{
lean_object* v_val_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; 
lean_del_object(v___x_5302_);
v_val_5304_ = lean_ctor_get(v_a_5300_, 0);
lean_inc_n(v_val_5304_, 2);
lean_dec_ref(v_a_5300_);
lean_inc(v_val_5296_);
v___x_5305_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_5305_, 0, v_val_5296_);
lean_ctor_set(v___x_5305_, 1, v_val_5304_);
v___x_5306_ = l_Lean_Grind_CommRing_Expr_toPoly(v___x_5305_);
lean_inc_ref(v_b_5274_);
lean_inc_ref(v_a_5273_);
v___x_5307_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5307_, 0, v_a_5273_);
lean_ctor_set(v___x_5307_, 1, v_b_5274_);
lean_ctor_set(v___x_5307_, 2, v_val_5296_);
lean_ctor_set(v___x_5307_, 3, v_val_5304_);
v___x_5308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5308_, 0, v___x_5306_);
lean_ctor_set(v___x_5308_, 1, v___x_5307_);
v___x_5309_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(v___x_5308_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_, v_a_5285_);
if (lean_obj_tag(v___x_5309_) == 0)
{
lean_object* v_a_5310_; lean_object* v___x_5311_; 
v_a_5310_ = lean_ctor_get(v___x_5309_, 0);
lean_inc(v_a_5310_);
lean_dec_ref(v___x_5309_);
v___x_5311_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5273_, v_a_5276_);
lean_dec_ref(v_a_5273_);
if (lean_obj_tag(v___x_5311_) == 0)
{
lean_object* v_a_5312_; lean_object* v___x_5313_; 
v_a_5312_ = lean_ctor_get(v___x_5311_, 0);
lean_inc(v_a_5312_);
lean_dec_ref(v___x_5311_);
v___x_5313_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5274_, v_a_5276_);
lean_dec_ref(v_b_5274_);
if (lean_obj_tag(v___x_5313_) == 0)
{
lean_object* v_a_5314_; lean_object* v_p_5315_; lean_object* v___y_5317_; uint8_t v___x_5351_; 
v_a_5314_ = lean_ctor_get(v___x_5313_, 0);
lean_inc(v_a_5314_);
lean_dec_ref(v___x_5313_);
v_p_5315_ = lean_ctor_get(v_a_5310_, 0);
v___x_5351_ = lean_nat_dec_le(v_a_5312_, v_a_5314_);
if (v___x_5351_ == 0)
{
lean_dec(v_a_5314_);
v___y_5317_ = v_a_5312_;
goto v___jp_5316_;
}
else
{
lean_dec(v_a_5312_);
v___y_5317_ = v_a_5314_;
goto v___jp_5316_;
}
v___jp_5316_:
{
lean_object* v___x_5318_; 
lean_inc(v___y_5317_);
lean_inc_ref(v_p_5315_);
v___x_5318_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(v_p_5315_, v___y_5317_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_, v_a_5285_);
if (lean_obj_tag(v___x_5318_) == 0)
{
lean_object* v_a_5319_; lean_object* v___x_5320_; 
v_a_5319_ = lean_ctor_get(v___x_5318_, 0);
lean_inc(v_a_5319_);
lean_dec_ref(v___x_5318_);
v___x_5320_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5319_, v___x_5287_, v___y_5317_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_, v_a_5285_);
if (lean_obj_tag(v___x_5320_) == 0)
{
lean_object* v_a_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5334_; 
v_a_5321_ = lean_ctor_get(v___x_5320_, 0);
v_isSharedCheck_5334_ = !lean_is_exclusive(v___x_5320_);
if (v_isSharedCheck_5334_ == 0)
{
v___x_5323_ = v___x_5320_;
v_isShared_5324_ = v_isSharedCheck_5334_;
goto v_resetjp_5322_;
}
else
{
lean_inc(v_a_5321_);
lean_dec(v___x_5320_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5334_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
if (lean_obj_tag(v_a_5321_) == 1)
{
lean_object* v_val_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; 
lean_del_object(v___x_5323_);
v_val_5325_ = lean_ctor_get(v_a_5321_, 0);
lean_inc_n(v_val_5325_, 2);
lean_dec_ref(v_a_5321_);
v___x_5326_ = l_Lean_Grind_Linarith_Expr_norm(v_val_5325_);
v___x_5327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5327_, 0, v_a_5310_);
lean_ctor_set(v___x_5327_, 1, v_val_5325_);
v___x_5328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5328_, 0, v___x_5326_);
lean_ctor_set(v___x_5328_, 1, v___x_5327_);
v___x_5329_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5328_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_, v_a_5285_);
return v___x_5329_;
}
else
{
lean_object* v___x_5330_; lean_object* v___x_5332_; 
lean_dec(v_a_5321_);
lean_dec(v_a_5310_);
v___x_5330_ = lean_box(0);
if (v_isShared_5324_ == 0)
{
lean_ctor_set(v___x_5323_, 0, v___x_5330_);
v___x_5332_ = v___x_5323_;
goto v_reusejp_5331_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v___x_5330_);
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
lean_dec(v_a_5310_);
v_a_5335_ = lean_ctor_get(v___x_5320_, 0);
v_isSharedCheck_5342_ = !lean_is_exclusive(v___x_5320_);
if (v_isSharedCheck_5342_ == 0)
{
v___x_5337_ = v___x_5320_;
v_isShared_5338_ = v_isSharedCheck_5342_;
goto v_resetjp_5336_;
}
else
{
lean_inc(v_a_5335_);
lean_dec(v___x_5320_);
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
lean_object* v_a_5343_; lean_object* v___x_5345_; uint8_t v_isShared_5346_; uint8_t v_isSharedCheck_5350_; 
lean_dec(v___y_5317_);
lean_dec(v_a_5310_);
v_a_5343_ = lean_ctor_get(v___x_5318_, 0);
v_isSharedCheck_5350_ = !lean_is_exclusive(v___x_5318_);
if (v_isSharedCheck_5350_ == 0)
{
v___x_5345_ = v___x_5318_;
v_isShared_5346_ = v_isSharedCheck_5350_;
goto v_resetjp_5344_;
}
else
{
lean_inc(v_a_5343_);
lean_dec(v___x_5318_);
v___x_5345_ = lean_box(0);
v_isShared_5346_ = v_isSharedCheck_5350_;
goto v_resetjp_5344_;
}
v_resetjp_5344_:
{
lean_object* v___x_5348_; 
if (v_isShared_5346_ == 0)
{
v___x_5348_ = v___x_5345_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5349_; 
v_reuseFailAlloc_5349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_a_5343_);
v___x_5348_ = v_reuseFailAlloc_5349_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
return v___x_5348_;
}
}
}
}
}
else
{
lean_object* v_a_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5359_; 
lean_dec(v_a_5312_);
lean_dec(v_a_5310_);
v_a_5352_ = lean_ctor_get(v___x_5313_, 0);
v_isSharedCheck_5359_ = !lean_is_exclusive(v___x_5313_);
if (v_isSharedCheck_5359_ == 0)
{
v___x_5354_ = v___x_5313_;
v_isShared_5355_ = v_isSharedCheck_5359_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_a_5352_);
lean_dec(v___x_5313_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5359_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
lean_object* v___x_5357_; 
if (v_isShared_5355_ == 0)
{
v___x_5357_ = v___x_5354_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5358_; 
v_reuseFailAlloc_5358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5358_, 0, v_a_5352_);
v___x_5357_ = v_reuseFailAlloc_5358_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
return v___x_5357_;
}
}
}
}
else
{
lean_object* v_a_5360_; lean_object* v___x_5362_; uint8_t v_isShared_5363_; uint8_t v_isSharedCheck_5367_; 
lean_dec(v_a_5310_);
lean_dec_ref(v_b_5274_);
v_a_5360_ = lean_ctor_get(v___x_5311_, 0);
v_isSharedCheck_5367_ = !lean_is_exclusive(v___x_5311_);
if (v_isSharedCheck_5367_ == 0)
{
v___x_5362_ = v___x_5311_;
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
else
{
lean_inc(v_a_5360_);
lean_dec(v___x_5311_);
v___x_5362_ = lean_box(0);
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
v_resetjp_5361_:
{
lean_object* v___x_5365_; 
if (v_isShared_5363_ == 0)
{
v___x_5365_ = v___x_5362_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_a_5360_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
}
}
else
{
lean_object* v_a_5368_; lean_object* v___x_5370_; uint8_t v_isShared_5371_; uint8_t v_isSharedCheck_5375_; 
lean_dec_ref(v_b_5274_);
lean_dec_ref(v_a_5273_);
v_a_5368_ = lean_ctor_get(v___x_5309_, 0);
v_isSharedCheck_5375_ = !lean_is_exclusive(v___x_5309_);
if (v_isSharedCheck_5375_ == 0)
{
v___x_5370_ = v___x_5309_;
v_isShared_5371_ = v_isSharedCheck_5375_;
goto v_resetjp_5369_;
}
else
{
lean_inc(v_a_5368_);
lean_dec(v___x_5309_);
v___x_5370_ = lean_box(0);
v_isShared_5371_ = v_isSharedCheck_5375_;
goto v_resetjp_5369_;
}
v_resetjp_5369_:
{
lean_object* v___x_5373_; 
if (v_isShared_5371_ == 0)
{
v___x_5373_ = v___x_5370_;
goto v_reusejp_5372_;
}
else
{
lean_object* v_reuseFailAlloc_5374_; 
v_reuseFailAlloc_5374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5374_, 0, v_a_5368_);
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
lean_object* v___x_5376_; lean_object* v___x_5378_; 
lean_dec(v_a_5300_);
lean_dec(v_val_5296_);
lean_dec_ref(v_b_5274_);
lean_dec_ref(v_a_5273_);
v___x_5376_ = lean_box(0);
if (v_isShared_5303_ == 0)
{
lean_ctor_set(v___x_5302_, 0, v___x_5376_);
v___x_5378_ = v___x_5302_;
goto v_reusejp_5377_;
}
else
{
lean_object* v_reuseFailAlloc_5379_; 
v_reuseFailAlloc_5379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5379_, 0, v___x_5376_);
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
lean_dec(v_val_5296_);
lean_dec_ref(v_b_5274_);
lean_dec_ref(v_a_5273_);
v_a_5381_ = lean_ctor_get(v___x_5299_, 0);
v_isSharedCheck_5388_ = !lean_is_exclusive(v___x_5299_);
if (v_isSharedCheck_5388_ == 0)
{
v___x_5383_ = v___x_5299_;
v_isShared_5384_ = v_isSharedCheck_5388_;
goto v_resetjp_5382_;
}
else
{
lean_inc(v_a_5381_);
lean_dec(v___x_5299_);
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
lean_dec(v_a_5292_);
lean_dec_ref(v_b_5274_);
lean_dec_ref(v_a_5273_);
v___x_5389_ = lean_box(0);
if (v_isShared_5295_ == 0)
{
lean_ctor_set(v___x_5294_, 0, v___x_5389_);
v___x_5391_ = v___x_5294_;
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
lean_dec_ref(v_b_5274_);
lean_dec_ref(v_a_5273_);
v_a_5394_ = lean_ctor_get(v___x_5291_, 0);
v_isSharedCheck_5401_ = !lean_is_exclusive(v___x_5291_);
if (v_isSharedCheck_5401_ == 0)
{
v___x_5396_ = v___x_5291_;
v_isShared_5397_ = v_isSharedCheck_5401_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_a_5394_);
lean_dec(v___x_5291_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq___boxed(lean_object* v_a_5402_, lean_object* v_b_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_){
_start:
{
lean_object* v_res_5416_; 
v_res_5416_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5402_, v_b_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_, v_a_5414_);
lean_dec(v_a_5414_);
lean_dec_ref(v_a_5413_);
lean_dec(v_a_5412_);
lean_dec_ref(v_a_5411_);
lean_dec(v_a_5410_);
lean_dec_ref(v_a_5409_);
lean_dec(v_a_5408_);
lean_dec_ref(v_a_5407_);
lean_dec(v_a_5406_);
lean_dec(v_a_5405_);
lean_dec(v_a_5404_);
return v_res_5416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(lean_object* v_a_5417_, lean_object* v_b_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_, lean_object* v_a_5424_, lean_object* v_a_5425_, lean_object* v_a_5426_, lean_object* v_a_5427_, lean_object* v_a_5428_, lean_object* v_a_5429_){
_start:
{
lean_object* v___x_5431_; 
v___x_5431_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5417_, v_a_5420_);
if (lean_obj_tag(v___x_5431_) == 0)
{
lean_object* v_a_5432_; uint8_t v___x_5433_; lean_object* v___x_5434_; 
v_a_5432_ = lean_ctor_get(v___x_5431_, 0);
lean_inc(v_a_5432_);
lean_dec_ref(v___x_5431_);
v___x_5433_ = 0;
lean_inc_ref(v_a_5417_);
v___x_5434_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_a_5417_, v___x_5433_, v_a_5432_, v_a_5419_, v_a_5420_, v_a_5421_, v_a_5422_, v_a_5423_, v_a_5424_, v_a_5425_, v_a_5426_, v_a_5427_, v_a_5428_, v_a_5429_);
if (lean_obj_tag(v___x_5434_) == 0)
{
lean_object* v_a_5435_; lean_object* v___x_5437_; uint8_t v_isShared_5438_; uint8_t v_isSharedCheck_5478_; 
v_a_5435_ = lean_ctor_get(v___x_5434_, 0);
v_isSharedCheck_5478_ = !lean_is_exclusive(v___x_5434_);
if (v_isSharedCheck_5478_ == 0)
{
v___x_5437_ = v___x_5434_;
v_isShared_5438_ = v_isSharedCheck_5478_;
goto v_resetjp_5436_;
}
else
{
lean_inc(v_a_5435_);
lean_dec(v___x_5434_);
v___x_5437_ = lean_box(0);
v_isShared_5438_ = v_isSharedCheck_5478_;
goto v_resetjp_5436_;
}
v_resetjp_5436_:
{
if (lean_obj_tag(v_a_5435_) == 1)
{
lean_object* v_val_5439_; lean_object* v___x_5440_; 
lean_del_object(v___x_5437_);
v_val_5439_ = lean_ctor_get(v_a_5435_, 0);
lean_inc(v_val_5439_);
lean_dec_ref(v_a_5435_);
v___x_5440_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5418_, v_a_5420_);
if (lean_obj_tag(v___x_5440_) == 0)
{
lean_object* v_a_5441_; lean_object* v___x_5442_; 
v_a_5441_ = lean_ctor_get(v___x_5440_, 0);
lean_inc(v_a_5441_);
lean_dec_ref(v___x_5440_);
lean_inc_ref(v_b_5418_);
v___x_5442_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_b_5418_, v___x_5433_, v_a_5441_, v_a_5419_, v_a_5420_, v_a_5421_, v_a_5422_, v_a_5423_, v_a_5424_, v_a_5425_, v_a_5426_, v_a_5427_, v_a_5428_, v_a_5429_);
if (lean_obj_tag(v___x_5442_) == 0)
{
lean_object* v_a_5443_; lean_object* v___x_5445_; uint8_t v_isShared_5446_; uint8_t v_isSharedCheck_5457_; 
v_a_5443_ = lean_ctor_get(v___x_5442_, 0);
v_isSharedCheck_5457_ = !lean_is_exclusive(v___x_5442_);
if (v_isSharedCheck_5457_ == 0)
{
v___x_5445_ = v___x_5442_;
v_isShared_5446_ = v_isSharedCheck_5457_;
goto v_resetjp_5444_;
}
else
{
lean_inc(v_a_5443_);
lean_dec(v___x_5442_);
v___x_5445_ = lean_box(0);
v_isShared_5446_ = v_isSharedCheck_5457_;
goto v_resetjp_5444_;
}
v_resetjp_5444_:
{
if (lean_obj_tag(v_a_5443_) == 1)
{
lean_object* v_val_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; 
lean_del_object(v___x_5445_);
v_val_5447_ = lean_ctor_get(v_a_5443_, 0);
lean_inc_n(v_val_5447_, 2);
lean_dec_ref(v_a_5443_);
lean_inc(v_val_5439_);
v___x_5448_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5448_, 0, v_val_5439_);
lean_ctor_set(v___x_5448_, 1, v_val_5447_);
v___x_5449_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5448_);
v___x_5450_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5450_, 0, v_a_5417_);
lean_ctor_set(v___x_5450_, 1, v_b_5418_);
lean_ctor_set(v___x_5450_, 2, v_val_5439_);
lean_ctor_set(v___x_5450_, 3, v_val_5447_);
v___x_5451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5451_, 0, v___x_5449_);
lean_ctor_set(v___x_5451_, 1, v___x_5450_);
v___x_5452_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5451_, v_a_5419_, v_a_5420_, v_a_5421_, v_a_5422_, v_a_5423_, v_a_5424_, v_a_5425_, v_a_5426_, v_a_5427_, v_a_5428_, v_a_5429_);
return v___x_5452_;
}
else
{
lean_object* v___x_5453_; lean_object* v___x_5455_; 
lean_dec(v_a_5443_);
lean_dec(v_val_5439_);
lean_dec_ref(v_b_5418_);
lean_dec_ref(v_a_5417_);
v___x_5453_ = lean_box(0);
if (v_isShared_5446_ == 0)
{
lean_ctor_set(v___x_5445_, 0, v___x_5453_);
v___x_5455_ = v___x_5445_;
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
lean_dec(v_val_5439_);
lean_dec_ref(v_b_5418_);
lean_dec_ref(v_a_5417_);
v_a_5458_ = lean_ctor_get(v___x_5442_, 0);
v_isSharedCheck_5465_ = !lean_is_exclusive(v___x_5442_);
if (v_isSharedCheck_5465_ == 0)
{
v___x_5460_ = v___x_5442_;
v_isShared_5461_ = v_isSharedCheck_5465_;
goto v_resetjp_5459_;
}
else
{
lean_inc(v_a_5458_);
lean_dec(v___x_5442_);
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
lean_object* v_a_5466_; lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5473_; 
lean_dec(v_val_5439_);
lean_dec_ref(v_b_5418_);
lean_dec_ref(v_a_5417_);
v_a_5466_ = lean_ctor_get(v___x_5440_, 0);
v_isSharedCheck_5473_ = !lean_is_exclusive(v___x_5440_);
if (v_isSharedCheck_5473_ == 0)
{
v___x_5468_ = v___x_5440_;
v_isShared_5469_ = v_isSharedCheck_5473_;
goto v_resetjp_5467_;
}
else
{
lean_inc(v_a_5466_);
lean_dec(v___x_5440_);
v___x_5468_ = lean_box(0);
v_isShared_5469_ = v_isSharedCheck_5473_;
goto v_resetjp_5467_;
}
v_resetjp_5467_:
{
lean_object* v___x_5471_; 
if (v_isShared_5469_ == 0)
{
v___x_5471_ = v___x_5468_;
goto v_reusejp_5470_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v_a_5466_);
v___x_5471_ = v_reuseFailAlloc_5472_;
goto v_reusejp_5470_;
}
v_reusejp_5470_:
{
return v___x_5471_;
}
}
}
}
else
{
lean_object* v___x_5474_; lean_object* v___x_5476_; 
lean_dec(v_a_5435_);
lean_dec_ref(v_b_5418_);
lean_dec_ref(v_a_5417_);
v___x_5474_ = lean_box(0);
if (v_isShared_5438_ == 0)
{
lean_ctor_set(v___x_5437_, 0, v___x_5474_);
v___x_5476_ = v___x_5437_;
goto v_reusejp_5475_;
}
else
{
lean_object* v_reuseFailAlloc_5477_; 
v_reuseFailAlloc_5477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5477_, 0, v___x_5474_);
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
lean_dec_ref(v_b_5418_);
lean_dec_ref(v_a_5417_);
v_a_5479_ = lean_ctor_get(v___x_5434_, 0);
v_isSharedCheck_5486_ = !lean_is_exclusive(v___x_5434_);
if (v_isSharedCheck_5486_ == 0)
{
v___x_5481_ = v___x_5434_;
v_isShared_5482_ = v_isSharedCheck_5486_;
goto v_resetjp_5480_;
}
else
{
lean_inc(v_a_5479_);
lean_dec(v___x_5434_);
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
lean_object* v_a_5487_; lean_object* v___x_5489_; uint8_t v_isShared_5490_; uint8_t v_isSharedCheck_5494_; 
lean_dec_ref(v_b_5418_);
lean_dec_ref(v_a_5417_);
v_a_5487_ = lean_ctor_get(v___x_5431_, 0);
v_isSharedCheck_5494_ = !lean_is_exclusive(v___x_5431_);
if (v_isSharedCheck_5494_ == 0)
{
v___x_5489_ = v___x_5431_;
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
else
{
lean_inc(v_a_5487_);
lean_dec(v___x_5431_);
v___x_5489_ = lean_box(0);
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
v_resetjp_5488_:
{
lean_object* v___x_5492_; 
if (v_isShared_5490_ == 0)
{
v___x_5492_ = v___x_5489_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_a_5487_);
v___x_5492_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
return v___x_5492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq___boxed(lean_object* v_a_5495_, lean_object* v_b_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_, lean_object* v_a_5502_, lean_object* v_a_5503_, lean_object* v_a_5504_, lean_object* v_a_5505_, lean_object* v_a_5506_, lean_object* v_a_5507_, lean_object* v_a_5508_){
_start:
{
lean_object* v_res_5509_; 
v_res_5509_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5495_, v_b_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_);
lean_dec(v_a_5507_);
lean_dec_ref(v_a_5506_);
lean_dec(v_a_5505_);
lean_dec_ref(v_a_5504_);
lean_dec(v_a_5503_);
lean_dec_ref(v_a_5502_);
lean_dec(v_a_5501_);
lean_dec_ref(v_a_5500_);
lean_dec(v_a_5499_);
lean_dec(v_a_5498_);
lean_dec(v_a_5497_);
return v_res_5509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(lean_object* v_a_5510_, lean_object* v_b_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_, lean_object* v_a_5516_, lean_object* v_a_5517_, lean_object* v_a_5518_, lean_object* v_a_5519_, lean_object* v_a_5520_, lean_object* v_a_5521_, lean_object* v_a_5522_){
_start:
{
lean_object* v___x_5524_; 
v___x_5524_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_, v_a_5518_, v_a_5519_, v_a_5520_, v_a_5521_, v_a_5522_);
if (lean_obj_tag(v___x_5524_) == 0)
{
lean_object* v_a_5525_; lean_object* v_addRightCancelInst_x3f_5526_; 
v_a_5525_ = lean_ctor_get(v___x_5524_, 0);
lean_inc(v_a_5525_);
lean_dec_ref(v___x_5524_);
v_addRightCancelInst_x3f_5526_ = lean_ctor_get(v_a_5525_, 11);
if (lean_obj_tag(v_addRightCancelInst_x3f_5526_) == 0)
{
lean_object* v___x_5527_; 
lean_dec(v_a_5525_);
v___x_5527_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(v_a_5510_, v_b_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_, v_a_5518_, v_a_5519_, v_a_5520_, v_a_5521_, v_a_5522_);
return v___x_5527_;
}
else
{
lean_object* v_id_5528_; lean_object* v_structId_5529_; lean_object* v___x_5530_; 
v_id_5528_ = lean_ctor_get(v_a_5525_, 0);
lean_inc(v_id_5528_);
v_structId_5529_ = lean_ctor_get(v_a_5525_, 1);
lean_inc(v_structId_5529_);
lean_dec(v_a_5525_);
lean_inc_ref(v_a_5510_);
v___x_5530_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_a_5510_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_, v_a_5518_, v_a_5519_, v_a_5520_, v_a_5521_, v_a_5522_);
if (lean_obj_tag(v___x_5530_) == 0)
{
lean_object* v_a_5531_; lean_object* v_fst_5532_; lean_object* v___x_5534_; uint8_t v_isShared_5535_; uint8_t v_isSharedCheck_5620_; 
v_a_5531_ = lean_ctor_get(v___x_5530_, 0);
lean_inc(v_a_5531_);
lean_dec_ref(v___x_5530_);
v_fst_5532_ = lean_ctor_get(v_a_5531_, 0);
v_isSharedCheck_5620_ = !lean_is_exclusive(v_a_5531_);
if (v_isSharedCheck_5620_ == 0)
{
lean_object* v_unused_5621_; 
v_unused_5621_ = lean_ctor_get(v_a_5531_, 1);
lean_dec(v_unused_5621_);
v___x_5534_ = v_a_5531_;
v_isShared_5535_ = v_isSharedCheck_5620_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_fst_5532_);
lean_dec(v_a_5531_);
v___x_5534_ = lean_box(0);
v_isShared_5535_ = v_isSharedCheck_5620_;
goto v_resetjp_5533_;
}
v_resetjp_5533_:
{
lean_object* v___x_5536_; 
lean_inc_ref(v_b_5511_);
v___x_5536_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_b_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_, v_a_5518_, v_a_5519_, v_a_5520_, v_a_5521_, v_a_5522_);
if (lean_obj_tag(v___x_5536_) == 0)
{
lean_object* v_a_5537_; lean_object* v_fst_5538_; lean_object* v___x_5540_; uint8_t v_isShared_5541_; uint8_t v_isSharedCheck_5610_; 
v_a_5537_ = lean_ctor_get(v___x_5536_, 0);
lean_inc(v_a_5537_);
lean_dec_ref(v___x_5536_);
v_fst_5538_ = lean_ctor_get(v_a_5537_, 0);
v_isSharedCheck_5610_ = !lean_is_exclusive(v_a_5537_);
if (v_isSharedCheck_5610_ == 0)
{
lean_object* v_unused_5611_; 
v_unused_5611_ = lean_ctor_get(v_a_5537_, 1);
lean_dec(v_unused_5611_);
v___x_5540_ = v_a_5537_;
v_isShared_5541_ = v_isSharedCheck_5610_;
goto v_resetjp_5539_;
}
else
{
lean_inc(v_fst_5538_);
lean_dec(v_a_5537_);
v___x_5540_ = lean_box(0);
v_isShared_5541_ = v_isSharedCheck_5610_;
goto v_resetjp_5539_;
}
v_resetjp_5539_:
{
lean_object* v___x_5542_; 
v___x_5542_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_5510_, v_a_5513_);
if (lean_obj_tag(v___x_5542_) == 0)
{
lean_object* v_a_5543_; uint8_t v___x_5544_; lean_object* v___x_5545_; 
v_a_5543_ = lean_ctor_get(v___x_5542_, 0);
lean_inc(v_a_5543_);
lean_dec_ref(v___x_5542_);
v___x_5544_ = 0;
v___x_5545_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5532_, v___x_5544_, v_a_5543_, v_structId_5529_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_, v_a_5518_, v_a_5519_, v_a_5520_, v_a_5521_, v_a_5522_);
if (lean_obj_tag(v___x_5545_) == 0)
{
lean_object* v_a_5546_; lean_object* v___x_5548_; uint8_t v_isShared_5549_; uint8_t v_isSharedCheck_5593_; 
v_a_5546_ = lean_ctor_get(v___x_5545_, 0);
v_isSharedCheck_5593_ = !lean_is_exclusive(v___x_5545_);
if (v_isSharedCheck_5593_ == 0)
{
v___x_5548_ = v___x_5545_;
v_isShared_5549_ = v_isSharedCheck_5593_;
goto v_resetjp_5547_;
}
else
{
lean_inc(v_a_5546_);
lean_dec(v___x_5545_);
v___x_5548_ = lean_box(0);
v_isShared_5549_ = v_isSharedCheck_5593_;
goto v_resetjp_5547_;
}
v_resetjp_5547_:
{
if (lean_obj_tag(v_a_5546_) == 1)
{
lean_object* v_val_5550_; lean_object* v___x_5551_; 
lean_del_object(v___x_5548_);
v_val_5550_ = lean_ctor_get(v_a_5546_, 0);
lean_inc(v_val_5550_);
lean_dec_ref(v_a_5546_);
v___x_5551_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_5511_, v_a_5513_);
if (lean_obj_tag(v___x_5551_) == 0)
{
lean_object* v_a_5552_; lean_object* v___x_5553_; 
v_a_5552_ = lean_ctor_get(v___x_5551_, 0);
lean_inc(v_a_5552_);
lean_dec_ref(v___x_5551_);
v___x_5553_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(v_fst_5538_, v___x_5544_, v_a_5552_, v_structId_5529_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_, v_a_5518_, v_a_5519_, v_a_5520_, v_a_5521_, v_a_5522_);
if (lean_obj_tag(v___x_5553_) == 0)
{
lean_object* v_a_5554_; lean_object* v___x_5556_; uint8_t v_isShared_5557_; uint8_t v_isSharedCheck_5572_; 
v_a_5554_ = lean_ctor_get(v___x_5553_, 0);
v_isSharedCheck_5572_ = !lean_is_exclusive(v___x_5553_);
if (v_isSharedCheck_5572_ == 0)
{
v___x_5556_ = v___x_5553_;
v_isShared_5557_ = v_isSharedCheck_5572_;
goto v_resetjp_5555_;
}
else
{
lean_inc(v_a_5554_);
lean_dec(v___x_5553_);
v___x_5556_ = lean_box(0);
v_isShared_5557_ = v_isSharedCheck_5572_;
goto v_resetjp_5555_;
}
v_resetjp_5555_:
{
if (lean_obj_tag(v_a_5554_) == 1)
{
lean_object* v_val_5558_; lean_object* v___x_5560_; 
lean_del_object(v___x_5556_);
v_val_5558_ = lean_ctor_get(v_a_5554_, 0);
lean_inc_n(v_val_5558_, 2);
lean_dec_ref(v_a_5554_);
lean_inc(v_val_5550_);
if (v_isShared_5541_ == 0)
{
lean_ctor_set_tag(v___x_5540_, 3);
lean_ctor_set(v___x_5540_, 1, v_val_5558_);
lean_ctor_set(v___x_5540_, 0, v_val_5550_);
v___x_5560_ = v___x_5540_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5567_; 
v_reuseFailAlloc_5567_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5567_, 0, v_val_5550_);
lean_ctor_set(v_reuseFailAlloc_5567_, 1, v_val_5558_);
v___x_5560_ = v_reuseFailAlloc_5567_;
goto v_reusejp_5559_;
}
v_reusejp_5559_:
{
lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5564_; 
v___x_5561_ = l_Lean_Grind_Linarith_Expr_norm(v___x_5560_);
v___x_5562_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_5562_, 0, v_a_5510_);
lean_ctor_set(v___x_5562_, 1, v_b_5511_);
lean_ctor_set(v___x_5562_, 2, v_id_5528_);
lean_ctor_set(v___x_5562_, 3, v_val_5550_);
lean_ctor_set(v___x_5562_, 4, v_val_5558_);
if (v_isShared_5535_ == 0)
{
lean_ctor_set(v___x_5534_, 1, v___x_5562_);
lean_ctor_set(v___x_5534_, 0, v___x_5561_);
v___x_5564_ = v___x_5534_;
goto v_reusejp_5563_;
}
else
{
lean_object* v_reuseFailAlloc_5566_; 
v_reuseFailAlloc_5566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5566_, 0, v___x_5561_);
lean_ctor_set(v_reuseFailAlloc_5566_, 1, v___x_5562_);
v___x_5564_ = v_reuseFailAlloc_5566_;
goto v_reusejp_5563_;
}
v_reusejp_5563_:
{
lean_object* v___x_5565_; 
v___x_5565_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_DiseqCnstr_assert(v___x_5564_, v_structId_5529_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_, v_a_5518_, v_a_5519_, v_a_5520_, v_a_5521_, v_a_5522_);
lean_dec(v_structId_5529_);
return v___x_5565_;
}
}
}
else
{
lean_object* v___x_5568_; lean_object* v___x_5570_; 
lean_dec(v_a_5554_);
lean_dec(v_val_5550_);
lean_del_object(v___x_5540_);
lean_del_object(v___x_5534_);
lean_dec(v_structId_5529_);
lean_dec(v_id_5528_);
lean_dec_ref(v_b_5511_);
lean_dec_ref(v_a_5510_);
v___x_5568_ = lean_box(0);
if (v_isShared_5557_ == 0)
{
lean_ctor_set(v___x_5556_, 0, v___x_5568_);
v___x_5570_ = v___x_5556_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v___x_5568_);
v___x_5570_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
return v___x_5570_;
}
}
}
}
else
{
lean_object* v_a_5573_; lean_object* v___x_5575_; uint8_t v_isShared_5576_; uint8_t v_isSharedCheck_5580_; 
lean_dec(v_val_5550_);
lean_del_object(v___x_5540_);
lean_del_object(v___x_5534_);
lean_dec(v_structId_5529_);
lean_dec(v_id_5528_);
lean_dec_ref(v_b_5511_);
lean_dec_ref(v_a_5510_);
v_a_5573_ = lean_ctor_get(v___x_5553_, 0);
v_isSharedCheck_5580_ = !lean_is_exclusive(v___x_5553_);
if (v_isSharedCheck_5580_ == 0)
{
v___x_5575_ = v___x_5553_;
v_isShared_5576_ = v_isSharedCheck_5580_;
goto v_resetjp_5574_;
}
else
{
lean_inc(v_a_5573_);
lean_dec(v___x_5553_);
v___x_5575_ = lean_box(0);
v_isShared_5576_ = v_isSharedCheck_5580_;
goto v_resetjp_5574_;
}
v_resetjp_5574_:
{
lean_object* v___x_5578_; 
if (v_isShared_5576_ == 0)
{
v___x_5578_ = v___x_5575_;
goto v_reusejp_5577_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v_a_5573_);
v___x_5578_ = v_reuseFailAlloc_5579_;
goto v_reusejp_5577_;
}
v_reusejp_5577_:
{
return v___x_5578_;
}
}
}
}
else
{
lean_object* v_a_5581_; lean_object* v___x_5583_; uint8_t v_isShared_5584_; uint8_t v_isSharedCheck_5588_; 
lean_dec(v_val_5550_);
lean_del_object(v___x_5540_);
lean_dec(v_fst_5538_);
lean_del_object(v___x_5534_);
lean_dec(v_structId_5529_);
lean_dec(v_id_5528_);
lean_dec_ref(v_b_5511_);
lean_dec_ref(v_a_5510_);
v_a_5581_ = lean_ctor_get(v___x_5551_, 0);
v_isSharedCheck_5588_ = !lean_is_exclusive(v___x_5551_);
if (v_isSharedCheck_5588_ == 0)
{
v___x_5583_ = v___x_5551_;
v_isShared_5584_ = v_isSharedCheck_5588_;
goto v_resetjp_5582_;
}
else
{
lean_inc(v_a_5581_);
lean_dec(v___x_5551_);
v___x_5583_ = lean_box(0);
v_isShared_5584_ = v_isSharedCheck_5588_;
goto v_resetjp_5582_;
}
v_resetjp_5582_:
{
lean_object* v___x_5586_; 
if (v_isShared_5584_ == 0)
{
v___x_5586_ = v___x_5583_;
goto v_reusejp_5585_;
}
else
{
lean_object* v_reuseFailAlloc_5587_; 
v_reuseFailAlloc_5587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5587_, 0, v_a_5581_);
v___x_5586_ = v_reuseFailAlloc_5587_;
goto v_reusejp_5585_;
}
v_reusejp_5585_:
{
return v___x_5586_;
}
}
}
}
else
{
lean_object* v___x_5589_; lean_object* v___x_5591_; 
lean_dec(v_a_5546_);
lean_del_object(v___x_5540_);
lean_dec(v_fst_5538_);
lean_del_object(v___x_5534_);
lean_dec(v_structId_5529_);
lean_dec(v_id_5528_);
lean_dec_ref(v_b_5511_);
lean_dec_ref(v_a_5510_);
v___x_5589_ = lean_box(0);
if (v_isShared_5549_ == 0)
{
lean_ctor_set(v___x_5548_, 0, v___x_5589_);
v___x_5591_ = v___x_5548_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v___x_5589_);
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
lean_del_object(v___x_5540_);
lean_dec(v_fst_5538_);
lean_del_object(v___x_5534_);
lean_dec(v_structId_5529_);
lean_dec(v_id_5528_);
lean_dec_ref(v_b_5511_);
lean_dec_ref(v_a_5510_);
v_a_5594_ = lean_ctor_get(v___x_5545_, 0);
v_isSharedCheck_5601_ = !lean_is_exclusive(v___x_5545_);
if (v_isSharedCheck_5601_ == 0)
{
v___x_5596_ = v___x_5545_;
v_isShared_5597_ = v_isSharedCheck_5601_;
goto v_resetjp_5595_;
}
else
{
lean_inc(v_a_5594_);
lean_dec(v___x_5545_);
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
lean_object* v_a_5602_; lean_object* v___x_5604_; uint8_t v_isShared_5605_; uint8_t v_isSharedCheck_5609_; 
lean_del_object(v___x_5540_);
lean_dec(v_fst_5538_);
lean_del_object(v___x_5534_);
lean_dec(v_fst_5532_);
lean_dec(v_structId_5529_);
lean_dec(v_id_5528_);
lean_dec_ref(v_b_5511_);
lean_dec_ref(v_a_5510_);
v_a_5602_ = lean_ctor_get(v___x_5542_, 0);
v_isSharedCheck_5609_ = !lean_is_exclusive(v___x_5542_);
if (v_isSharedCheck_5609_ == 0)
{
v___x_5604_ = v___x_5542_;
v_isShared_5605_ = v_isSharedCheck_5609_;
goto v_resetjp_5603_;
}
else
{
lean_inc(v_a_5602_);
lean_dec(v___x_5542_);
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
lean_del_object(v___x_5534_);
lean_dec(v_fst_5532_);
lean_dec(v_structId_5529_);
lean_dec(v_id_5528_);
lean_dec_ref(v_b_5511_);
lean_dec_ref(v_a_5510_);
v_a_5612_ = lean_ctor_get(v___x_5536_, 0);
v_isSharedCheck_5619_ = !lean_is_exclusive(v___x_5536_);
if (v_isSharedCheck_5619_ == 0)
{
v___x_5614_ = v___x_5536_;
v_isShared_5615_ = v_isSharedCheck_5619_;
goto v_resetjp_5613_;
}
else
{
lean_inc(v_a_5612_);
lean_dec(v___x_5536_);
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
lean_object* v_a_5622_; lean_object* v___x_5624_; uint8_t v_isShared_5625_; uint8_t v_isSharedCheck_5629_; 
lean_dec(v_structId_5529_);
lean_dec(v_id_5528_);
lean_dec_ref(v_b_5511_);
lean_dec_ref(v_a_5510_);
v_a_5622_ = lean_ctor_get(v___x_5530_, 0);
v_isSharedCheck_5629_ = !lean_is_exclusive(v___x_5530_);
if (v_isSharedCheck_5629_ == 0)
{
v___x_5624_ = v___x_5530_;
v_isShared_5625_ = v_isSharedCheck_5629_;
goto v_resetjp_5623_;
}
else
{
lean_inc(v_a_5622_);
lean_dec(v___x_5530_);
v___x_5624_ = lean_box(0);
v_isShared_5625_ = v_isSharedCheck_5629_;
goto v_resetjp_5623_;
}
v_resetjp_5623_:
{
lean_object* v___x_5627_; 
if (v_isShared_5625_ == 0)
{
v___x_5627_ = v___x_5624_;
goto v_reusejp_5626_;
}
else
{
lean_object* v_reuseFailAlloc_5628_; 
v_reuseFailAlloc_5628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5628_, 0, v_a_5622_);
v___x_5627_ = v_reuseFailAlloc_5628_;
goto v_reusejp_5626_;
}
v_reusejp_5626_:
{
return v___x_5627_;
}
}
}
}
}
else
{
lean_object* v_a_5630_; lean_object* v___x_5632_; uint8_t v_isShared_5633_; uint8_t v_isSharedCheck_5637_; 
lean_dec_ref(v_b_5511_);
lean_dec_ref(v_a_5510_);
v_a_5630_ = lean_ctor_get(v___x_5524_, 0);
v_isSharedCheck_5637_ = !lean_is_exclusive(v___x_5524_);
if (v_isSharedCheck_5637_ == 0)
{
v___x_5632_ = v___x_5524_;
v_isShared_5633_ = v_isSharedCheck_5637_;
goto v_resetjp_5631_;
}
else
{
lean_inc(v_a_5630_);
lean_dec(v___x_5524_);
v___x_5632_ = lean_box(0);
v_isShared_5633_ = v_isSharedCheck_5637_;
goto v_resetjp_5631_;
}
v_resetjp_5631_:
{
lean_object* v___x_5635_; 
if (v_isShared_5633_ == 0)
{
v___x_5635_ = v___x_5632_;
goto v_reusejp_5634_;
}
else
{
lean_object* v_reuseFailAlloc_5636_; 
v_reuseFailAlloc_5636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5636_, 0, v_a_5630_);
v___x_5635_ = v_reuseFailAlloc_5636_;
goto v_reusejp_5634_;
}
v_reusejp_5634_:
{
return v___x_5635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq___boxed(lean_object* v_a_5638_, lean_object* v_b_5639_, lean_object* v_a_5640_, lean_object* v_a_5641_, lean_object* v_a_5642_, lean_object* v_a_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_){
_start:
{
lean_object* v_res_5652_; 
v_res_5652_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5638_, v_b_5639_, v_a_5640_, v_a_5641_, v_a_5642_, v_a_5643_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_);
lean_dec(v_a_5650_);
lean_dec_ref(v_a_5649_);
lean_dec(v_a_5648_);
lean_dec_ref(v_a_5647_);
lean_dec(v_a_5646_);
lean_dec_ref(v_a_5645_);
lean_dec(v_a_5644_);
lean_dec_ref(v_a_5643_);
lean_dec(v_a_5642_);
lean_dec(v_a_5641_);
lean_dec(v_a_5640_);
return v_res_5652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(lean_object* v_a_5653_, lean_object* v_b_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_, lean_object* v_a_5659_, lean_object* v_a_5660_, lean_object* v_a_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_){
_start:
{
lean_object* v___x_5666_; 
v___x_5666_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_inSameStruct_x3f___redArg(v_a_5653_, v_b_5654_, v_a_5655_, v_a_5663_);
if (lean_obj_tag(v___x_5666_) == 0)
{
lean_object* v_a_5667_; 
v_a_5667_ = lean_ctor_get(v___x_5666_, 0);
lean_inc(v_a_5667_);
lean_dec_ref(v___x_5666_);
if (lean_obj_tag(v_a_5667_) == 1)
{
lean_object* v_val_5668_; lean_object* v___x_5669_; 
v_val_5668_ = lean_ctor_get(v_a_5667_, 0);
lean_inc(v_val_5668_);
lean_dec_ref(v_a_5667_);
v___x_5669_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_val_5668_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_, v_a_5659_, v_a_5660_, v_a_5661_, v_a_5662_, v_a_5663_, v_a_5664_);
if (lean_obj_tag(v___x_5669_) == 0)
{
lean_object* v_a_5670_; uint8_t v___x_5671_; 
v_a_5670_ = lean_ctor_get(v___x_5669_, 0);
lean_inc(v_a_5670_);
lean_dec_ref(v___x_5669_);
v___x_5671_ = lean_unbox(v_a_5670_);
lean_dec(v_a_5670_);
if (v___x_5671_ == 0)
{
lean_object* v___x_5672_; 
v___x_5672_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewIntModuleDiseq(v_a_5653_, v_b_5654_, v_val_5668_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_, v_a_5659_, v_a_5660_, v_a_5661_, v_a_5662_, v_a_5663_, v_a_5664_);
lean_dec(v_val_5668_);
return v___x_5672_;
}
else
{
lean_object* v___x_5673_; 
v___x_5673_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewCommRingDiseq(v_a_5653_, v_b_5654_, v_val_5668_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_, v_a_5659_, v_a_5660_, v_a_5661_, v_a_5662_, v_a_5663_, v_a_5664_);
lean_dec(v_val_5668_);
return v___x_5673_;
}
}
else
{
lean_object* v_a_5674_; lean_object* v___x_5676_; uint8_t v_isShared_5677_; uint8_t v_isSharedCheck_5681_; 
lean_dec(v_val_5668_);
lean_dec_ref(v_b_5654_);
lean_dec_ref(v_a_5653_);
v_a_5674_ = lean_ctor_get(v___x_5669_, 0);
v_isSharedCheck_5681_ = !lean_is_exclusive(v___x_5669_);
if (v_isSharedCheck_5681_ == 0)
{
v___x_5676_ = v___x_5669_;
v_isShared_5677_ = v_isSharedCheck_5681_;
goto v_resetjp_5675_;
}
else
{
lean_inc(v_a_5674_);
lean_dec(v___x_5669_);
v___x_5676_ = lean_box(0);
v_isShared_5677_ = v_isSharedCheck_5681_;
goto v_resetjp_5675_;
}
v_resetjp_5675_:
{
lean_object* v___x_5679_; 
if (v_isShared_5677_ == 0)
{
v___x_5679_ = v___x_5676_;
goto v_reusejp_5678_;
}
else
{
lean_object* v_reuseFailAlloc_5680_; 
v_reuseFailAlloc_5680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5680_, 0, v_a_5674_);
v___x_5679_ = v_reuseFailAlloc_5680_;
goto v_reusejp_5678_;
}
v_reusejp_5678_:
{
return v___x_5679_;
}
}
}
}
else
{
lean_object* v___x_5682_; 
lean_dec(v_a_5667_);
v___x_5682_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_5653_, v_b_5654_, v_a_5655_, v_a_5663_);
if (lean_obj_tag(v___x_5682_) == 0)
{
lean_object* v_a_5683_; lean_object* v___x_5685_; uint8_t v_isShared_5686_; uint8_t v_isSharedCheck_5693_; 
v_a_5683_ = lean_ctor_get(v___x_5682_, 0);
v_isSharedCheck_5693_ = !lean_is_exclusive(v___x_5682_);
if (v_isSharedCheck_5693_ == 0)
{
v___x_5685_ = v___x_5682_;
v_isShared_5686_ = v_isSharedCheck_5693_;
goto v_resetjp_5684_;
}
else
{
lean_inc(v_a_5683_);
lean_dec(v___x_5682_);
v___x_5685_ = lean_box(0);
v_isShared_5686_ = v_isSharedCheck_5693_;
goto v_resetjp_5684_;
}
v_resetjp_5684_:
{
if (lean_obj_tag(v_a_5683_) == 1)
{
lean_object* v_val_5687_; lean_object* v___x_5688_; 
lean_del_object(v___x_5685_);
v_val_5687_ = lean_ctor_get(v_a_5683_, 0);
lean_inc(v_val_5687_);
lean_dec_ref(v_a_5683_);
v___x_5688_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq_0__Lean_Meta_Grind_Arith_Linear_processNewNatModuleDiseq(v_a_5653_, v_b_5654_, v_val_5687_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_, v_a_5659_, v_a_5660_, v_a_5661_, v_a_5662_, v_a_5663_, v_a_5664_);
lean_dec(v_val_5687_);
return v___x_5688_;
}
else
{
lean_object* v___x_5689_; lean_object* v___x_5691_; 
lean_dec(v_a_5683_);
lean_dec_ref(v_b_5654_);
lean_dec_ref(v_a_5653_);
v___x_5689_ = lean_box(0);
if (v_isShared_5686_ == 0)
{
lean_ctor_set(v___x_5685_, 0, v___x_5689_);
v___x_5691_ = v___x_5685_;
goto v_reusejp_5690_;
}
else
{
lean_object* v_reuseFailAlloc_5692_; 
v_reuseFailAlloc_5692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5692_, 0, v___x_5689_);
v___x_5691_ = v_reuseFailAlloc_5692_;
goto v_reusejp_5690_;
}
v_reusejp_5690_:
{
return v___x_5691_;
}
}
}
}
else
{
lean_object* v_a_5694_; lean_object* v___x_5696_; uint8_t v_isShared_5697_; uint8_t v_isSharedCheck_5701_; 
lean_dec_ref(v_b_5654_);
lean_dec_ref(v_a_5653_);
v_a_5694_ = lean_ctor_get(v___x_5682_, 0);
v_isSharedCheck_5701_ = !lean_is_exclusive(v___x_5682_);
if (v_isSharedCheck_5701_ == 0)
{
v___x_5696_ = v___x_5682_;
v_isShared_5697_ = v_isSharedCheck_5701_;
goto v_resetjp_5695_;
}
else
{
lean_inc(v_a_5694_);
lean_dec(v___x_5682_);
v___x_5696_ = lean_box(0);
v_isShared_5697_ = v_isSharedCheck_5701_;
goto v_resetjp_5695_;
}
v_resetjp_5695_:
{
lean_object* v___x_5699_; 
if (v_isShared_5697_ == 0)
{
v___x_5699_ = v___x_5696_;
goto v_reusejp_5698_;
}
else
{
lean_object* v_reuseFailAlloc_5700_; 
v_reuseFailAlloc_5700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5700_, 0, v_a_5694_);
v___x_5699_ = v_reuseFailAlloc_5700_;
goto v_reusejp_5698_;
}
v_reusejp_5698_:
{
return v___x_5699_;
}
}
}
}
}
else
{
lean_object* v_a_5702_; lean_object* v___x_5704_; uint8_t v_isShared_5705_; uint8_t v_isSharedCheck_5709_; 
lean_dec_ref(v_b_5654_);
lean_dec_ref(v_a_5653_);
v_a_5702_ = lean_ctor_get(v___x_5666_, 0);
v_isSharedCheck_5709_ = !lean_is_exclusive(v___x_5666_);
if (v_isSharedCheck_5709_ == 0)
{
v___x_5704_ = v___x_5666_;
v_isShared_5705_ = v_isSharedCheck_5709_;
goto v_resetjp_5703_;
}
else
{
lean_inc(v_a_5702_);
lean_dec(v___x_5666_);
v___x_5704_ = lean_box(0);
v_isShared_5705_ = v_isSharedCheck_5709_;
goto v_resetjp_5703_;
}
v_resetjp_5703_:
{
lean_object* v___x_5707_; 
if (v_isShared_5705_ == 0)
{
v___x_5707_ = v___x_5704_;
goto v_reusejp_5706_;
}
else
{
lean_object* v_reuseFailAlloc_5708_; 
v_reuseFailAlloc_5708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5708_, 0, v_a_5702_);
v___x_5707_ = v_reuseFailAlloc_5708_;
goto v_reusejp_5706_;
}
v_reusejp_5706_:
{
return v___x_5707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed(lean_object* v_a_5710_, lean_object* v_b_5711_, lean_object* v_a_5712_, lean_object* v_a_5713_, lean_object* v_a_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_, lean_object* v_a_5717_, lean_object* v_a_5718_, lean_object* v_a_5719_, lean_object* v_a_5720_, lean_object* v_a_5721_, lean_object* v_a_5722_){
_start:
{
lean_object* v_res_5723_; 
v_res_5723_ = l_Lean_Meta_Grind_Arith_Linear_processNewDiseq(v_a_5710_, v_b_5711_, v_a_5712_, v_a_5713_, v_a_5714_, v_a_5715_, v_a_5716_, v_a_5717_, v_a_5718_, v_a_5719_, v_a_5720_, v_a_5721_);
lean_dec(v_a_5721_);
lean_dec_ref(v_a_5720_);
lean_dec(v_a_5719_);
lean_dec_ref(v_a_5718_);
lean_dec(v_a_5717_);
lean_dec_ref(v_a_5716_);
lean_dec(v_a_5715_);
lean_dec_ref(v_a_5714_);
lean_dec(v_a_5713_);
lean_dec(v_a_5712_);
return v_res_5723_;
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
